(* ML audits of inherent impl blocks: grammar, AST, source slices, printing and markup of the
   syntax; declarations, registrations, ownership, options, atomicity and output of the members;
   and resolution of Self and type heads, path selection, direct calls and imports. The readable
   examples are in Parser_Impl_Examples. *)

theory Parser_Impl_ML_Tests
  imports
    Parser_Impl_Examples
    Parser_Chunk_Use_ML_Tests
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

chapter\<open> Impl block parsing \<close>

section\<open> Test support \<close>

text\<open>
The audits parse synthetic sources positioned at offset 1, so expected ranges are symbol offsets
into the audited text. Report captures cover the lexer and grammar reports of one parse.
\<close>

ML\<open>
structure Impl_Syntax_Test =
struct
  open Chunk_Test

  fun impl_of _ (URust_AST.Impl_Item_Node impl) = impl
    | impl_of label _ = error ("impl audit: " ^ label ^ " is not an impl item")

  fun envelopes ctxt label text = URust_AST.chunk_items (the_chunk ctxt label text)

  fun only_impl ctxt label text =
    (case envelopes ctxt label text of
       [envelope] => (envelope, impl_of label (URust_AST.annotated_item_item envelope))
     | _ => error ("impl audit: " ^ label ^ " is not one chunk member"))

  fun function_source ctxt label text =
    URust_Parser.parse_function_source ctxt (source label text)

  fun the_function ctxt label text =
    (case function_source ctxt label text of
       SOME function => function
     | NONE => error ("impl audit: " ^ label ^ " parsed as empty"))

  (* A rejection with every expected fragment, positioned at exactly the expected range. *)
  fun rejects_at label expected range action =
    let val message = expect_failure label expected action in
      require (label ^ ": diagnostic range " ^ @{make_string} (message_range message))
        (message_range message = range)
    end

  fun parse_rejects ctxt label expected text needle occurrence =
    rejects_at label expected (range_of text needle occurrence)
      (fn () => parse ctxt label text)

  fun command_rejects thy label expected text needle occurrence =
    rejects_at label expected (range_of text needle occurrence)
      (fn () => run_commands false label thy text)

  (* Every report of one parse as (markup name, symbol range, report body text). *)
  fun parse_reports ctxt label text =
    let
      val captured = Synchronized.var ("impl reports " ^ label) ([]: string list)
      fun collect chunks = Synchronized.change captured (fn messages => messages @ [implode chunks])
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
            Unsynchronized.setmp Private_Output.report_fn collect
              (fn () => Exn.result (parse ctxt label) text) ()) ())
      fun events (XML.Elem ((name, properties), body)) =
            (name, position_range (Position.of_properties properties), XML.content_of body) ::
              maps events body
        | events (XML.Text _) = []
    in (result, maps events (maps YXML.parse_body (Synchronized.value captured))) end

  fun roles_at reports range =
    reports
    |> map_filter (fn (name, report_range, body) =>
        if report_range = range then SOME (name, body) else NONE)
    |> sort_distinct (prod_ord string_ord string_ord)

  fun token_ranges layout token =
    map position_range (URust_AST.source_token_positions layout token)

  fun source_text source = Input.string_of source
  fun source_range source = position_range (#1 (Input.range_of source))
end
\<close>

section\<open> Impl headers \<close>

text\<open>
The header lexes like a signature: primitive names in generic arguments are Rust type tokens,
nested generic closers split, and \<open>\<tau>\<open>\<dots>\<close>\<close> arguments stay positioned HOL sources. The
target, the \<open>impl\<close> keyword and both braces keep their exact ranges, and the chunk envelope
of the impl is its complete source.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>

  val text = "impl Counter {}"
  val (envelope, impl) = only_impl ctxt "header-plain" text
  val layout = URust_AST.impl_source_layout impl
  val _ = require "plain header target"
    (case URust_AST.impl_target impl of
       URust_AST.Path_Type ([URust_AST.Rust_Type_Path_Segment ("Counter", pos, NONE, _)], _) =>
         position_range pos = range_of text "Counter" 0
     | _ => false)
  val _ = require "plain header keyword range"
    (position_range (URust_AST.impl_position impl) = range_of text "impl" 0)
  val _ = require "plain header span"
    (position_range (URust_AST.impl_item_position impl) = (1, 1 + size text))
  val _ = require "plain header item position"
    (URust_AST.item_position (URust_AST.Impl_Item_Node impl) = URust_AST.impl_item_position impl)
  val _ = require "plain header braces"
    (token_ranges layout (URust_AST.Delimiter_Token "{") = [range_of text "{" 0] andalso
      token_ranges layout (URust_AST.Delimiter_Token "}") = [range_of text "}" 0])
  val _ = require "plain header has no members" (null (URust_AST.impl_members impl))
  val _ = require "plain header envelope source"
    (source_text (URust_AST.annotated_item_source envelope) = text andalso
      source_range (URust_AST.annotated_item_source envelope) = (1, 1 + size text) andalso
      is_none (URust_AST.annotated_item_annotation envelope))

  fun target_of label text = URust_AST.impl_target (#2 (only_impl ctxt label text))

  val qualified = "impl outer::inner::Counter {}"
  val _ = require "qualified header segments"
    (case target_of "header-qualified" qualified of
       URust_AST.Path_Type (segments, _) =>
         map (fn URust_AST.Rust_Type_Path_Segment (name, pos, NONE, _) =>
                (name, position_range pos)
               | _ => ("", (~1, ~1))) segments =
           [("outer", range_of qualified "outer" 0), ("inner", range_of qualified "inner" 0),
            ("Counter", range_of qualified "Counter" 0)]
     | _ => false)

  val concrete = "impl Pair<u8, bool, usize> {}"
  val _ = require "concrete generic arguments lex as Rust primitive types"
    (case target_of "header-concrete" concrete of
       URust_AST.Path_Type ([URust_AST.Rust_Type_Path_Segment ("Pair", _, SOME arguments, _)], _) =>
         map (fn URust_AST.Rust_Type_Argument (URust_AST.Primitive_Type (primitive, pos)) =>
                (primitive, position_range pos)
               | _ => (URust_AST.DPT_Unit, (~1, ~1))) arguments =
           [(URust_AST.DPT_U8, range_of concrete "u8" 0),
            (URust_AST.DPT_Bool, range_of concrete "bool" 0),
            (URust_AST.DPT_Usize, range_of concrete "usize" 0)]
     | _ => false)

  val nested = "impl Pair<Pair<u8>> {}"
  val (nested_result, nested_reports) = parse_reports ctxt "header-nested" nested
  val _ = require "nested generic header parsed"
    (case nested_result of
       Exn.Res (SOME chunk) =>
         (case map URust_AST.annotated_item_item (URust_AST.chunk_items chunk) of
            [URust_AST.Impl_Item_Node impl] =>
              (case URust_AST.impl_target impl of
                 URust_AST.Path_Type
                   ([URust_AST.Rust_Type_Path_Segment
                     ("Pair", _,
                      SOME [URust_AST.Rust_Type_Argument
                        (URust_AST.Path_Type
                          ([URust_AST.Rust_Type_Path_Segment
                            ("Pair", _,
                             SOME [URust_AST.Rust_Type_Argument
                               (URust_AST.Primitive_Type (URust_AST.DPT_U8, _))], _)], _))],
                      _)], _) => true
               | _ => false)
          | _ => false)
     | _ => false)
  val first_closer = range_within nested ">>" ">"
  val second_closer = (#1 first_closer + 1, #2 first_closer + 1)
  val _ = require "nested generic closers split into two delimiters"
    (roles_at nested_reports first_closer = [("delimiter", ""), ("typing", "TGT")] andalso
      roles_at nested_reports second_closer = [("delimiter", ""), ("typing", "TGT")])

  (* Adjacent closers leave the enclosing argument list open for its const sibling; its
     balanced braces belong to the target, and the following body still owns the member. *)
  fun const_sibling (label, text, constant) =
    let
      val (_, impl) = only_impl ctxt label text
      val _ = require (label ^ ": positioned const sibling")
        (case URust_AST.impl_target impl of
           URust_AST.Path_Type
             ([URust_AST.Rust_Type_Path_Segment
               ("Outer", _, SOME [URust_AST.Rust_Type_Argument _,
                 URust_AST.Rust_Const_Expression_Argument source], _)], _) =>
               source_text source = constant andalso source_range source = range_of text constant 0
         | _ => false)
      val _ = require (label ^ ": the body retains its member")
        (map (#1 o URust_AST.function_name o URust_AST.impl_member_function)
          (URust_AST.impl_members impl) = ["read"])
    in () end
  val _ = List.app const_sibling
    [("header-const-after-adjacent-closers",
      "impl Outer<Middle<Inner<u32>>, {1}> { fn read() {} }", "{1}"),
     ("header-const-after-spaced-closers",
      "impl Outer<Middle<Inner<u32> >, {1}> { fn read() {} }", "{1}"),
     ("header-const-two-adjacent-closer-groups",
      "impl Outer<Next<Middle<Inner<u32>>, {1}>, {2}> { fn read() {} }", "{2}")]

  val escaped = "impl Pair<\<tau>\<open>'a list\<close>> {}"
  val _ = require "HOL type generic argument keeps its positioned source"
    (case target_of "header-escaped" escaped of
       URust_AST.Path_Type
         ([URust_AST.Rust_Type_Path_Segment
           ("Pair", _, SOME [URust_AST.Rust_Type_Argument (URust_AST.HOL_Type_Source source)],
            _)], _) =>
         source_text source = "'a list" andalso
           source_range source = range_of escaped "'a list" 0
     | _ => false)

  val whole_hol = "impl \<tau>\<open>nat\<close> {}"
  val _ = require "a whole HOL type target parses for elaboration to reject"
    (case target_of "header-whole-hol" whole_hol of
       URust_AST.HOL_Type_Source source => source_text source = "nat"
     | _ => false)
  val primitive = "impl u32 {}"
  val _ = require "a primitive target parses for elaboration to reject"
    (case target_of "header-primitive" primitive of
       URust_AST.Primitive_Type (URust_AST.DPT_U32, pos) =>
         position_range pos = range_of primitive "u32" 0
     | _ => false)
in end
\<close>

subsection\<open> Header rejections \<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  fun header label text needle construct =
    parse_rejects ctxt label ["urust: " ^ construct ^ " is not supported in impl headers"]
      text needle 0
  val _ = List.app (fn (label, text, expected) =>
    let val (_, impl) = only_impl ctxt label text
    in require (label ^ ": generic header is preserved")
      (length (#parameters (URust_AST.impl_generics impl)) = expected) end)
    [("header-generic-parameters", "impl<T> Pair<T> {}", 1),
     ("header-lifetime-parameters", "impl<'a> Counter {}", 1),
     ("header-mixed-parameters", "impl<'a, T, const N: usize> Grid<T, N> {}", 3)]
  val _ = header "header-trait" "impl Display for Counter {}" "for"
    "a trait impl (`impl Trait for T`)"
  val _ = header "header-generic-trait" "impl From<u8> for Counter {}" "for"
    "a trait impl (`impl Trait for T`)"
  val (_, where_impl) = only_impl ctxt "header-where"
    "impl Counter where Counter: Copy {}"
  val _ = require "impl where predicate is retained before denotation"
    (length (#where_clause (URust_AST.impl_generics where_impl)) = 1)
  val _ = header "header-unsafe" "unsafe impl Counter {}" "unsafe" "`unsafe impl`"
  val _ = header "header-negative" "impl !Send for Counter {}" "!"
    "a negative impl (`impl !T`)"
  val _ = header "header-negative-inherent" "impl !Counter {}" "!"
    "a negative impl (`impl !T`)"
  (* Supported generic headers reach ordinary syntax errors in malformed members. *)
  val _ = expect_failure "header-generic-before-syntax-error" ["syntax error"]
    (fn () => parse ctxt "header-generic-before-syntax-error" "impl<T: Copy> Pair<T> { fn ( }")
  val _ = expect_failure "header-where-before-syntax-error" ["syntax error"]
    (fn () => parse ctxt "header-where-before-syntax-error" "impl Counter where Self: { fn")
  val _ = header "header-annotated-unsafe"
    (annotation "register_notation" ^ "\nunsafe impl Counter {}") "unsafe" "`unsafe impl`"
  (* Outside impl headers, for and where keep their identifier spelling in signatures. *)
  val _ = require "for and where remain signature identifiers"
    (case URust_AST.function_parameters
        (the_function ctxt "signature-for-where" "fn Names(for: u8, where: u8) {}") of
       [URust_AST.Function_Parameter (_, URust_AST.P_Ident ("for", _), _, _),
        URust_AST.Function_Parameter (_, URust_AST.P_Ident ("where", _), _, _)] => true
     | _ => false)
  (* A malformed header remains an ordinary positioned syntax error. *)
  val _ = parse_rejects ctxt "header-missing-target" ["syntax error"] "impl {}" "{" 0
  val _ = expect_failure "header-missing-brace" ["syntax error"]
    (fn () => parse ctxt "header-missing-brace" "impl Counter")
in end
\<close>

subsection\<open> Header levels \<close>

text\<open>
Header rejections apply at the header's own level only. Inside the target's generic-argument,
parenthesis and bracket groups, \<open>for\<close>, \<open>where\<close>, \<open><\<close> and \<open>!\<close> lex as in any
signature, so a nested higher-ranked type gets the diagnostic it gets in a function parameter,
at the same token. After a group closes, including a split \<open>>>\<close>, the header level resumes.
No Rust type contains a brace, so the header ends at its first opening brace at any depth: a
target with an unclosed group is a syntax error in the header, and the impl body lexes as a body.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  fun header label text needle construct =
    parse_rejects ctxt label ["urust: " ^ construct ^ " is not supported in impl headers"]
      text needle 0
  val trait = "a trait impl (`impl Trait for T`)"
  val _ = header "level-trait-after-tuple" "impl Pair<(u8, u16)> for Counter {}" "for" trait
  val _ = header "level-trait-after-array" "impl Pair<[u8; 4]> for Counter {}" "for" trait
  val _ = header "level-trait-after-split-closer" "impl Pair<Pair<u8>> for Counter {}" "for" trait
  val (_, after_arguments) = only_impl ctxt "level-where-after-arguments"
    "impl Pair<Pair<u8>> where Self: Copy {}"
  val _ = require "structured where predicate resumes after split generic closers"
    (length (#where_clause (URust_AST.impl_generics after_arguments)) = 1)

  (* The reason of a diagnostic, without the line and column prefix of a syntax error. *)
  fun reason message =
    let
      val text = plain message
      val (_, rest) = Substring.position ": " (Substring.full text)
    in
      if String.isPrefix "Parse Error at" text andalso not (Substring.isEmpty rest)
      then Substring.string (Substring.triml 2 rest) else text
    end
  fun failure label action =
    (case Exn.result action () of
       Exn.Res _ => error ("impl audit: " ^ label ^ " was accepted")
     | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
  fun relative (start, stop) origin = (start - origin, stop - origin)

  (* A nested type is rejected in an impl header exactly as in a function parameter. *)
  fun nested label typ =
    let
      val impl_text = "impl Pair<" ^ typ ^ "> {}"
      val fn_text = "fn F(value: Pair<" ^ typ ^ ">) {}"
      val impl_message = failure label (fn () => parse ctxt label impl_text)
      val fn_message = failure label (fn () => function_source ctxt label fn_text)
      val _ = require (label ^ ": impl header rejection misfired: " ^ plain impl_message)
        (not (String.isSubstring "impl headers" impl_message))
      val _ = require (label ^ ": reason differs: " ^ reason impl_message ^ " / " ^
          reason fn_message)
        (reason impl_message = reason fn_message)
      val _ = require (label ^ ": range differs")
        (relative (message_range impl_message) (#1 (range_of impl_text typ 0)) =
          relative (message_range fn_message) (#1 (range_of fn_text typ 0)))
    in () end
  val hrtb = "for<'a> fn(&'a u8)"
  val _ = nested "nested-hrtb" hrtb
  val _ = nested "nested-hrtb-deep" ("Pair<Pair<" ^ hrtb ^ ">>")
  val _ = nested "nested-hrtb-tuple" ("(u8, " ^ hrtb ^ ")")
  val _ = nested "nested-hrtb-array" ("[" ^ hrtb ^ "; 4]")
  val _ = nested "nested-hrtb-fn-argument" ("fn(" ^ hrtb ^ ") -> u8")

  fun argument_names label text =
    (case URust_AST.impl_target (#2 (only_impl ctxt label text)) of
       URust_AST.Path_Type ([URust_AST.Rust_Type_Path_Segment (_, _, SOME arguments, _)], _) =>
         map (fn URust_AST.Rust_Type_Argument
                  (URust_AST.Path_Type ([URust_AST.Rust_Type_Path_Segment (name, _, _, _)], _)) =>
                  name
               | URust_AST.Rust_Type_Argument (URust_AST.Primitive_Type (URust_AST.DPT_Never, _)) =>
                  "!"
               | _ => "?") arguments
     | _ => [])
  val _ = require "nested for and where are identifiers"
    (argument_names "nested-identifiers" "impl Pair<for, where> {}" = ["for", "where"])
  val _ = require "a nested never type is not a negative impl"
    (argument_names "nested-never" "impl Pair<!> {}" = ["!"])

  (* Groups in the target do not end the header early, and its first brace does. *)
  fun member_names label text =
    map (#1 o URust_AST.function_name o URust_AST.impl_member_function)
      (URust_AST.impl_members (#2 (only_impl ctxt label text)))
  val _ = require "header with array and tuple arguments"
    (member_names "level-groups"
      "impl Pair<[u8; 4], (u8, Pair<u16>)> {\n  fn get(self) -> u32 { 0 }\n}" = ["get"])
  val _ = require "header with a split closer"
    (member_names "level-split" "impl Pair<Pair<u8>> { fn get(self) {} }" = ["get"])

  (* An unclosed group in the target is a syntax error in the header: at a token of the target
     up to the brace that ends the header (where ML-Yacc's correction places it), never a lexer
     error in a body that the header would otherwise swallow. *)
  fun unclosed_at label text needle =
    let
      val message = expect_failure label ["syntax error"] (fn () => parse ctxt label text)
      val (start, stop) = message_range message
    in
      require (label ^ ": body lexed as a signature: " ^ plain message)
        (not (String.isSubstring "unexpected input" message));
      require (label ^ ": diagnostic range " ^ @{make_string} (start, stop))
        (#2 (range_of text "impl" 0) < start andalso stop <= #2 (range_of text needle 0))
    end
  fun unclosed label text = unclosed_at label text "{"
  val _ = unclosed "unclosed-angle-operator" "impl Pair<u8 { 1 + 2 }"
  val _ = unclosed "unclosed-angle-fuel" "impl Pair<u8 { #[fuel(3)] loop {} }"
  (* A body token that no body lexes is rejected by the body lexer whatever the header: the
     header's syntax error is detected one token later. A signature lexer would instead read 'a
     as a lifetime and reject the closing apostrophe. *)
  val character_body = "impl Pair<u8 { 'a' }"
  val character_message =
    expect_failure "unclosed-angle-character" ["unexpected input"]
      (fn () => parse ctxt "unclosed-angle-character" character_body)
  val _ = require "unclosed header: the body lexes as a body"
    (#1 (message_range character_message) = #1 (range_of character_body "'" 0))
  val _ = unclosed "unclosed-nested-angle" "impl Pair<Pair<u8> {\n  fn get(self) -> u8 { 1 + 2 }\n}"
  val _ = unclosed "unclosed-angle-annotated-member"
    ("impl Pair<u8 {\n  " ^ annotation "pretty" ^ "\n  fn get(self) -> u8 { 1 + 2 }\n}")
  val _ = unclosed_at "unclosed-paren" "impl Pair<(u8, u16> {\n  fn get(self) -> u8 { 1 + 2 }\n}" ">"
  val _ = unclosed_at "unclosed-bracket" "impl Pair<[u8; 4> {\n  fn get(self) -> u8 { 1 + 2 }\n}" ">"
  val _ = unclosed "unclosed-paren-at-brace" "impl Pair<(u8 {\n  fn get(self) -> u8 { 1 + 2 }\n}"
in end
\<close>

section\<open> Members and annotations \<close>

text\<open>
Members keep their source order, their optional annotation and the positioned source slice of
their function item without the annotation. An annotation before \<open>impl\<close> belongs to the
chunk envelope.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>

  val first = "fn new() -> u32 { 0 }"
  val second = "fn get(self) -> u32 { \<llangle>value\<rrangle> }"
  val third = "fn bump(&mut self, step: u32) { \<epsilon>\<open>skip\<close> }"
  val text =
    annotation "register_notation" ^ "\n" ^
    "impl Counter {\n" ^
    "  " ^ first ^ "\n\n" ^
    "  " ^ annotation "name = \"counter_get_value\"" ^ "\n" ^
    "  " ^ second ^ "\n" ^
    "  " ^ third ^ "\n" ^
    "}"
  val (envelope, impl) = only_impl ctxt "members" text
  val members = URust_AST.impl_members impl
  val _ = require "impl annotation belongs to the envelope"
    (case URust_AST.annotated_item_annotation envelope of
       SOME annotation =>
         source_text (URust_AST.annotation_payload annotation) = "register_notation"
     | NONE => false)
  val _ = require "envelope starts at impl"
    (#1 (source_range (URust_AST.annotated_item_source envelope)) = #1 (range_of text "impl" 0))
  val _ = require "member names in source order"
    (map (#1 o URust_AST.function_name o URust_AST.impl_member_function) members =
      ["new", "get", "bump"])
  val _ = require "member annotations"
    (map (Option.map (source_text o URust_AST.annotation_payload) o
        URust_AST.impl_member_annotation) members =
      [NONE, SOME "name = \"counter_get_value\"", NONE])
  (* Escaped symbols before and inside a member do not shift its slice. *)
  val _ = require "member source slices"
    (map (fn member =>
        let val source = URust_AST.impl_member_source member
        in (source_text source, source_range source) end) members =
      [(first, range_of text first 0), (second, range_of text second 0),
       (third, range_of text third 0)])
  val _ = require "member source slices span their function items"
    (map (position_range o URust_AST.function_item_position o URust_AST.impl_member_function)
        members =
      map (source_range o URust_AST.impl_member_source) members)

  val single = "impl Counter { fn only() {} }"
  val _ = require "one member"
    (map (#1 o URust_AST.function_name o URust_AST.impl_member_function)
      (URust_AST.impl_members (#2 (only_impl ctxt "one-member" single))) = ["only"])

  (* One envelope per impl, between other members, each with its exact source. *)
  val impl_left = "impl Counter {\n  fn left() {}\n}"
  val function = "fn between() {}"
  val impl_right = "impl Gauge {}"
  val structure_item = "struct Gauge { level: u32 }"
  val mixed = structure_item ^ "\n" ^ impl_left ^ "\n" ^ function ^ "\n" ^ impl_right
  val mixed_envelopes = envelopes ctxt "one-envelope-per-impl" mixed
  val _ = require "one envelope per impl"
    (map (fn envelope =>
        (source_text (URust_AST.annotated_item_source envelope),
         source_range (URust_AST.annotated_item_source envelope)))
      mixed_envelopes =
      map (fn item => (item, range_of mixed item 0))
        [structure_item, impl_left, function, impl_right])
  val _ = require "impl kinds in a mixed chunk"
    (map (fn envelope =>
        (case URust_AST.annotated_item_item envelope of
           URust_AST.Impl_Item_Node _ => "impl"
         | URust_AST.Function_Item_Node _ => "fn"
         | URust_AST.Datatype_Item _ => "datatype"
         | _ => "other")) mixed_envelopes = ["datatype", "impl", "fn", "impl"])
in end
\<close>

subsection\<open> Annotation placement \<close>

text\<open>
Member annotations follow the chunk placement rules, and an annotation directly before the
closing brace has no declaration. \<open>impl\<close> starts a declaration for the same-line check.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  val pretty = annotation "pretty"

  val same_line = "impl Counter {\n  " ^ pretty ^ " fn f() {}\n}"
  val _ = parse_rejects ctxt "member-annotation-same-line"
    ["not on the same line"] same_line "fn f() {}" 0

  val impl_same_line = pretty ^ " impl Counter {}"
  val _ = parse_rejects ctxt "impl-annotation-same-line"
    ["not on the same line"] impl_same_line "impl Counter {}" 0

  val blank_line = "impl Counter {\n  " ^ pretty ^ "\n\n  fn f() {}\n}"
  val blank_start = symbol_offset blank_line (raw_index blank_line (Symbol.close ^ "\n\n") 0) + 2
  val _ =
    rejects_at "member-annotation-blank-line" ["remove the blank line"]
      (blank_start, blank_start + 1) (fn () => parse ctxt "member-annotation-blank-line" blank_line)

  val consecutive = "impl Counter {\n  " ^ pretty ^ "\n  " ^ annotation "verbosity = 0" ^
    "\n  fn f() {}\n}"
  val second_opener = range_of consecutive (omega ^ Symbol.open_) 1
  val _ =
    rejects_at "member-annotation-consecutive" ["must be the only annotation of its declaration"]
      second_opener (fn () => parse ctxt "member-annotation-consecutive" consecutive)

  val dangling = "impl Counter {\n  fn f() {}\n  " ^ pretty ^ "\n}"
  val _ = parse_rejects ctxt "member-annotation-dangling"
    ["must be followed by its declaration, not the end of its impl block"] dangling pretty 0
  val dangling_empty = "impl Counter {\n  " ^ pretty ^ "\n}"
  val _ = parse_rejects ctxt "member-annotation-dangling-empty"
    ["must be followed by its declaration, not the end of its impl block"] dangling_empty pretty 0

  val before_const = "impl Counter {\n  " ^ pretty ^ "\n  const LIMIT: u32 = 1;\n}"
  val _ = parse_rejects ctxt "member-annotation-before-const"
    ["urust: only fn items are supported in impl blocks"] before_const "const" 0

  val opening_line = "impl Counter { " ^ pretty ^ "\n  fn f() {}\n}"
  val _ = parse_rejects ctxt "member-annotation-opening-line"
    ["must start its own line"] opening_line pretty 0
in end
\<close>

subsection\<open> Non-fn members \<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  fun member_occurrence label body needle occurrence =
    parse_rejects ctxt label ["urust: only fn items are supported in impl blocks"]
      ("impl Counter {\n  " ^ body ^ "\n}") needle occurrence
  fun member label body needle = member_occurrence label body needle 0
  val _ = member "member-const" "const LIMIT: u32 = 1;" "const"
  val _ = member "member-const-fn" "const fn limit() -> u32 { 1 }" "const"
  val _ = member "member-type" "type Value = u32;" "type"
  val _ = member "member-pub" "pub fn get(self) -> u32 { 0 }" "pub"
  val _ = member "member-pub-crate" "pub(crate) fn get(self) -> u32 { 0 }" "pub"
  val _ = member "member-struct" "struct Inner { value: u32 }" "struct"
  val _ = member "member-enum" "enum Inner { First }" "enum"
  val _ = member "member-use" "use demo::value;" "use"
  val _ = member_occurrence "member-impl" "impl Gauge {}" "impl" 1
  val _ = member "member-unsafe" "unsafe fn get(self) -> u32 { 0 }" "unsafe"
  val _ =
    parse_rejects ctxt "member-after-function" ["urust: only fn items are supported in impl blocks"]
      "impl Counter {\n  fn get(self) -> u32 { 0 }\n  type Value = u32;\n}" "type" 0
in end
\<close>

section\<open> Receivers \<close>

text\<open>
Every receiver shorthand parses as the first parameter of any function, keeps its source
spelling, the exact range of its \<open>self\<close> token and a layout with its \<open>&\<close> operator and
\<open>mut\<close> keyword, and prints as written. Typed receivers and borrowed patterns are unchanged.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  val lifetime = URust_AST.Rust_Lifetime ("'a", Position.none)
  val forms =
    [("self", URust_AST.Receiver_Value),
     ("mut self", URust_AST.Receiver_Mut_Value),
     ("&self", URust_AST.Receiver_Ref {mutable = false, lifetime = NONE}),
     ("&mut self", URust_AST.Receiver_Ref {mutable = true, lifetime = NONE}),
     ("&'a self", URust_AST.Receiver_Ref {mutable = false, lifetime = SOME lifetime}),
     ("&'a mut self", URust_AST.Receiver_Ref {mutable = true, lifetime = SOME lifetime})]

  (* Lifetime positions are compared separately. *)
  fun erase (URust_AST.Receiver_Ref {mutable, lifetime = SOME _}) =
        URust_AST.Receiver_Ref {mutable = mutable, lifetime = SOME lifetime}
    | erase form = form

  fun check_receiver label text receiver expected parameter =
    (case parameter of
       URust_AST.Receiver_Parameter (form, self_pos, layout) =>
         let
           val receiver_start = #1 (range_of text receiver 0)
           val receiver_range = (receiver_start, receiver_start + size receiver)
           val self_start = receiver_start + size receiver - size "self"
           val amp = String.isPrefix "&" receiver
           val has_mut = String.isSubstring "mut" receiver
           val mut_start =
             receiver_start + the_default 0 (try (raw_index receiver "mut") 0)
           val _ = require (label ^ ": form") (erase form = expected)
           val _ = require (label ^ ": self token range")
             (position_range self_pos = (self_start, self_start + 4))
           val _ = require (label ^ ": receiver span")
             (position_range (URust_AST.source_span layout) = receiver_range andalso
               position_range (URust_AST.function_parameter_position parameter) = receiver_range)
           val _ = require (label ^ ": ampersand token")
             (token_ranges layout URust_AST.Operator_Token =
               (if amp then [(receiver_start, receiver_start + 1)] else []))
           val _ = require (label ^ ": mut token")
             (token_ranges layout (URust_AST.Keyword_Token "mut") =
               (if has_mut then [(mut_start, mut_start + 3)] else []))
           val _ = require (label ^ ": lifetime")
             (case form of
                URust_AST.Receiver_Ref {lifetime = SOME (URust_AST.Rust_Lifetime ("'a", pos)), ...} =>
                  position_range pos = (receiver_start + 1, receiver_start + 3)
              | URust_AST.Receiver_Ref {lifetime = SOME _, ...} => false
              | _ => true)
           val _ = require (label ^ ": receiver accessor")
             (Option.map (position_range o #2) (URust_AST.receiver_parameter parameter) =
               SOME (self_start, self_start + 4))
         in () end
     | _ => error ("impl audit: " ^ label ^ " is not a receiver"))

  fun free_function (receiver, expected) =
    let
      val label = "receiver-free " ^ receiver
      val text = "fn Receiver<'a>(" ^ receiver ^ ", value: u32) -> u32 { value }"
      val function = the_function ctxt label text
      val parameters = URust_AST.function_parameters function
      val _ = check_receiver label text receiver expected (hd parameters)
      val _ = require (label ^ ": later parameter is ordinary")
        (case nth parameters 1 of
           URust_AST.Function_Parameter (NONE, URust_AST.P_Ident ("value", _), _, _) => true
         | _ => false)
      val printed = URust_Printer.string_of_function URust_Printer.serialized_options function
      val _ = require (label ^ ": source spelling printed: " ^ printed)
        (String.isSubstring ("(" ^ receiver ^ ", value: u32)") printed)
      val reparsed = the_function ctxt (label ^ " reparsed") printed
      val _ = require (label ^ ": printer roundtrip")
        (URust_Printer.tokens_of_function URust_Printer.serialized_options reparsed =
          URust_Printer.tokens_of_function URust_Printer.serialized_options function)
    in () end
  val _ = List.app free_function forms

  fun member_receiver (receiver, expected) =
    let
      val label = "receiver-member " ^ receiver
      val text = "impl Counter {\n  fn get<'a>(" ^ receiver ^ ") -> u32 { 0 }\n}"
      val (_, impl) = only_impl ctxt label text
    in
      (case URust_AST.impl_members impl of
         [member] =>
           check_receiver label text receiver expected
             (hd (URust_AST.function_parameters (URust_AST.impl_member_function member)))
       | _ => error ("impl audit: " ^ label ^ " member count"))
    end
  val _ = List.app member_receiver forms

  (* A receiver alone, a typed receiver and borrowed patterns keep their existing shapes. *)
  val _ = require "receiver alone"
    (case URust_AST.function_parameters (the_function ctxt "receiver-alone" "fn F(self) {}") of
       [URust_AST.Receiver_Parameter (URust_AST.Receiver_Value, _, _)] => true
     | _ => false)
  val _ = require "typed receivers stay ordinary parameters"
    (case URust_AST.function_parameters
        (the_function ctxt "receiver-typed" "fn F(self: u32, mut other: u32) {}") of
       [URust_AST.Function_Parameter (NONE, URust_AST.P_Ident ("self", _), _, _),
        URust_AST.Function_Parameter (SOME _, URust_AST.P_Ident ("other", _), _, _)] => true
     | _ => false)
  val _ = require "typed self after the first parameter is unchanged"
    (case URust_AST.function_parameters
        (the_function ctxt "receiver-typed-later" "fn F(value: u32, self: u32) {}") of
       [_, URust_AST.Function_Parameter (NONE, URust_AST.P_Ident ("self", _), _, _)] => true
     | _ => false)
  val _ = require "borrowed self patterns stay patterns"
    (case URust_AST.function_parameters
        (the_function ctxt "receiver-borrowed-pattern"
          "fn F(&self: \<tau>\<open>nat\<close>, &mut other: \<tau>\<open>nat\<close>) {}") of
       [URust_AST.Function_Parameter
          (NONE, URust_AST.P_Borrow (URust_AST.BM_Imm, URust_AST.P_Ident ("self", _), _), _, _),
        URust_AST.Function_Parameter
          (NONE, URust_AST.P_Borrow (URust_AST.BM_Mut, URust_AST.P_Ident ("other", _), _), _, _)] =>
         true
     | _ => false)
in end
\<close>

subsection\<open> Receiver rejections \<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  fun later label text needle =
    rejects_at label ["urust: a self receiver must be the first parameter"]
      (range_of text needle 0) (fn () => function_source ctxt label text)
  val _ = later "receiver-second" "fn F(value: u32, self) {}" "self"
  val _ = later "receiver-second-mut" "fn F(value: u32, mut self) {}" "mut self"
  val _ = later "receiver-second-reference" "fn F(value: u32, &'a mut self) {}" "&'a mut self"
  val _ = later "receiver-twice" "fn F(self, &self) {}" "&self"
  val _ = later "receiver-third" "fn F(a: u32, b: u32, &mut self, c: u32) {}" "&mut self"
  val member_text = "impl Counter {\n  fn get(value: u32, &mut self) {}\n}"
  val _ = parse_rejects ctxt "receiver-second-member"
    ["urust: a self receiver must be the first parameter"] member_text "&mut self" 0

  fun untyped label text needle =
    rejects_at label ["requires a type (`name: Type`); only a self receiver omits it"]
      (range_of text needle 0) (fn () => function_source ctxt label text)
  val _ = untyped "parameter-untyped" "fn F(value) {}" "value"
  val _ = untyped "parameter-untyped-mut" "fn F(mut value) {}" "mut value"
  val _ = untyped "parameter-untyped-borrow" "fn F(&value) {}" "&value"
  val _ = untyped "parameter-untyped-later" "fn F(self, &'a mut value) {}" "&'a mut value"
  val _ = untyped "parameter-untyped-Self" "fn F(Self) {}" "Self"
in end
\<close>

section\<open> Serialized roundtrip \<close>

text\<open>
The serialized printer prints each impl with its members on their own lines and each member
annotation on the line before its member. Every envelope, and the whole chunk, reparses to the
same tokens, with one envelope per impl.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  val text =
    "struct Counter { value: u32 }\n" ^
    annotation "register_notation" ^ "\n" ^
    "impl Counter {\n" ^
    "  fn new() -> u32 { 0 }\n\n" ^
    "  " ^ annotation "name = \"counter_peek\", pretty" ^ "\n" ^
    "  fn peek(&self) -> u32 { \<llangle>value\<rrangle> }\n" ^
    "  fn take(mut self) { \<epsilon>\<open>skip\<close> }\n" ^
    "  fn bump<'a>(&'a mut self, step: u32) { () }\n" ^
    "}\n" ^
    "fn Free(value: u32) -> u32 { value }\n" ^
    "impl outer::Pair<u8, \<tau>\<open>'a\<close>> {}\n" ^
    "use demo::value;\n" ^
    "impl Gauge {\n  fn level(self) -> u32 { 1 }\n}"
  val chunk = the_chunk ctxt "roundtrip" text
  val options = URust_Printer.serialized_options
  fun envelope_roundtrip envelope =
    let
      val generated = URust_Printer.string_of_annotated_item options envelope
      val reparsed =
        (case URust_AST.chunk_items (the_chunk ctxt "roundtrip envelope" generated) of
           [reparsed] => reparsed
         | _ => error ("impl audit: envelope did not reparse as one member:\n" ^ generated))
    in
      require ("envelope roundtrip:\n" ^ generated)
        (URust_Printer.tokens_of_annotated_item options reparsed =
          URust_Printer.tokens_of_annotated_item options envelope)
    end
  val _ = List.app envelope_roundtrip (URust_AST.chunk_items chunk)
  val generated = URust_Printer.string_of_chunk options chunk
  val reparsed = the_chunk ctxt "roundtrip chunk" generated
  val _ = require ("chunk roundtrip:\n" ^ generated)
    (URust_Printer.tokens_of_chunk options reparsed = URust_Printer.tokens_of_chunk options chunk)
  val _ = require "roundtrip keeps one envelope per impl"
    (length (URust_AST.chunk_items reparsed) = 6)
  val (_, gauge) = only_impl ctxt "printed impl" (URust_Printer.string_of_annotated_item options
    (nth (URust_AST.chunk_items chunk) 5))
  val _ = require "printed impl keeps its member"
    (map (#1 o URust_AST.function_name o URust_AST.impl_member_function)
      (URust_AST.impl_members gauge) = ["level"])
  val empty = URust_Printer.string_of_annotated_item options (nth (URust_AST.chunk_items chunk) 3)
  val _ = require ("empty impl prints compactly: " ^ empty)
    (empty = "impl outer::Pair<u8, \<tau>\<open>'a\<close>> {}")
  val annotated =
    URust_Printer.string_of_annotated_item options (nth (URust_AST.chunk_items chunk) 1)
  val _ = require ("member annotations print on their own lines:\n" ^ annotated)
    (String.isSubstring
      ("\n  " ^ annotation "name = \"counter_peek\", pretty" ^ "\n  fn peek(&self)") annotated
      andalso String.isPrefix (annotation "register_notation" ^ "\nimpl Counter {\n") annotated)
in end
\<close>

section\<open> Rejections outside chunks \<close>

text\<open>
The single-item parsers and commands reject an impl at its keyword and direct the user to a
chunk. Inside a body, the impl keyword gets the item-in-expression rejection.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  val thy = \<^theory>
  val chunk_member = "urust: impl blocks are chunk members; write urust \<open> impl \<dots> \<close>"
  val text = "impl Counter { fn get(self) -> u32 { 0 } }"
  fun item_mode label parser =
    rejects_at label [chunk_member] (range_of text "impl" 0)
      (fn () => parser ctxt (source label text))
  val _ = item_mode "item-mode-function" URust_Parser.parse_function_source
  val _ = item_mode "item-mode-datatype" URust_Parser.parse_datatype_source
  val _ = item_mode "item-mode-type-alias" URust_Parser.parse_type_alias_source
  val _ = item_mode "item-mode-use" URust_Parser.parse_use_source
  val _ = item_mode "item-mode-item" URust_Parser.parse_item_source

  val _ = rejects_at "expression-mode" ["uRust impl declarations are not expressions"]
    (range_of text "impl" 0) (fn () => URust_Parser.parse_source ctxt (source "expression" text))

  fun command label keyword =
    let val command_text = quiet_prefix "" ^ keyword ^ " " ^ cartouche (" " ^ text ^ " ")
    in command_rejects thy label [chunk_member] command_text "impl" 0 end
  val _ = command "command-urust-fn" "urust_fn"
  val _ = command "command-urust-datatype" "urust_datatype"
  val _ = command "command-urust-type-alias" "urust_type_alias"

  val body = "fn Outer() -> u32 {\n  impl Counter {};\n  0\n}"
  val _ = parse_rejects ctxt "function-body" ["uRust impl declarations are not expressions"]
    body "impl" 0
  val _ =
    rejects_at "function-body-command" ["uRust impl declarations are not expressions"]
      (range_of body "impl" 0) (fn () => function_source ctxt "function-body-command" body)
  val nested = "impl Counter {\n  fn get(self) -> u32 { impl Gauge {}; 0 }\n}"
  val _ = parse_rejects ctxt "member-body" ["uRust impl declarations are not expressions"]
    nested "impl" 1
in end
\<close>

section\<open> Receiver shorthands outside impls \<close>

text\<open>
An impl reaching chunk declaration is elaborated (chapter "Impl block declarations"); the sources
that the elaboration stub once rejected now declare. A receiver shorthand outside an impl member
is rejected at the receiver: a free function has no Self type.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val thy = \<^theory>
  val former_stub =
    quiet_prefix "" ^ "urust " ^
      command_source "struct StubCounter { value: u32 }\nimpl StubCounter {\n  fn get(self) {}\n}"
  val _ = run_commands false "impl-former-stub" thy former_stub
  val former_annotated_stub =
    quiet_prefix "" ^ "urust " ^
      command_source
        ("struct StubGauge;\nfn Before() {}\n" ^ annotation "register_notation" ^
          "\nimpl StubGauge {}")
  val _ = run_commands false "impl-former-stub-annotated" thy former_annotated_stub

  val shorthand = "urust: receiver shorthand is only allowed in impl members"
  fun free label receiver =
    let
      val text =
        quiet_prefix "" ^ "urust_fn " ^
          cartouche (" fn FreeReceiver<'a>(" ^ receiver ^ ") -> u32 { 0 } ")
    in command_rejects thy label [shorthand] text receiver 0 end
  val _ = free "free-receiver-value" "self"
  val _ = free "free-receiver-mut" "mut self"
  val _ = free "free-receiver-reference" "&self"
  val _ = free "free-receiver-mut-reference" "&mut self"
  val _ = free "free-receiver-lifetime" "&'a mut self"
  val chunk_free =
    quiet_prefix "" ^ "urust " ^ command_source "fn ChunkFreeReceiver(&mut self, step: u32) {}"
  val _ = command_rejects thy "free-receiver-chunk" [shorthand] chunk_free "&mut self" 0
in end
\<close>

section\<open> Markup \<close>

text\<open>
\<open>impl\<close> is a reserved word with a typing tooltip, impl braces are delimiters, and the \<open>&\<close>
and \<open>mut\<close> of a receiver keep the roles they have in a reference type.
\<close>

ML\<open>
local
  open Impl_Syntax_Test
  val ctxt = \<^context>
  val text =
    "impl Counter {\n" ^
    "  fn get(&'a mut self, other: &'a mut u32) -> u32 { 0 }\n" ^
    "}"
  val (result, reports) = parse_reports ctxt "markup" text
  val _ = require "markup source parses" (case result of Exn.Res (SOME _) => true | _ => false)
  val _ = require "impl keyword markup"
    (roles_at reports (range_of text "impl" 0) = [("keyword1", ""), ("typing", "TIMPL")])
  val _ = require "impl brace markup"
    (roles_at reports (range_of text "{" 0) = [("delimiter", ""), ("typing", "TLBRACE")] andalso
      roles_at reports (range_of text "}" 1) = [("delimiter", ""), ("typing", "TRBRACE")])
  fun same_role needle =
    require ("receiver " ^ needle ^ " role")
      (roles_at reports (range_of text needle 0) = roles_at reports (range_of text needle 1) andalso
        not (null (roles_at reports (range_of text needle 0))))
  val _ = same_role "&"
  val _ = same_role "mut"
  val _ = same_role "'a"
  val _ = require "receiver self has no lexical markup"
    (null (roles_at reports (range_of text "self" 0)))

  val expression = "impl Counter {}"
  val (_, expression_reports) =
    Parser_Test_Reports.chunks (fn () =>
      Exn.result (URust_Parser.parse_source ctxt) (source "markup-expression" expression))
  val _ = require "impl is a keyword in expression input"
    (exists (String.isSubstring "TIMPL") expression_reports)

  val signature_text = "fn F(value: u32) -> impl Counter { 0 }"
  val signature_function = the_function ctxt "impl-trait-in-signature" signature_text
  val (_, signature_reports) = parse_reports ctxt "impl-trait-markup" signature_text
  val _ = require "impl Trait is retained as a type in a signature"
    (case URust_AST.function_return_type signature_function of
       SOME (URust_AST.Impl_Trait_Type
         (URust_AST.Path_Type
           ([URust_AST.Rust_Type_Path_Segment ("Counter", _, NONE, _)], _), _)) => true
     | _ => false)
  val _ = require "impl Trait keyword keeps impl markup in a signature"
    (roles_at signature_reports (range_of signature_text "impl" 0) =
      [("keyword1", ""), ("typing", "TIMPL")])
  val signature_command = quiet_prefix "" ^ "urust_fn " ^ command_source signature_text
  val _ = command_rejects \<^theory> "impl-trait-unresolved-signature"
    ["Rust impl Trait types is not supported in function signatures"]
    signature_command "impl Counter" 0
  val block_signature = "fn F(value: impl Counter {}) -> u32 { 0 }"
  val _ = rejects_at "impl-block-in-signature" ["syntax error"]
    (range_of block_signature "{" 0)
    (fn () => function_source ctxt "impl-block-in-signature" block_signature)
in end
\<close>

chapter\<open> Impl block declarations \<close>

section\<open> Declaration test support \<close>

text\<open>
Declaration audits run synthetic command sequences on this theory, whose context holds the
declarations of \<open>Parser_Impl_Examples\<close>, and inspect the resulting registry.
\<close>

ML\<open>
structure Impl_Declaration_Test =
struct
  open Impl_Syntax_Test

  fun chunk text = "urust " ^ command_source text
  fun quiet text = quiet_prefix "" ^ text

  fun context_after label thy text = Toplevel.context_of (run_commands false label thy text)

  fun entries ctxt name = Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name

  fun head_name term =
    (case Term.head_of term of
       Const (name, _) => name
     | _ => "")

  fun backends ctxt name = map (head_name o #hol_term) (entries ctxt name)

  (* (automatic, method-only) *)
  fun status ctxt entry =
    (Micro_Rust_Names.is_automatic ctxt entry, Micro_Rust_Names.is_method_only ctxt entry)

  fun the_entry ctxt label name =
    (case entries ctxt name of
       [entry] => entry
     | found =>
         error ("impl declaration audit: " ^ label ^ ": " ^ quote name ^ " has " ^
           string_of_int (length found) ^ " entries"))

  fun owners ctxt name = Micro_Rust_Names.associated_functions ctxt name

  fun owner_types ctxt name = map #self_type (owners ctxt name)

  fun same_types left right = eq_set (op =) (left, right)

  (* Every report element at a range with its body text. *)
  fun texts_at range reports =
    let
      fun events (XML.Elem ((name, properties), body)) =
            (name, properties, XML.content_of body) :: maps events body
        | events (XML.Text _) = []
    in
      maps events reports
      |> filter (fn (_, properties, _) =>
          position_range (Position.of_properties properties) = range)
      |> map (fn (name, _, body) => (name, body))
    end

  fun entity_ids_at range kind def reports =
    reports_at range reports
    |> map_filter (fn (name, properties) =>
        if name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME kind
        then Properties.get properties (if def then Markup.defN else Markup.refN)
        else NONE)
end
\<close>

section\<open> Registrations of the examples \<close>

text\<open>
Every member registers an automatic path entry under its target's canonical path, whose source
serial is the identity of its associated-function owner; a member with a receiver also registers
a method-only entry under its bare name. Alias targets register under the final target with the
expansion as Self type, and locale interpretations register their instances under one identity.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val ctxt = \<^context>
  val path_get = the_entry ctxt "path" "Counter::get"
  val bare_get = the_entry ctxt "bare" "get"
  val _ = require "Counter::get backend"
    (head_name (#hol_term path_get) = \<^const_name>\<open>counter_get\<close> andalso
      head_name (#hol_term bare_get) = \<^const_name>\<open>counter_get\<close>)
  val _ = require "the path entry is automatic and not method-only"
    (status ctxt path_get = (true, false))
  val _ = require "the bare entry is automatic and method-only"
    (status ctxt bare_get = (true, true))
  val _ = require "the path and method entries share the member position"
    (Position.offset_of (#reg_pos path_get) = Position.offset_of (#reg_pos bare_get) andalso
      #serial path_get <> #serial bare_get)
  val _ = require "the owner of Counter::get is the path entry's identity at the Self type"
    (case owners ctxt "Counter::get" of
       [{identity, self_type, pos}] =>
         identity = #serial path_get andalso self_type = \<^typ>\<open>counter\<close> andalso
           Position.offset_of pos = Position.offset_of (#reg_pos path_get)
     | _ => false)
  val _ = require "associated functions have no method entry"
    (null (entries ctxt "new") andalso null (entries ctxt "with_value") andalso
      backends ctxt "Counter::new" = [\<^const_name>\<open>counter_new\<close>] andalso
      owner_types ctxt "Counter::with_value" = [\<^typ>\<open>counter\<close>])
  val _ = require "a typed receiver makes a method"
    (backends ctxt "read_typed" = [\<^const_name>\<open>gauge_read_typed\<close>] andalso
      backends ctxt "touch_typed" = [\<^const_name>\<open>gauge_touch_typed\<close>])
  val _ = require "control declarations registered nothing"
    (null (entries ctxt "Counter::control_counter_get") andalso
      not (member (op =) (backends ctxt "get") \<^const_name>\<open>control_counter_get\<close>))
  val _ = require "targets: enum, mapping, escaped mapping arguments"
    (owner_types ctxt "Mode::flipped" = [\<^typ>\<open>mode\<close>] andalso
      owner_types ctxt "Meter::doubled" = [\<^typ>\<open>nat\<close>] andalso
      (case owner_types ctxt "Slot::items" of
         [Type (\<^type_name>\<open>list\<close>, [TVar _])] => true
       | _ => false))
  val total_owners = owners ctxt "Pair::total"
  val _ = require "two instance impls of Pair own Pair::total"
    (length total_owners = 2 andalso
      #identity (hd total_owners) <> #identity (nth total_owners 1) andalso
      same_types (map #self_type total_owners)
        [\<^typ>\<open>8 word pair\<close>, \<^typ>\<open>16 word pair\<close>] andalso
      same_types (map (fastype_of o #hol_term) (entries ctxt "total"))
        (map (fastype_of o Logic.varify_global)
          [\<^term>\<open>pair_byte_total\<close>, \<^term>\<open>pair_word_total\<close>]))
  val _ = require "alias targets register under the final target"
    (owner_types ctxt "Counter::doubled_value" = [\<^typ>\<open>counter\<close>] andalso
      owner_types ctxt "Pair::left_of" = [\<^typ>\<open>32 word pair\<close>] andalso
      owner_types ctxt "Pair::right_of" = [\<^typ>\<open>8 word pair\<close>] andalso
      null (entries ctxt "CounterAlias::doubled_value") andalso
      null (entries ctxt "Twin::left_of") andalso null (entries ctxt "ByteTwin::right_of"))
  val stored_owners = owners ctxt "Slot::stored"
  val _ = require "interpretations register one impl at each instance type"
    (length stored_owners = 2 andalso
      length (distinct (op =) (map #identity stored_owners)) = 1 andalso
      same_types (map #self_type stored_owners) [\<^typ>\<open>nat list\<close>, \<^typ>\<open>bool list\<close>] andalso
      backends ctxt "stored" =
        replicate 2 \<^const_name>\<open>impl_store.slot_stored\<close> andalso
      length (distinct (op =) (map (fastype_of o #hol_term) (entries ctxt "stored"))) = 2)
  val _ = require "the locale-level instance stays in the locale"
    (exists
      (fn {self_type = Type (\<^type_name>\<open>list\<close>, [TFree _]), ...} => true | _ => false)
      (owners (Locale.init \<^locale>\<open>impl_store\<close> \<^theory>) "Slot::stored"))
in end
\<close>

section\<open> Targets \<close>

text\<open>
Targets are resolved like signature types and must denote nominal Rust types. Every rejection
is positioned at the written target, also when a type alias expands to the rejected shape.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun target label expected header needle =
    let val text = quiet (chunk ("impl " ^ header ^ " {}")) in
      command_rejects thy label expected text needle 0
    end
  val _ = target "target-unknown" ["urust: unknown impl target type \"Countr\""] "Countr" "Countr"
  val _ = target "target-unknown-qualified" ["unknown impl target type \"demo::Countr\""]
    "demo::Countr" "demo::Countr"
  val _ = target "target-arity" ["Rust type \"Pair\" has generic arities [0]"] "Pair" "Pair"
  val primitive = "urust: cannot define an inherent impl for the primitive type"
  val _ = target "target-primitive" [primitive ^ " \"u8\""] "u8" "u8"
  val _ = target "target-primitive-bool" [primitive ^ " \"bool\""] "bool" "bool"
  val non_path = "urust: impl targets must be Rust type paths, not "
  val _ = target "target-reference" [non_path ^ "a mutable reference type"]
    "&mut Counter" "&mut Counter"
  val _ = target "target-shared-reference" [non_path ^ "a shared reference type"]
    "&Counter" "&Counter"
  val _ = target "target-tuple" [non_path ^ "a tuple type"] "(u8, u16)" "(u8, u16)"
  val _ = target "target-array" [non_path ^ "an array type"] "[u8; 4]" "[u8; 4]"
  val _ = target "target-pointer" [non_path ^ "a raw pointer type"] "*const u8" "*const u8"
  val _ = target "target-slice" [non_path ^ "a slice type"] "[u8]" "[u8]"
  (* As every rejection of a HOL type escape, at the escape's content. *)
  val _ = target "target-hol" ["urust: a \<tau>\<open>...\<close> HOL type cannot be an impl target"]
    "\<tau>\<open>nat\<close>" "nat"
  val _ = target "target-parenthesized" [non_path ^ "a parenthesized type"] "(Counter)" "(Counter)"
  val _ = target "target-unit" [primitive ^ " \"()\""] "()" "()"
  val _ = target "target-const-array" [non_path ^ "an array type"] "[u8; N]" "[u8; N]"
  val _ = target "target-hole" ["urust: an impl target must not contain inference holes"]
    "Slot<\<tau>\<open>_\<close>>" "Slot<\<tau>\<open>_\<close>>"
  val _ = target "target-self" ["urust: Self is only available inside an impl block"]
    "Self" "Self"
  val _ = target "target-self-argument" ["urust: Self is only available inside an impl block"]
    "Slot<Self>" "Self"

  fun alias label expected rhs =
    let
      val text =
        quiet ("urust_type_alias " ^ cartouche (" type ImplAliasTarget = " ^ rhs ^ "; ") ^ "\n" ^
          chunk "impl ImplAliasTarget {}")
    in command_rejects thy label expected text "ImplAliasTarget" 1 end
  val _ = alias "alias-primitive"
    [primitive ^ " \"u16\" (through the type alias \"ImplAliasTarget\")"] "u16"
  val alias_of = "urust: impl target \"ImplAliasTarget\" is a type alias of "
  val _ = alias "alias-tuple" [alias_of ^ "a tuple type"] "(u8, u16)"
  val _ = alias "alias-pointer" [alias_of ^ "a raw pointer type"] "*const u8"
  val _ = alias "alias-hol" [alias_of ^ "the HOL type", "nat"] "\<tau>\<open>nat\<close>"
  val _ = alias "alias-array" [alias_of ^ "the HOL type"] "[u8; 4]"
  val chained =
    quiet
      ("urust_type_alias " ^ cartouche " type ImplAliasInner = (u8, bool); " ^ "\n" ^
       "urust_type_alias " ^ cartouche " type ImplAliasOuter = ImplAliasInner; " ^ "\n" ^
       chunk "impl ImplAliasOuter {}")
  val _ = command_rejects thy "alias-chained-tuple"
    ["urust: impl target \"ImplAliasOuter\" is a type alias of a tuple type"]
    chained "ImplAliasOuter" 1
  val chained_primitive =
    quiet
      ("urust_type_alias " ^ cartouche " type ImplAliasByte = u8; " ^ "\n" ^
       "urust_type_alias " ^ cartouche " type ImplAliasByteOuter = ImplAliasByte; " ^ "\n" ^
       chunk "impl ImplAliasByteOuter {}")
  val _ = command_rejects thy "alias-chained-primitive"
    [primitive ^ " \"u8\" (through the type alias \"ImplAliasByteOuter\")"]
    chained_primitive "ImplAliasByteOuter" 1

  (* A target declared earlier in the same chunk, also through a chunk import. *)
  val same_chunk =
    quiet (chunk ("struct ImplLocalTarget { level: u32 }\nimpl ImplLocalTarget {\n" ^
      "  fn level(self) -> u32 { self.level }\n}"))
  val ctxt = context_after "target-same-chunk" thy same_chunk
  val _ = require "a target declared earlier in the chunk"
    (case owner_types ctxt "ImplLocalTarget::level" of
       [Type (name, [])] => Long_Name.base_name name = "impl_local_target"
     | _ => false)
  val imported =
    quiet (chunk ("use Counter as ImportedCounter;\nimpl ImportedCounter {\n" ^
      "  fn imported_value(self) -> u32 { self.value }\n}"))
  val ctxt = context_after "target-imported" thy imported
  val _ = require "an imported target registers under the canonical path"
    (owner_types ctxt "Counter::imported_value" = [\<^typ>\<open>counter\<close>] andalso
      null (entries ctxt "ImportedCounter::imported_value") andalso
      backends ctxt "imported_value" = [Sign.full_name (Proof_Context.theory_of ctxt)
        (Binding.name "imported_counter_imported_value")])
  val empty = quiet (chunk "impl Counter {}")
  val ctxt = context_after "target-empty" thy empty
  val _ = require "an empty impl registers nothing"
    (Micro_Rust_Names.dump ctxt = Micro_Rust_Names.dump \<^context>)
in end
\<close>

section\<open> Receivers and Self \<close>

text\<open>
In an impl member, \<open>self\<close> may only be the first parameter, typed or not, as in Rust; free
functions keep their typed \<open>self\<close> extension. \<open>&self\<close> requires an explicit policy; its missing-policy
message is positioned at the receiver. \<open>Self\<close> outside an impl member is rejected in every type position.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun member label expected source needle occurrence =
    command_rejects thy label expected (quiet (chunk ("impl Counter {\n  " ^ source ^ "\n}")))
      needle occurrence
  val first = "urust: a self receiver must be the first parameter"
  val _ = member "member-typed-self-second" [first]
    "fn late(value: u32, self: Counter) -> u32 { value }" "self" 0
  val _ = member "member-typed-mut-self-second" [first]
    "fn late(value: u32, mut self: Counter) -> u32 { value }" "self" 0
  val _ = member "member-typed-self-third" [first]
    "fn late(self, value: u32, self: Counter) -> u32 { value }" "self" 1
  val _ = member "member-shorthand-second" [first]
    "fn late(value: u32, &mut self) -> u32 { value }" "&mut self" 0
  val shared = "shared Rust references (&T) require an explicit representation"
  val _ = member "member-shared-receiver" [shared] "fn peek(&self) -> u32 { 0_u32 }" "&self" 0
  val _ = member "member-shared-lifetime-receiver" [shared]
    "fn peek<'a>(&'a self) -> u32 { 0_u32 }" "&'a self" 0
  val _ = member "member-undeclared-lifetime" ["undeclared lifetime \"'b\""]
    "fn peek(&'b mut self) -> u32 { 0_u32 }" "'b" 0
  val _ = member "member-self-arguments" ["urust: Self cannot take generic arguments"]
    "fn peek(self: Self<u8>) -> u32 { 0_u32 }" "Self<u8>" 0

  (* A free function keeps typed self after the first parameter. *)
  val free_typed =
    quiet ("urust_fn " ^ cartouche " fn ImplFreeTypedSelf(value: u32, self: u32) -> u32 { value } ")
  val _ = run_commands false "free-typed-self-second" thy free_typed

  val outside = "urust: Self is only available inside an impl block"
  fun outside_at label text = command_rejects thy label [outside] (quiet text) "Self" 0
  val _ = outside_at "self-free-parameter"
    ("urust_fn " ^ cartouche " fn ImplOutsideProbe(value: Self) -> u32 { 0_u32 } ")
  val _ = outside_at "self-free-result"
    ("urust_fn " ^ cartouche " fn ImplOutsideProbe(value: u32) -> Self { value } ")
  val _ = outside_at "self-chunk-function"
    (chunk "fn ImplOutsideProbe(value: Pair<Self>) -> u32 { 0_u32 }")
  val _ = outside_at "self-datatype-field"
    ("urust_datatype " ^ cartouche " struct ImplOutsideProbe { next: Self } ")
  val _ = outside_at "self-type-alias" ("urust_type_alias " ^ cartouche " type ImplOutside = Self; ")
  val _ = outside_at "self-after-impl"
    (chunk "impl Counter {}\nfn ImplOutsideProbe(value: Self) -> u32 { 0_u32 }")
  (* The Self context ends with its member's declaration. *)
  val _ = outside_at "self-later-command"
    (chunk "impl Counter {\n  fn later_probe(self) -> u32 { 0_u32 }\n}" ^ "\n" ^
      "urust_fn " ^ cartouche " fn ImplLaterProbe(value: Self) -> u32 { 0_u32 } ")

  (* Self in a cast target of a member body. *)
  val cast =
    quiet (chunk ("impl Counter {\n  fn cast_probe(self, value: u32) -> u32 { value as Self }\n}"))
  val _ = command_rejects thy "self-cast-target" ["has no supported cast operation"] cast
    "Self" 0
in end
\<close>

section\<open> Ownership and conflicts \<close>

text\<open>
Two impls conflict when they define the same associated function at unifying Self types: within
one impl, across impls, against an earlier declaration, and across merged theories in both
orders. Different instances of one type constructor coexist, and an associated function cannot
share its path with an enum variant.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val overlap = "is defined in more than one impl with overlapping Self types"
  fun conflict label key text needle occurrence =
    command_rejects thy label ["urust: associated function \"" ^ key ^ "\" " ^ overlap]
      (quiet (chunk text)) needle occurrence
  (* Against a member of an earlier theory, the message lists that member first. *)
  fun conflict_listing label key text needle =
    let
      val text = quiet (chunk text)
      val message =
        expect_failure label ["urust: associated function \"" ^ key ^ "\" " ^ overlap]
          (fn () => run_commands false label thy text)
      val positions = message_positions message
    in
      (* The earlier member, then this member, then the failing command. *)
      require (label ^ ": listed positions")
        (length positions >= 2 andalso
          Position.file_of (hd positions) <> SOME label andalso
          position_range (nth positions 1) = range_within text ("fn " ^ needle) needle)
    end
  val _ = conflict "duplicate-within-impl" "Counter::twice"
    ("impl Counter {\n  fn twice(self) -> u32 { 0_u32 }\n" ^
     "  \<omega>\<open>name = \"counter_twice_again\"\<close>\n  fn twice(self) -> u32 { 1_u32 }\n}")
    "twice" 0
  val _ = conflict "duplicate-across-impls" "Counter::twice"
    ("impl Counter {\n  fn twice(self) -> u32 { 0_u32 }\n}\n" ^
     "impl Counter {\n  \<omega>\<open>name = \"counter_twice_again\"\<close>\n" ^
     "  fn twice() -> u32 { 1_u32 }\n}")
    "twice" 0
  val _ = conflict_listing "duplicate-earlier-declaration" "Counter::get"
    ("impl CounterAlias {\n  \<omega>\<open>name = \"counter_get_again\"\<close>\n" ^
     "  fn get(self) -> u32 { 0_u32 }\n}")
    "get"
  val _ = conflict_listing "duplicate-polymorphic-instance" "Slot::items"
    ("impl Slot<\<tau>\<open>nat\<close>> {\n  \<omega>\<open>name = \"slot_nat_items\"\<close>\n" ^
     "  fn items(self) -> \<tau>\<open>nat list\<close> { self }\n}")
    "items"
  val third =
    quiet (chunk ("impl Pair<u32> {\n  \<omega>\<open>name = \"pair_wide_total\"\<close>\n" ^
      "  fn total(self) -> u32 { self.left }\n}"))
  val ctxt = context_after "distinct-instance" thy third
  val _ = require "a third instance impl coexists"
    (length (owners ctxt "Pair::total") = 3 andalso length (entries ctxt "total") = 3)
  val _ =
    command_rejects thy "member-against-variant"
      ["Rust function path \"Mode::On\" is already owned by a Rust constructor item"]
      (quiet (chunk "impl Mode {\n  fn On() -> u32 { 0_u32 }\n}")) "On" 0
in end
\<close>

subsection\<open> Merged theories \<close>

ML\<open>
local
  open Impl_Declaration_Test
  fun branch name parents text =
    Theory.begin_theory (name, Position.none) parents
    |> (fn thy => if text = "" then thy
         else Toplevel.theory_of (run_commands false name thy (quiet text)))
    |> Theory.end_theory
  val parent =
    branch "Impl_Merge_Parent" [\<^theory>]
      (chunk "struct MergeDial { notch: u32 }\nstruct MergePair<T> { left: T }")
  fun member target self_type =
    chunk ("impl " ^ target ^ " {\n  fn read(self) -> " ^ self_type ^ " { self.left }\n}")
  val left = branch "Impl_Merge_Left" [parent]
    (chunk "impl MergeDial {\n  fn read(self) -> u32 { self.notch }\n}")
  val right = branch "Impl_Merge_Right" [parent]
    (chunk "impl MergeDial {\n  fn read(self) -> u32 { 0_u32 }\n}")
  val byte = branch "Impl_Merge_Byte" [parent] (member "MergePair<u8>" "u8")
  val word = branch "Impl_Merge_Word" [parent] (member "MergePair<u16>" "u16")
  fun merged label theories = Theory.begin_theory (label, Position.none) theories
  val overlap =
    "urust: associated function \"MergeDial::read\" is defined in more than one impl " ^
      "with overlapping Self types"
  fun rejected label theories =
    let
      val message = expect_failure label [overlap] (fn () => merged label theories)
      val positions = message_positions message
    in
      require (label ^ ": both members are listed")
        (length positions = 2 andalso
          Position.file_of (hd positions) <> Position.file_of (nth positions 1))
      ; message
    end
  val left_right = rejected "merge-left-right" [left, right]
  val right_left = rejected "merge-right-left" [right, left]
  val _ = require "the merge conflict does not depend on the merge order"
    (left_right = right_left)
  val instances = Proof_Context.init_global (merged "merge-instances" [byte, word])
  val reversed = Proof_Context.init_global (merged "merge-instances-reversed" [word, byte])
  fun owner_rows ctxt =
    owners ctxt "MergePair::read" |> map (fn {self_type, identity, ...} => (self_type, identity))
  (* Gauge::read of the examples also owns a method entry "read". *)
  val base_reads = length (entries \<^context> "read")
  val _ = require "differently instantiated impls merge in both orders"
    (length (owner_rows instances) = 2 andalso
      eq_set (op =) (owner_rows instances, owner_rows reversed) andalso
      length (entries instances "read") = base_reads + 2 andalso
      length (entries reversed "read") = base_reads + 2)
in end
\<close>

section\<open> Options \<close>

text\<open>
Member annotations override impl annotations, which override the outer chunk defaults, which
override scoped configurations; no configuration changes. \<open>register_notation = false\<close>
suppresses both registrations of a member, and \<open>name = _\<close> checks it without defining or
registering anything.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val text =
    quiet
      ("urust_datatype " ^ cartouche " struct Knob { level: u32 } " ^ "\n" ^
       "declare [[urust_register_notation = false, urust_abbrev = true]]\n" ^
       "urust [register_notation] " ^
       command_source
         (annotation "register_notation = false" ^ "\n" ^
          "impl Knob {\n" ^
          "  fn by_impl(self) -> u32 { self.level }\n\n" ^
          "  " ^ annotation "register_notation, abbrev = false" ^ "\n" ^
          "  fn by_member(self) -> u32 { self.level }\n\n" ^
          "  " ^ annotation "name = _" ^ "\n" ^
          "  fn checked(self) -> u32 { self.level }\n\n" ^
          "  " ^ annotation "name = \"renamed_knob_value\", abbrev = false, register_notation" ^ "\n" ^
          "  fn renamed() -> u32 { 1_u32 }\n" ^
          "}\n\n" ^
          "impl Knob {\n  fn by_outer(self) -> u32 { self.level }\n\n" ^
          "  " ^ annotation "register_notation = false" ^ "\n" ^
          "  fn by_member_off(self) -> u32 { self.level }\n}") ^ "\n" ^
       chunk "impl Knob {\n  fn by_config(self) -> u32 { self.level }\n}")
  val ctxt = context_after "options-precedence" thy text
  fun registered name = not (null (entries ctxt ("Knob::" ^ name)))
  fun method name = not (null (entries ctxt name))
  fun definition name = fact_declared ctxt ("knob_" ^ name ^ "_def")
  (* A definition or an abbreviation. *)
  fun declared_in ctxt name =
    Name_Space.declared (Consts.space_of (Proof_Context.consts_of ctxt))
      (Sign.full_name (Proof_Context.theory_of ctxt) (Binding.name name))
  fun declared name = declared_in ctxt ("knob_" ^ name)
  val _ = require "impl annotation over the outer default"
    (not (registered "by_impl") andalso not (method "by_impl") andalso
      not (definition "by_impl") andalso declared "by_impl")
  val _ = require "member annotation over the impl annotation and the configuration"
    (registered "by_member" andalso method "by_member" andalso definition "by_member")
  (* Disabled registration keeps the associated-function owner: overlap belongs to the impl. *)
  val _ = require "a member annotation disables both registrations, keeping the owner"
    (not (registered "by_member_off") andalso not (method "by_member_off") andalso
      length (owners ctxt "Knob::by_member_off") = 1 andalso declared "by_member_off")
  val _ = require "an impl annotation disables both registrations, keeping the owner"
    (length (owners ctxt "Knob::by_impl") = 1)
  val _ = require "outer default over the configuration"
    (registered "by_outer" andalso method "by_outer" andalso not (definition "by_outer"))
  val _ = require "configuration without any option"
    (not (registered "by_config") andalso not (method "by_config") andalso declared "by_config")
  val _ = require "name = _ defines and registers nothing"
    (not (declared "checked") andalso not (registered "checked") andalso
      null (owners ctxt "Knob::checked"))
  val _ = require "an explicit name binds the HOL name and keeps the Rust key"
    (backends ctxt "Knob::renamed" = [Sign.full_name (Proof_Context.theory_of ctxt)
      (Binding.name "renamed_knob_value")] andalso not (declared "renamed"))
  val later =
    context_after "options-configuration-restored" thy
      (text ^ "\nurust_fn " ^ cartouche " fn KnobLater() -> u32 { 1_u32 } ")
  val _ = require "configurations are unchanged after the chunk"
    (null (entries later "KnobLater") andalso declared_in later "knob_later" andalso
      not (fact_declared later "knob_later_def"))

  val impl_name = "urust: option \"name\" names one function; supply it in an \<omega> annotation"
  val _ =
    command_rejects thy "impl-annotation-name" [impl_name]
      (quiet (chunk (annotation "name = \"knob_all\"" ^ "\nimpl Counter {}"))) "name" 0
  val _ =
    command_rejects thy "impl-annotation-datatype-option"
      ["urust: option \"backend\" does not apply to impl declarations"]
      (quiet (chunk (annotation "backend = hol" ^ "\nimpl Counter {}"))) "backend" 0
  val member_pp_test =
    quiet (chunk ("impl Counter {\n  " ^ annotation "pp_test" ^
      "\n  fn probe(self) -> u32 { 0_u32 }\n}"))
  val _ =
    rejects_at "impl-member-pp-test"
      ["urust: pp_test applies to the whole impl; set it on the impl annotation"]
      (range_within member_pp_test (annotation "pp_test") "pp_test")
      (fn () => run_commands false "impl-member-pp-test" thy member_pp_test)
  val _ =
    command_rejects thy "impl-member-datatype-option"
      ["urust: option \"hol_names\" does not apply to fn declarations"]
      (quiet (chunk ("impl Counter {\n  " ^ annotation "hol_names = []" ^
        "\n  fn probe(self) -> u32 { 0_u32 }\n}"))) "hol_names" 0
  (* Annotation payloads are validated before the first declaration. *)
  val early =
    quiet (chunk ("fn ImplEarlierProbe() -> u32 { Missing() }\nimpl Counter {\n  " ^
      annotation "verbosity = 3" ^ "\n  fn probe(self) -> u32 { 0_u32 }\n}"))
  val _ =
    rejects_at "impl-member-option-before-declaration"
      ["uRust command option \"verbosity\" must be 0, 1, or 2"]
      (range_within early "verbosity = 3" "3")
      (fn () => run_commands false "impl-member-option-before-declaration" thy early)
in end
\<close>

section\<open> Explicit registrations \<close>

text\<open>
An explicit call notation coexists with the impl's entries under both keys. A registration of
another backend accumulates as an overload, before or after the impl; a registration of the same
backend after the impl makes the covered entry explicit, keeping its identity. A member always
defines a new constant, so an explicit registration of its backend cannot precede it.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val setup =
    quiet
      ("urust_datatype " ^ cartouche " struct Dial { notch: u32 } " ^ "\n" ^
       "urust_fn [register_notation = false] dial_other " ^
         cartouche " fn other(self: Dial) -> bool { true } " ^ "\n" ^
       "micro_rust_notation (call) dial_other (\"Dial::read\")\n" ^
       "micro_rust_notation (call) dial_other (\"read\")\n" ^
       chunk "impl Dial {\n  fn read(self) -> u32 { self.notch }\n}" ^ "\n")
  val before_ctxt = context_after "explicit-before" thy setup
  val dial_read = Sign.full_name (Proof_Context.theory_of before_ctxt) (Binding.name "dial_read")
  val dial_other = Sign.full_name (Proof_Context.theory_of before_ctxt) (Binding.name "dial_other")
  (* Gauge::read of the examples also owns a method entry "read". *)
  fun row ctxt name =
    entries ctxt name
    |> map (fn entry => (head_name (#hol_term entry), status ctxt entry))
    |> filter (fn (backend, _) => String.isPrefix "Parser_Impl_ML_Tests.dial_" backend)
    |> sort (prod_ord string_ord (K EQUAL))
  val _ = require "an earlier explicit registration of another backend accumulates"
    (row before_ctxt "Dial::read" = sort (prod_ord string_ord (K EQUAL))
        [(dial_read, (true, false)), (dial_other, (false, false))] andalso
      row before_ctxt "read" = sort (prod_ord string_ord (K EQUAL))
        [(dial_read, (true, true)), (dial_other, (false, false))])
  val use_dial =
    "urust_fn " ^ cartouche " fn UseDial(d: Dial) -> u32 { d.read() + Dial::read(d) } "
  val use_ctxt = context_after "explicit-before-use" thy (setup ^ use_dial)
  val _ = require "the overloads dispatch by type"
    (exists (fn Const (name, _) => name = dial_read | _ => false)
      (Term.add_consts (Thm.prop_of (Proof_Context.get_thm use_ctxt "use_dial_def")) []
        |> map Const))
  fun read_serial ctxt =
    #serial (the_single (filter (fn entry => head_name (#hol_term entry) = dial_read)
      (entries ctxt "Dial::read")))
  val _ = require "the path entry is the member's identity"
    (map #identity (owners before_ctxt "Dial::read") = [read_serial before_ctxt])
  val after =
    context_after "explicit-after" thy
      (setup ^
       "micro_rust_notation (call) dial_read (\"Dial::read\")\n" ^
       "micro_rust_notation (call) dial_read (\"read\")\n" ^
       "urust_fn [register_notation = false] dial_third " ^
         cartouche " fn third(self: Dial) -> u8 { 3_u8 } " ^ "\n" ^
       "micro_rust_notation (call) dial_third (\"Dial::read\")\n" ^
       "micro_rust_notation (call) dial_third (\"read\")")
  val dial_third = Sign.full_name (Proof_Context.theory_of after) (Binding.name "dial_third")
  val _ = require "a later explicit registration of the same backend makes the entries explicit"
    (row after "Dial::read" = sort (prod_ord string_ord (K EQUAL))
        [(dial_read, (false, false)), (dial_other, (false, false)),
         (dial_third, (false, false))] andalso
      row after "read" = sort (prod_ord string_ord (K EQUAL))
        [(dial_read, (false, false)), (dial_other, (false, false)),
         (dial_third, (false, false))])
  val _ = require "the replaced path entry keeps the member's identity"
    (map #identity (owners after "Dial::read") = [read_serial after])
in end
\<close>

section\<open> Dispatch \<close>

text\<open>
Method calls dispatch by receiver type: across types, across instances of one type constructor,
and across interpretations. A receiver whose type does not fix the instance is ambiguous, and
same-typed interpretations are ambiguous unless registration is disabled in the locale.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  fun consts_of name =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))) []
  val _ = require "instance dispatch"
    (member (op =) (consts_of "use_pair_byte_total") \<^const_name>\<open>pair_byte_total\<close> andalso
      not (member (op =) (consts_of "use_pair_byte_total") \<^const_name>\<open>pair_word_total\<close>) andalso
      member (op =) (consts_of "use_pair_word_total") \<^const_name>\<open>pair_word_total\<close>)
  val _ = require "interpretation dispatch"
    (member (op =) (consts_of "use_stored_nat") \<^const_name>\<open>impl_store.slot_stored\<close> andalso
      member (op =) (consts_of "use_stored_bool") \<^const_name>\<open>impl_store.slot_stored\<close>)
  val ambiguous =
    quiet ("urust_fn " ^
      cartouche " fn ImplPolymorphicTotal(p: Pair<\<tau>\<open>_\<close>>) -> u32 { let t = p.total(); 0_u32 } ")
  val _ =
    expect_failure "polymorphic-receiver" ["Ambiguous uRust notation \<open>total\<close>"]
      (fn () => run_commands false "polymorphic-receiver" thy ambiguous)

  fun locale_text options =
    "locale impl_twin_store =\n  fixes impl_twin_seed :: " ^ cartouche " 'a " ^
    "\nbegin\n" ^ "urust " ^ options ^ command_source
      ("impl Slot<\<tau>\<open>'a\<close>> {\n  fn twin_stored(self) -> \<tau>\<open>'a list\<close> " ^
       "{ \<llangle>impl_twin_seed # self\<rrangle> }\n}") ^
    "\nend\n" ^
    "interpretation impl_twin_first: impl_twin_store " ^ cartouche " 0 :: nat " ^ " .\n" ^
    "interpretation impl_twin_second: impl_twin_store " ^ cartouche " 1 :: nat " ^ " .\n"
  val use =
    "urust_fn " ^
      cartouche " fn ImplTwinUse(s: Slot<\<tau>\<open>nat\<close>>) -> \<tau>\<open>nat list\<close> { s.twin_stored() } "
  val _ =
    expect_failure "same-typed-instances" ["Ambiguous uRust notation \<open>twin_stored\<close>"]
      (fn () => run_commands false "same-typed-instances" thy (quiet (locale_text "" ^ use)))
  val opt_out = context_after "same-typed-opt-out" thy (quiet (locale_text "[register_notation = false] "))
  (* The opt-out registers no entry; the instances keep one owner of one impl. *)
  val _ = require "the opt-out registers nothing for same-typed instances"
    (null (entries opt_out "twin_stored") andalso null (entries opt_out "Slot::twin_stored") andalso
      length (distinct (op =) (map #identity (owners opt_out "Slot::twin_stored"))) = 1)
  val same = context_after "same-typed-owners" thy (quiet (locale_text ""))
  val _ = require "same-typed instances are one owner"
    (length (owners same "Slot::twin_stored") = 1)
in end
\<close>

section\<open> Atomicity \<close>

text\<open>
An impl is part of its chunk's transaction. A failure in a later member, a later impl or a later
item leaves no declaration, registration, owner, semantic report or successful output, at theory
level and in a locale, and the corrected chunk then succeeds.
\<close>

ML\<open>
structure Impl_Atomicity =
struct
  open Impl_Declaration_Test

  (* The lexical baseline of Chunk_Test, extended by the impl annotation schema and the member
     annotations inside impl braces, which are read before the first declaration as well. *)
  fun lexical_reports label thy text =
    let
      val ctxt = Proof_Context.init_global thy
      val keywords = Thy_Header.get_keywords' ctxt
      val tokens = Token.explode keywords (start_position label) text
      val after_command =
        (case find_index (fn token => Token.is_command token andalso Token.content_of token = "urust")
            tokens of
           ~1 => error ("impl atomicity: no urust command in " ^ label)
         | index => drop index tokens)
      val cartouche =
        (case List.find (fn token => Token.kind_of token = Token.Cartouche) after_command of
           SOME token => token
         | NONE => error ("impl atomicity: no cartouche in " ^ label))
      val source = Parser_Lex_Util.cartouche_source cartouche
      val captured = Synchronized.var ("impl lexical reports " ^ label) ([]: string list)
      fun collect chunks = Synchronized.change captured (fn messages => messages @ [implode chunks])
      fun read schema annotation =
        ignore (URust_Command.read_annotation_options ctxt schema annotation)
      fun read_envelope envelope =
        (case URust_AST.annotated_item_item envelope of
           URust_AST.Impl_Item_Node impl =>
             (Option.app (read URust_Command.Impl_Annotation)
                (URust_AST.annotated_item_annotation envelope);
              List.app
                (Option.app (read URust_Command.Impl_Member_Annotation) o
                  URust_AST.impl_member_annotation)
                (URust_AST.impl_members impl))
         | URust_AST.Function_Item_Node _ =>
             Option.app (read URust_Command.Function_Annotation)
               (URust_AST.annotated_item_annotation envelope)
         | _ =>
             Option.app (read URust_Command.Datatype_Annotation)
               (URust_AST.annotated_item_annotation envelope))
      val _ =
        Parser_Test_Report_Lock.run (fn () =>
          Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
            Unsynchronized.setmp Private_Output.report_fn collect (fn () =>
              (case URust_Parser.parse_chunk_source ctxt source of
                 SOME chunk => List.app read_envelope (URust_AST.chunk_items chunk)
               | NONE => ())) ()) ())
    in maps YXML.parse_body (Synchronized.value captured) end

  fun non_lexical label thy text command_start reports =
    let val lexical = map #2 (report_keys (lexical_reports label thy text)) in
      report_keys reports
      |> filter (fn (start, _) => start >= command_start)
      |> map #2
      |> filter_out (member (op =) lexical)
      |> sort_distinct string_ord
    end

  val loud = "declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]\n"
  val earlier_members =
    "    fn atomic_read(self) -> u32 { self.level }\n" ^
    "    " ^ annotation "name = \"atomic_gauge_fresh\", pretty = false" ^ "\n" ^
    "    fn fresh() -> Self { AtomicGauge { level: 0_u32 } }\n"
  fun source members later =
    "  struct AtomicGauge { level: u32 }\n" ^
    "  " ^ annotation "register_notation" ^ "\n" ^
    "  impl AtomicGauge {\n" ^ earlier_members ^ members ^ "  }\n" ^
    "  fn AtomicImplUse(g: AtomicGauge) -> u32 { g.atomic_read() + AtomicGauge::atomic_read(g) }\n" ^
    later
  val failures =
    [("member-typing", "    fn broken(self) -> bool { 1_u32 }\n", "", "fn broken",
       ["Type unification failed"]),
     ("member-duplicate",
       "    " ^ annotation "name = \"atomic_gauge_again\"" ^ "\n" ^
         "    fn atomic_read(self) -> u32 { 0_u32 }\n", "", "atomic_gauge_again",
       ["associated function \"AtomicGauge::atomic_read\" is defined in more than one impl"]),
     ("member-binding",
       "    " ^ annotation "name = \"atomic_gauge_fresh\"" ^ "\n" ^ "    fn again() -> u32 { 0_u32 }\n",
       "", "fn again", ["atomic_gauge_fresh"]),
     ("member-receiver", "    fn shared(&self) -> u32 { 0_u32 }\n", "", "fn shared",
       ["shared Rust references (&T) require an explicit representation"]),
     ("later-impl", "", "  impl AtomicMissing {}\n", "impl AtomicMissing",
       ["unknown impl target type \"AtomicMissing\""]),
     ("later-item", "", "  fn AtomicImplBroken() -> bool { 1_u32 }\n", "fn AtomicImplBroken",
       ["Type unification failed"])]

  (* reopen enters the target of wrap again, without closing it, for the corrected chunk. *)
  fun failing_case target wrap reopen (label, members, later, failing, expected) =
    let
      val label = "impl-atomic-" ^ target ^ "-" ^ label
      val text = loud ^ wrap (chunk (source members later))
      val {result, output, warnings, reports} = capture true label \<^theory> text
      val _ = failure_message ("impl atomic " ^ label) expected result
      val chunk_output =
        filter_out (String.isPrefix "locale atomic_loc") (authored_output output)
      val _ =
        require ("failed " ^ label ^ " chunk printed successful output:\n" ^ cat_lines chunk_output)
          (null chunk_output)
      val command_start = #1 (range_of text "urust " 0)
      val _ =
        require ("failed " ^ label ^ " chunk replayed semantic reports")
          (null (filter (fn event => #1 (report_range event) >= command_start)
            (semantic_entities reports)))
      val _ =
        require ("failed " ^ label ^ " chunk emitted warnings:\n" ^ cat_lines warnings)
          (null warnings)
      val failing_start = #1 (range_of text failing 0)
      fun key_start key =
        (case space_explode "|" key of
           _ :: _ :: start :: _ => the_default 0 (Int.fromString start)
         | _ => 0)
      val leaked =
        filter (fn key => key_start key < failing_start)
          (non_lexical label \<^theory> text command_start reports)
      val _ =
        require ("failed " ^ label ^ " chunk left non-lexical reports of earlier members:\n" ^
            cat_lines leaked)
          (null leaked)
      (* The corrected chunk, after the failed one in the same command sequence. *)
      val corrected = text ^ "\n" ^ reopen (chunk (source "" ""))
      val transitions =
        Outer_Syntax.parse_text \<^theory> (K \<^theory>) (start_position label) corrected
      val state =
        fold (fn transition => fn state =>
            (case Exn.result (Toplevel.command_exception false transition) state of
               Exn.Res state' => state'
             | Exn.Exn _ => state))
          transitions (Toplevel.make_state (SOME \<^theory>))
      val ctxt = Toplevel.context_of state
    in
      require ("corrected " ^ label ^ " chunk did not declare the impl")
        (length (owners ctxt "AtomicGauge::atomic_read") = 1 andalso
          length (entries ctxt "AtomicGauge::atomic_read") = 1)
    end

  fun reopen_locale body = "context atomic_loc\nbegin\n" ^ body ^ "\n"
end
\<close>

ML\<open>
local
  open Impl_Atomicity
  val _ = List.app (failing_case "theory" I I) (take 3 failures)
in end
\<close>

ML\<open>
local
  open Impl_Atomicity
  val _ = List.app (failing_case "theory" I I) (drop 3 failures)
in end
\<close>

ML\<open>
local
  open Impl_Atomicity
  val _ =
    List.app (failing_case "locale" Chunk_Atomicity.in_locale reopen_locale) (take 3 failures)
in end
\<close>

ML\<open>
local
  open Impl_Atomicity
  val _ =
    List.app (failing_case "locale" Chunk_Atomicity.in_locale reopen_locale) (drop 3 failures)
in end
\<close>

section\<open> Markup and navigation \<close>

text\<open>
A member name carries the native definition entity of its constant and the notation entities of
its path and method entries; path and method calls navigate to them. \<open>Self\<close> in a type
references the target's type mapping, with the typing tooltip \<open>Self = Target\<close>, and a target
written through an alias references the alias.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val text =
    quiet
      (chunk
        ("struct MarkGauge { level: u32 }\n" ^
         "impl MarkGauge {\n" ^
         "  fn level_of(self) -> u32 { self.level }\n" ^
         "  fn merged(self, other: Self) -> Self { other }\n" ^
         "}\n" ^
         "fn MarkUse(g: MarkGauge) -> u32 { g.level_of() + MarkGauge::level_of(g) }") ^ "\n" ^
       "urust_type_alias " ^ cartouche " type MarkAlias = MarkGauge; " ^ "\n" ^
       chunk "impl MarkAlias {\n  fn alias_level(self) -> Self { self }\n}")
  val {result, reports, ...} = capture true "impl-markup" \<^theory> text
  val ctxt = result_context result
  val notation = Micro_Rust_Names.notationN
  val member_range = range_within text "fn level_of" "level_of"
  val definition_ids = entity_ids_at member_range notation true reports
  val _ = require "the member name defines its path and method entries"
    (length definition_ids = 2 andalso
      eq_set (op =) (definition_ids,
        map (string_of_int o #serial)
          (entries ctxt "MarkGauge::level_of" @
            filter (fn entry => head_name (#hol_term entry) = Sign.full_name
              (Proof_Context.theory_of ctxt) (Binding.name "mark_gauge_level_of"))
              (entries ctxt "level_of"))))
  val _ = require "the member name defines its constant"
    (member (op =) (entity_kinds_at member_range reports) Markup.constantN)
  fun references_at range = entity_ids_at range notation false reports
  val method_range = range_within text "g.level_of" "level_of"
  val path_range = range_within text "MarkGauge::level_of(g)" "level_of"
  val _ = require "the method call navigates to the member"
    (exists (member (op =) definition_ids) (references_at method_range))
  val _ = require "the path call navigates to the member"
    (exists (member (op =) definition_ids) (references_at path_range))

  val mapping = "micro_rust_type_mapping"
  val target_ids = entity_ids_at (range_of text "MarkGauge" 0) mapping true reports
  fun self_at occurrence =
    let val range = range_within text (if occurrence = 0 then "other: Self" else "-> Self") "Self"
    in
      require ("Self type markup " ^ string_of_int occurrence)
        (not (null target_ids) andalso
          entity_ids_at range mapping false reports = target_ids andalso
          member (op =) (texts_at range reports) ("typing", "Self = MarkGauge") andalso
          member (op =) (map #1 (texts_at range reports)) Markup.keyword3N)
    end
  val _ = self_at 0
  val _ = self_at 1
  val _ = require "the impl target references the mapping"
    (entity_ids_at (range_within text "impl MarkGauge" "MarkGauge") mapping false reports =
      target_ids)
  val alias_ids = entity_ids_at (range_within text "type MarkAlias" "MarkAlias") mapping true reports
  val alias_self = range_within text "alias_level(self) -> Self" "Self"
  val _ = require "an alias target and its Self reference the alias"
    (not (null alias_ids) andalso
      entity_ids_at (range_within text "impl MarkAlias" "MarkAlias") mapping false reports =
        alias_ids andalso
      entity_ids_at alias_self mapping false reports = alias_ids andalso
      member (op =) (texts_at alias_self reports) ("typing", "Self = MarkGauge"))
in end
\<close>

section\<open> Output \<close>

text\<open>
At verbosity 1 and 2 each member prints its declaration followed by its registration manifest,
\<open>associated T::f \<mapsto> c\<close> or \<open>method T::f / .f \<mapsto> c\<close>; verbosity 0 prints nothing.
\<open>pretty\<close> replays member bodies as uRust, and \<open>pp_test\<close> roundtrips the impl through the
chunk printer. The notation listing tags path entries \<open>generated\<close> and method entries
\<open>generated, method-only\<close>.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  fun text verbosity options =
    "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = " ^ verbosity ^
      "]]\n" ^
    "urust " ^ options ^
    command_source
      ("struct OutGauge { level: u32 }\n" ^
       "impl OutGauge {\n" ^
       "  fn fresh() -> Self { OutGauge { level: 0_u32 } }\n\n" ^
       "  fn level_of(self) -> u32 { self.level }\n\n" ^
       "  " ^ annotation "register_notation = false" ^ "\n" ^
       "  fn hidden(self) -> u32 { self.level }\n" ^
       "}")
  fun output verbosity options =
    let val {result, output, ...} = capture true ("impl-output-" ^ verbosity) \<^theory>
      (text verbosity options)
    in (ignore (result_context result); authored_output output) end
  val fresh = "associated OutGauge::fresh \<mapsto> out_gauge_fresh"
  val level = "method OutGauge::level_of / .level_of \<mapsto> out_gauge_level_of"
  val _ = require "verbosity 0 prints nothing" (null (output "0" ""))
  val _ = require "verbosity 1 prints each member and its manifest"
    (case output "1" "" of
       [_, fresh_definition, fresh_manifest, level_definition, level_manifest, hidden] =>
         String.isPrefix "definition out_gauge_fresh_def:" fresh_definition andalso
         fresh_manifest = fresh andalso
         String.isPrefix "definition out_gauge_level_of_def:" level_definition andalso
         level_manifest = level andalso
         String.isPrefix "definition out_gauge_hidden_def:" hidden
     | _ => false)
  val _ = require "verbosity 2 prints the definitions and the manifests"
    (case output "2" "" of
       [_, fresh_definition, fresh_manifest, _, level_manifest, _] =>
         String.isSubstring "out_gauge_fresh \<equiv>" fresh_definition andalso
         fresh_manifest = fresh andalso level_manifest = level
     | _ => false)
  val _ = require "pretty replays the member bodies"
    (case output "2" "[pretty, pp_test] " of
       [_, _, _, level_definition, _, _] =>
         String.isSubstring "FunctionBody" level_definition andalso
         String.isSubstring "self.level" level_definition
     | _ => false)

  (* The command-level roundtrip of an impl with every receiver form and member annotations. *)
  val roundtrip =
    quiet
      ("urust [pp_test] " ^
       command_source
         ("struct TripGauge { level: u32 }\n" ^
          annotation "register_notation" ^ "\n" ^
          "impl TripGauge {\n" ^
          "  " ^ annotation "name = \"trip_read\"" ^ "\n" ^
          "  fn read(self) -> u32 { self.level }\n\n" ^
          "  fn read_mut(mut self) -> u32 { self.level }\n\n" ^
          "  fn touch<'a>(&'a mut self, step: u32) -> u32 { step }\n\n" ^
          "  fn touch_now(&mut self) -> u32 { 0_u32 }\n\n" ^
          "  fn typed(self: Self, other: TripGauge) -> Self { other }\n" ^
          "}\n" ^
          "impl TripGauge {}"))
  val ctxt = context_after "impl-pp-test" \<^theory> roundtrip
  val _ = require "the roundtripped impl declares"
    (length (owners ctxt "TripGauge::read") = 1 andalso length (owners ctxt "TripGauge::typed") = 1)

  val listing_ctxt = \<^context>
  fun listed name =
    map (fn entry =>
        Pretty.string_of
          (Micro_Rust_Notation_Print.pretty_entry listing_ctxt
            (Micro_Rust_Names.NFunction, name, entry)) |> plain)
      (entries listing_ctxt name)
  val _ = require "listing tags"
    (listed "Counter::get" = ["Counter::get \<longmapsto> counter_get  (function, generated)"] andalso
      listed "get" = ["get \<longmapsto> counter_get  (function, generated, method-only)"])
in end
\<close>

chapter\<open> Impl block resolution \<close>

section\<open> Path selection \<close>

text\<open>
\<open>Duo::sum\<close> has three impls in \<open>Parser_Impl_Examples\<close>. An unannotated path call is
rejected at the \<open>sum\<close> segment, listing every impl, whatever the argument and expected types; a
selection without a matching impl and a selection of the wrong arity are rejected; explicit call
notations under the key are excluded by a selection. Keys without impls keep their behavior.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun function body = quiet ("urust_fn " ^ cartouche (" " ^ body ^ " "))
  fun at_segment label expected text context needle =
    rejects_at label expected (range_within text context needle)
      (fn () => run_commands false label thy text)
  val ambiguous =
    "urust: multiple applicable items in scope: Duo::sum is defined in more than one impl; " ^
      "write `Duo::<\<dots>>::sum`"
  fun ambiguous_at label body =
    let
      val text = function body
      val message =
        expect_failure label [ambiguous] (fn () => run_commands false label thy text)
      val positions = message_positions message
      val impls = filter (fn pos => Position.file_of pos <> SOME label) positions
      (* The impl members in declaration order: owner identities are allocated in that order. *)
      val declared =
        Micro_Rust_Names.associated_functions \<^context> "Duo::sum"
        |> sort (int_ord o apply2 #identity) |> map (position_range o #pos)
    in
      require (label ^ ": ranges")
        (position_range (hd positions) = range_within text "Duo::sum" "sum" andalso
          length declared = 3 andalso map position_range impls = declared)
    end
  val _ = ambiguous_at "ambiguous-no-type"
    "fn SelectNone() { let pick = |value| { Duo::sum(value) }; () }"
  val _ = ambiguous_at "ambiguous-argument-type" "fn SelectArgument(d: Duo<u8>) -> u8 { Duo::sum(d) }"
  val _ = ambiguous_at "ambiguous-expected-type"
    "fn SelectExpected(d: \<tau>\<open>_\<close>) -> u8 { Duo::sum(d) }"
  val _ = ambiguous_at "ambiguous-generic-alias" "fn SelectAlias(d: Duo<u8>) -> u8 { AnyDuo::sum(d) }"
  val _ =
    at_segment "no-matching-impl" ["urust: no associated function sum in impls of Duo<u32>"]
      (function "fn SelectMissing(d: Duo<u32>) -> u32 { Duo::<u32>::sum(d) }") "::sum" "sum"
  val _ =
    at_segment "selection-arity" ["Rust type \"Duo\" has generic arities [2]"]
      (function "fn SelectArity(d: Duo<u8>) -> u8 { Duo::<u8, u8>::sum(d) }") "{ Duo" "Duo"
  val long_alias =
    quiet ("urust_type_alias " ^ cartouche " type LongDuo = Duo<u64>; " ^ "\n") ^
      function "fn SelectLong(d: Duo<u64>) -> u64 { LongDuo::sum(d) }"
  val _ =
    at_segment "alias-no-matching-impl" ["urust: no associated function sum in impls of LongDuo"]
      long_alias "LongDuo::sum" "sum"

  (* Explicit notations under keys with zero, one and three impls. *)
  val explicit =
    quiet
      ("urust_fn [register_notation = false] duo_other_sum " ^
         cartouche " fn other_sum(self: Duo<u8>) -> u8 { self.first } " ^ "\n" ^
       "micro_rust_notation (call) duo_other_sum (\"Duo::sum\")\n")
  val _ = expect_failure "explicit-three-impls-unannotated" [ambiguous]
    (fn () => run_commands false "explicit-three-impls-unannotated" thy
      (explicit ^ function "fn SelectExplicit(d: Duo<u8>) -> u8 { Duo::sum(d) }"))
  val selected =
    context_after "explicit-three-impls-selected" thy
      (explicit ^ function "fn SelectExplicitByte(d: Duo<u8>) -> u8 { Duo::<u8>::sum(d) }")
  fun calls ctxt name =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))) []
  val _ = require "a selection excludes explicit notations under the key"
    (member (op =) (calls selected "select_explicit_byte") \<^const_name>\<open>duo_byte_sum\<close> andalso
      not (exists (String.isSuffix "duo_other_sum") (calls selected "select_explicit_byte")))
  val replaced =
    context_after "explicit-same-backend-selected" thy
      (quiet "micro_rust_notation (call) duo_byte_sum (\"Duo::sum\")\n" ^
       function "fn SelectReplaced(d: Duo<u8>) -> u8 { Duo::<u8>::sum(d) }")
  val _ = require "a replaced path entry still counts for its impl"
    (member (op =) (calls replaced "select_replaced") \<^const_name>\<open>duo_byte_sum\<close>)
  val solo =
    context_after "explicit-one-impl" thy
      (quiet
        ("urust_fn [register_notation = false] solo_other " ^
           cartouche " fn other(self: Solo<u16>) -> u16 { self.inner } " ^ "\n" ^
         "micro_rust_notation (call) solo_other (\"Solo::only\")\n") ^
       function "fn SoloBoth(a: Solo<u8>, b: Solo<u16>) -> u16 { Solo::only(b) }")
  val _ = require "an explicit notation overloads the path of a key with one impl"
    (exists (String.isSuffix "solo_other") (calls solo "solo_both"))
  val none =
    context_after "explicit-no-impl" thy
      (quiet "micro_rust_notation (call) tally_new (\"Gadget::make\")\n" ^
       function "fn GadgetMake() -> Tally { Gadget::make() }")
  val _ = require "a key without impls dispatches as before"
    (member (op =) (calls none "gadget_make") \<^const_name>\<open>tally_new\<close>)
  val _ =
    at_segment "intermediate-without-impls"
      ["generic arguments on an intermediate path segment require an exact registration"]
      (quiet "micro_rust_notation (call) tally_new (\"Gadget::make\")\n" ^
       function "fn GadgetGeneric() -> Tally { Gadget::<u8>::make() }") "{ Gadget" "Gadget"
in end
\<close>

section\<open> Generic arguments of type heads \<close>

text\<open>
The instance that an alias, imported alias or \<open>Self\<close> head fixes types the constructors it
reaches, so each mismatch is rejected exactly as with the canonical path.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val clash = "Type unification failed"
  (* The clash is positioned where the canonical spelling reports it. Type-inference errors carry
     no position inside the elaborated term (its navigation payloads use the uRust position
     codec), so every spelling reports at the command keyword. *)
  fun mismatch label text =
    let val keyword = if String.isSubstring "urust_fn " text then "urust_fn" else "urust" in
      rejects_at label [clash] (range_within text (keyword ^ " ") keyword)
        (fn () => run_commands false label thy text)
    end
  fun function body = quiet ("urust_fn " ^ cartouche (" " ^ body ^ " "))
  fun member body = quiet ("urust " ^ command_source body)
  val _ = mismatch "canonical-variant"
    (function "fn CanonicalBad() -> Hold<u16> { Hold::<u8>::Holding(1_u16) }")
  val _ = mismatch "alias-variant-call"
    (function "fn AliasBad() -> Hold<u16> { ByteHold::Holding(1_u16) }")
  val _ = mismatch "alias-unit-variant"
    (function "fn AliasUnitBad() -> Hold<u16> { ByteHold::Empty }")
  val _ = mismatch "alias-variant-pattern"
    (function "fn AliasMatchBad(x: Hold<u16>) -> u8 { match x { ByteHold::Holding(_) => 0_u8, _ => 1_u8 } }")
  val _ = mismatch "alias-struct"
    (function "fn AliasStructBad() -> Parcel<u16> { ByteParcel { inner: 1_u16 } }")
  val _ = mismatch "alias-struct-pattern"
    (function "fn AliasStructMatchBad(p: Parcel<u16>) -> u16 { match p { ByteParcel { inner } => inner } }")
  val _ = mismatch "imported-alias-variant"
    (function "fn ImportedBad() -> Hold<u16> { use ByteHold as Held; Held::Holding(1_u16) }")
  val _ = mismatch "generic-alias-arguments"
    (function "fn GenericBad() -> Hold<u16> { AnyHold::<u8>::Holding(1_u16) }")
  val _ = mismatch "self-variant"
    (member "impl Hold<u8> {\n  fn self_bad() -> bool { let held = Self::Holding(1_u16); true }\n}")
  val _ = mismatch "self-struct-pattern"
    (member ("impl Parcel<u8> {\n  fn self_match_bad(self, other: Parcel<u16>) -> u16 {\n" ^
      "    match other { Self { inner } => inner }\n  }\n}"))
in end
\<close>

section\<open> Direct calls of methods \<close>

text\<open>
A key whose every entry is a method entry is unregistered for a direct call: the call reaches a
HOL constant of that name, if any, or is rejected, and either diagnostic names the method call
forms. An explicit bare registration restores direct calls. Method syntax does not reach an
associated function.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun function body = quiet ("urust_fn " ^ cartouche (" " ^ body ^ " "))
  fun at label expected text needle =
    rejects_at label expected (range_within text ("{ " ^ needle) needle)
      (fn () => run_commands false label thy text)
  val _ =
    at "method-direct"
      ["urust_expr: level_of is a method; call it as `x.level_of(..)` or `Light::level_of(x, ..)`"]
      (function "fn DirectMethod(l: Light) -> u32 { level_of(l) }") "level_of"
  val two_types =
    quiet ("urust " ^ command_source
      ("impl Tally {\n  fn twin_name(self) -> u32 { self.count }\n}\n" ^
       "impl Beacon {\n  fn twin_name(self) -> u32 { 0_u32 }\n}")) ^ "\n" ^
    function "fn DirectTwin(t: Tally) -> u32 { twin_name(t) }"
  val _ =
    at "method-direct-two-types"
      ["urust_expr: twin_name is a method; call it as `x.twin_name(..)` or " ^
         "`Beacon::twin_name(x, ..)` or `Tally::twin_name(x, ..)`"]
      two_types "twin_name"
  val hol_named =
    quiet ("urust " ^ command_source "impl Tally {\n  fn length(self) -> u32 { self.count }\n}") ^
      "\n" ^ function "fn DirectHol(t: Tally) -> u32 { length(t) }"
  val _ =
    at "method-direct-hol-constant"
      ["call head \"length\" has pure HOL type",
       "length is a method; call it as `x.length(..)` or `Tally::length(x, ..)`"]
      hol_named "length"
  (* A HOL constant whose result may be a function body is called, as for any unregistered name. *)
  val _ =
    expect_failure "method-direct-hol-polymorphic" ["Type unification failed"]
      (fn () => run_commands false "method-direct-hol-polymorphic" thy
        (function "fn DirectPlus(c: Counter) -> u32 { plus(c, 1_u32) }"))
  val _ =
    at "method-direct-turbofish"
      ["level_of is a method"] (function "fn DirectTurbofish(l: Light) -> u32 { level_of::<u8>(l) }")
      "level_of"
  val restored =
    context_after "explicit-bare-restores" thy
      (quiet "micro_rust_notation (call) light_level_of (\"level_of\")\n" ^
       function "fn DirectRestored(l: Light) -> u32 { level_of(l) }")
  val _ = require "an explicit bare registration restores the direct call"
    (member (op =)
      (Term.add_const_names
        (Thm.prop_of (Proof_Context.get_thm restored "direct_restored_def")) [])
      \<^const_name>\<open>light_level_of\<close>)
  val method_new = function "fn MethodNew(t: Tally) -> Tally { t.new() }"
  val _ =
    rejects_at "associated-method-syntax" ["unregistered method call head \"new\""]
      (range_within method_new "t.new" "new")
      (fn () => run_commands false "associated-method-syntax" thy method_new)
in end
\<close>

section\<open> Self heads outside impls \<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val outside = "urust: Self is only available inside an impl block"
  fun outside_at label body =
    let val text = quiet ("urust_fn " ^ cartouche (" " ^ body ^ " ")) in
      rejects_at label [outside] (range_of text "Self" 0)
        (fn () => run_commands false label thy text)
    end
  val _ = outside_at "self-call" "fn OutsideCall() -> Tally { Self::new() }"
  val _ = outside_at "self-variant-value" "fn OutsideVariant() -> Light { Self::Dark }"
  val _ = outside_at "self-variant-call" "fn OutsideVariantCall() -> Light { Self::Lit(1_u32) }"
  val _ = outside_at "self-unit-value" "fn OutsideUnit() -> Beacon { Self }"
  val _ = outside_at "self-tuple" "fn OutsideTuple() -> Twofold { Self(1_u32, 2_u32) }"
  val _ = outside_at "self-struct" "fn OutsideStruct() -> Tally { Self { count: 1_u32 } }"
  val _ = outside_at "self-variant-pattern"
    "fn OutsidePattern(l: Light) -> bool { match l { Self::Dark => true, _ => false } }"
  val _ = outside_at "self-tuple-pattern"
    "fn OutsideTuplePattern(t: Twofold) -> u32 { match t { Self(a, _) => a } }"
  val _ = outside_at "self-struct-pattern"
    "fn OutsideStructPattern(t: Tally) -> u32 { match t { Self { count } => count } }"
  val in_impl =
    quiet ("urust " ^ command_source "impl Tally {\n  fn generic_self() -> Self { Self::<u8>::new() }\n}")
  val _ =
    rejects_at "self-generic-arguments" ["urust: Self cannot take generic arguments"]
      (range_of in_impl "::<u8>" 0)
      (fn () => run_commands false "self-generic-arguments" thy in_impl)
in end
\<close>

section\<open> Imports of impl members \<close>

text\<open>
Associated functions are not importable, also when the impl follows the use item in the same
chunk; an explicit call notation under a path key stays importable, and method keys are no import
targets. Impl members contribute no import entities, so a chunk import never collides with them.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun import_rejects label key text =
    rejects_at label ["uRust import: associated function \"" ^ key ^ "\" cannot be imported"]
      (range_of text key 0) (fn () => run_commands false label thy text)
  val _ = import_rejects "import-method" "Tally::read" (quiet (chunk "use Tally::read;\nfn UseRead() {}"))
  val _ = import_rejects "import-associated" "Tally::new" (quiet (chunk "use Tally::new as make;"))
  val _ =
    import_rejects "import-block" "Tally::new"
      (quiet ("urust_fn " ^ cartouche " fn BlockImport() -> Tally { use Tally::new; new() } "))
  val _ =
    import_rejects "import-later-member" "Later::go"
      (quiet (chunk "use Later::go;\nstruct Later;\nimpl Later {\n  fn go() -> u32 { 1_u32 }\n}"))
  val explicit =
    context_after "import-explicit-path" thy
      (quiet ("micro_rust_notation (call) tally_new (\"Tally::make_explicit\")\n" ^
        chunk "use Tally::make_explicit as make;\nfn UseExplicit() -> Tally { make() }"))
  val _ = require "an explicit path key stays importable"
    (member (op =)
      (Term.add_const_names (Thm.prop_of (Proof_Context.get_thm explicit "use_explicit_def")) [])
      \<^const_name>\<open>tally_new\<close>)
  val _ =
    expect_failure "import-method-key" ["unknown import target \"level_of\""]
      (fn () => run_commands false "import-method-key" thy (quiet (chunk "use level_of;")))
  val _ =
    context_after "import-no-collision" thy
      (quiet (chunk ("use use_increment as probe;\nstruct ProbeHost;\n" ^
        "impl ProbeHost {\n  fn probe(self) -> u32 { 1_u32 }\n}\n" ^
        "fn UseProbe(h: ProbeHost) -> u32 { h.probe() + probe(1_u32) }")))
in end
\<close>

section\<open> Locals and heads \<close>

text\<open>
Lexical locals never capture method names, qualified heads or \<open>Self\<close> heads (D162).
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val text =
    quiet
      (chunk
        ("fn LocalHeads(t: Tally, c: Counter) -> u32 {\n" ^
         "  let get = 1_u32;\n  let Tally = 2_u32;\n" ^
         "  c.get() + get + Tally::read(t) + Tally\n}\n" ^
         "impl Tally {\n  fn local_self(self) -> u32 {\n    let read = 3_u32;\n" ^
         "    Self::read(self) + read\n  }\n}"))
  val ctxt = context_after "locals-and-heads" thy text
  val consts =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt "local_heads_def")) []
  val self_consts =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt "tally_local_self_def")) []
  val _ = require "locals do not capture heads"
    (member (op =) consts \<^const_name>\<open>counter_get\<close> andalso
      member (op =) consts \<^const_name>\<open>tally_read\<close> andalso
      member (op =) self_consts \<^const_name>\<open>tally_read\<close>)
  (* Self is a path in every pattern position, never a binder: outside an impl it is rejected
     as Self outside an impl. *)
  val self_binder = "urust: Self is only available inside an impl block"
  fun binder_rejects label body =
    let val text = quiet ("urust_fn " ^ cartouche (" " ^ body ^ " ")) in
      rejects_at label [self_binder] (range_of text "Self" 0)
        (fn () => run_commands false label thy text)
    end
  val _ = binder_rejects "self-let-binder" "fn BindLet() -> u32 { let Self = 3_u32; 0_u32 }"
  val _ = binder_rejects "self-parameter-binder" "fn BindParameter(Self: u32) -> u32 { 0_u32 }"
  val _ = binder_rejects "self-closure-binder"
    "fn BindClosure() -> u32 { let f = |Self| { 0_u32 }; 0_u32 }"
  (* In a match pattern, Self is a path, never a binder. *)
  val match_text =
    quiet ("urust_fn " ^
      cartouche " fn BindMatch(x: \<tau>\<open>32 word option\<close>) -> u32 { match x { Some(Self) => 0_u32, None => 1_u32 } } ")
  val _ =
    rejects_at "self-match-path" ["urust: Self is only available inside an impl block"]
      (range_of match_text "Self" 0)
      (fn () => run_commands false "self-match-path" thy match_text)
in end
\<close>

section\<open> Markup of Self and type heads \<close>

text\<open>
A \<open>Self\<close> head keeps its token: it references the target type with the tooltip
\<open>Self = Target\<close>, and \<open>Self::f(..)\<close> navigates to the member. An alias head references the
alias, and an import head its import. A rejected path leaves no semantic report.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val text =
    quiet
      (chunk
        ("struct MarkTally { count: u32 }\n" ^
         "impl MarkTally {\n" ^
         "  fn count_of(self) -> u32 { self.count }\n" ^
         "  fn recount(self) -> u32 { Self::count_of(self) }\n" ^
         "}") ^ "\n" ^
       "urust_type_alias " ^ cartouche " type MarkAlias = MarkTally; " ^ "\n" ^
       chunk "fn MarkAliasCall(t: MarkTally) -> u32 { MarkAlias::count_of(t) }")
  val {result, reports, ...} = capture true "self-head-markup" \<^theory> text
  val ctxt = result_context result
  val notation = Micro_Rust_Names.notationN
  val mapping = "micro_rust_type_mapping"
  val member_ids = entity_ids_at (range_within text "fn count_of" "count_of") notation true reports
  val self_range = range_within text "Self::count_of" "Self"
  val call_range = range_within text "Self::count_of" "count_of"
  val target_ids = entity_ids_at (range_of text "MarkTally" 0) mapping true reports
  val _ = require "Self::f navigates to the member"
    (exists (member (op =) member_ids) (entity_ids_at call_range notation false reports))
  val _ = require "the Self head references the target with its tooltip"
    (not (null target_ids) andalso
      entity_ids_at self_range mapping false reports = target_ids andalso
      member (op =) (texts_at self_range reports) ("typing", "Self = MarkTally") andalso
      member (op =) (map #1 (texts_at self_range reports)) Markup.keyword3N)
  val alias_ids = entity_ids_at (range_within text "type MarkAlias" "MarkAlias") mapping true reports
  val alias_head = range_within text "MarkAlias::count_of" "MarkAlias"
  val _ = require "the alias head references the alias and the call the member"
    (not (null alias_ids) andalso
      exists (member (op =) alias_ids) (entity_ids_at alias_head mapping false reports) andalso
      exists (member (op =) member_ids)
        (entity_ids_at (range_within text "MarkAlias::count_of" "count_of") notation false reports))
  val _ = ignore ctxt

  (* An import head references its import; the use target of a replaced automatic entry
     navigates to the covering explicit registration. *)
  val import_text =
    quiet
      ("urust_fn " ^ cartouche " fn NavProbe() -> u32 { 1_u32 } " ^ "\n" ^
       "micro_rust_notation (call) nav_probe (\"NavProbe\")\n" ^
       chunk ("use NavProbe as probe;\nfn MarkImportHead(t: Tally) -> u32 {\n" ^
         "  use Tally as Counted;\n  Counted::read(t) + probe()\n}"))
  val {result = import_result, reports = import_reports, ...} =
    capture true "import-head-markup" \<^theory> import_text
  val import_ctxt = result_context import_result
  val head_range = range_within import_text "Counted::read" "Counted"
  val _ = require "an import head references its import"
    (member (op =) (entity_kinds_at head_range import_reports) "urust_import")
  val probe_entry = the_entry import_ctxt "probe" "NavProbe"
  val (target_serial, _) = Micro_Rust_Names.navigation_target import_ctxt probe_entry
  val _ = require "a replaced use target navigates to the explicit registration"
    (target_serial <> #serial probe_entry andalso
      member (op =)
        (entity_ids_at (range_within import_text "use NavProbe" "NavProbe") notation false
          import_reports)
        (string_of_int target_serial))

  val rejected = quiet ("urust_fn " ^ cartouche " fn MarkRejected(d: Duo<u8>) -> u8 { Duo::sum(d) } ")
  val {result = rejected_result, reports = rejected_reports, ...} =
    capture true "rejected-path-markup" \<^theory> rejected
  val _ = failure_message "rejected path" ["multiple applicable items"] rejected_result
  val command_start = #1 (range_of rejected "urust_fn" 0)
  val _ = require "a rejected path leaves no semantic report"
    (null (filter (fn event => #1 (report_range event) >= command_start)
      (semantic_entities rejected_reports)))
in end
\<close>

chapter\<open> Integration review rows \<close>

section\<open> Default HOL names across instances \<close>

text\<open>
The default HOL name of a member does not distinguish impls of different instances of one type.
The clash is reported at the second member, before it is declared, with the earlier member and the
remedy.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val text =
    quiet (chunk
      ("struct ClashTwin<T> { left: T }\n" ^
       "impl ClashTwin<u8> {\n  fn width(self) -> u8 { self.left }\n}\n" ^
       "impl ClashTwin<u16> {\n  fn width(self) -> u16 { self.left }\n}"))
  val message =
    expect_failure "default-name-clash"
      ["urust: the default HOL name \"clash_twin_width\" of member \"width\"",
       "is already used by another impl of \"ClashTwin\"", "name = \"...\""]
      (fn () => run_commands false "default-name-clash" thy text)
  val positions = message_positions message
  val _ = require "the clash names the second member, then the first"
    (map position_range (take 2 positions) =
      [range_within text "fn width(self) -> u16" "width",
       range_within text "fn width(self) -> u8" "width"])

  (* A duplicate member is Rust's overlap error (E0592), not a naming clash. *)
  val overlap = "urust: associated function \"ClashOnce::d\" is defined in more than one impl"
  fun duplicate label body =
    let val dup_text = quiet (chunk ("struct ClashOnce<T> { left: T }\n" ^ body)) in
      rejects_at label [overlap] (range_within dup_text "fn d" "d")
        (fn () => run_commands false label thy dup_text)
    end
  val _ = duplicate "duplicate-within-impl-default"
    "impl ClashOnce<u8> {\n  fn d(self) -> u8 { self.left }\n  fn d(self) -> u8 { 0_u8 }\n}"
  val _ = duplicate "duplicate-same-instance-default"
    ("impl ClashOnce<u8> {\n  fn d(self) -> u8 { self.left }\n}\n" ^
     "impl ClashOnce<u8> {\n  fn d(self) -> u8 { 0_u8 }\n}")

  (* The wording names another impl only when the constant is another impl's member. *)
  val earlier =
    quiet
      ("definition clash_twin_size :: " ^ cartouche " nat " ^ " where " ^
         cartouche " clash_twin_size = 0 " ^ "\n" ^
       chunk
        ("struct ClashTwin<T> { left: T }\n" ^
         "impl ClashTwin<u8> {\n  " ^ annotation "name = \"clash_size_byte\"" ^
         "\n  fn size(self) -> u8 { self.left }\n}\n" ^
         "impl ClashTwin<u16> {\n  fn size(self) -> u16 { self.left }\n}"))
  val _ =
    expect_failure "default-name-earlier-definition"
      ["of member \"size\"", "is already used by an earlier declaration"]
      (fn () => run_commands false "default-name-earlier-definition" thy earlier)
in end
\<close>

section\<open> Impls with trait headers outside chunks \<close>

text\<open>
Outside chunk input, an impl whose header continues with \<open>for\<close> or \<open>where\<close> gets the
rejection of every impl outside a chunk, at its keyword: the item-mode message for an item, the
item-in-expression message inside a body. Chunk input keeps the header rejection at the
\<open>for\<close> or \<open>where\<close>.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun at label expected text needle occurrence =
    rejects_at label expected (range_of text needle occurrence)
      (fn () => run_commands false label thy text)
  val item_mode = "urust: impl blocks are chunk members"
  val in_body = "uRust impl declarations are not expressions; use a urust chunk"
  val _ = at "trait-header-item-mode" [item_mode]
    (quiet ("urust_fn " ^ cartouche " impl Clone for Tally {} ")) "impl" 0
  val _ = at "where-header-item-mode" [item_mode]
    (quiet ("urust_datatype " ^ cartouche " impl Tally where Tally: Copy {} ")) "impl" 0
  val _ = at "trait-header-in-body" [in_body]
    (quiet ("urust_fn " ^ cartouche " fn TraitInBody() -> u32 { impl Clone for Tally {}; 0_u32 } "))
    "impl" 0
  val _ = at "trait-header-in-expression" [in_body]
    (quiet ("urust_expr trait_in_expression " ^ cartouche " impl Clone for Tally {} ")) "impl" 0
  val _ = at "trait-header-chunk" ["is not supported in impl headers"]
    (quiet (chunk "impl Clone for Tally {}")) "for" 0
  val _ = at "unsafe-header-chunk" ["`unsafe impl`", "is not supported in impl headers"]
    (quiet (chunk "unsafe impl Tally {}")) "unsafe" 0
  (* The placement rule decides every header rejection: only the top level of chunk input admits
     an impl item, so only there do the header messages apply. *)
  val _ = at "unsafe-trait-item-mode" [item_mode]
    (quiet ("urust_fn " ^ cartouche " unsafe impl Clone for Tally {} ")) "impl" 0
  val _ = at "unsafe-item-mode" [item_mode]
    (quiet ("urust_fn " ^ cartouche " unsafe impl Tally {} ")) "impl" 0
  (* Item input holds one item: an impl after it, outside any body, is a misplaced item. *)
  val _ = at "trait-header-after-item" [item_mode]
    (quiet ("urust_fn " ^ cartouche " fn TraitAfter() {} impl Clone for Tally {} ")) "impl" 0
  val _ = at "generic-header-item-mode" [item_mode]
    (quiet ("urust_fn " ^ cartouche " impl<T> Duo<T> {} ")) "impl" 0
  val _ = at "generic-header-in-body" [in_body]
    (quiet ("urust_fn " ^ cartouche " fn GenericInBody() -> u32 { impl<T> Duo<T> {}; 0_u32 } "))
    "impl" 0
  val _ = at "negative-header-in-body" [in_body]
    (quiet ("urust_fn " ^
      cartouche " fn NegativeInBody() -> u32 { impl !Clone for Tally {}; 0_u32 } "))
    "impl" 0
  val _ = at "unsafe-in-body" [in_body]
    (quiet ("urust_fn " ^ cartouche " fn UnsafeInBody() -> u32 { unsafe impl Tally {}; 0_u32 } "))
    "impl" 0
  val _ = at "trait-header-chunk-body" [in_body]
    (quiet (chunk "fn TraitInChunkBody() -> u32 { impl Clone for Tally {}; 0_u32 }")) "impl" 0
  val _ = at "generic-header-chunk-body" [in_body]
    (quiet (chunk "fn GenericInChunkBody() -> u32 { impl<T> Duo<T> {}; 0_u32 }")) "impl" 0
  (* Impl braces hold members: a nested impl is a non-fn member, rejected at its first token,
     whatever its header. *)
  val member = "urust: only fn items are supported in impl blocks"
  fun nested label header needle =
    at label [member] (quiet (chunk ("impl Tally {\n  " ^ header ^ " {}\n}"))) needle 1
  val _ = nested "nested-plain" "impl Gauge" "impl"
  val _ = nested "nested-trait" "impl Clone for Tally" "impl"
  val _ = nested "nested-where" "impl Tally where Tally: Copy" "impl"
  val _ = nested "nested-generic" "impl<U> Duo<U>" "impl"
  val _ = nested "nested-negative" "impl !Clone for Tally" "impl"
  val _ =
    at "nested-unsafe" [member] (quiet (chunk "impl Tally {\n  unsafe impl Gauge {}\n}")) "unsafe" 0
  val _ =
    at "nested-unsafe-trait" [member]
      (quiet (chunk "impl Tally {\n  unsafe impl Clone for Gauge {}\n}")) "unsafe" 0
  (* Outside chunk input, the enclosing impl is the misplaced item. *)
  val _ = at "nested-trait-item-mode" [item_mode]
    (quiet ("urust_fn " ^ cartouche " impl Tally { impl Clone for Tally {} } ")) "impl" 0
in end
\<close>

section\<open> Receiver binding markup \<close>

text\<open>
A receiver shorthand binds \<open>self\<close> like a typed \<open>self: T\<close> parameter: its token carries the
binding's definition, and every use in the body references it.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val text =
    quiet (chunk
      ("struct MarkReceiver { count: u32 }\n" ^
       "impl MarkReceiver {\n" ^
       "  fn by_shorthand(self) -> u32 { self.count }\n" ^
       "  fn by_reference(&mut self) -> u32 { 0_u32 }\n" ^
       "  fn by_typed(self: Self) -> u32 { self.count }\n" ^
       "}"))
  val {result, reports, ...} = capture true "receiver-markup" \<^theory> text
  val _ = result_context result
  val local_kind = "urust_var"
  fun binding_at context = entity_ids_at (range_within text context "self") local_kind true reports
  fun use_at context = entity_ids_at (range_within text context "self") local_kind false reports
  val shorthand = binding_at "by_shorthand(self"
  val typed = binding_at "by_typed(self"
  val _ = require "a shorthand receiver defines its binding"
    (length shorthand = 1 andalso length typed = 1 andalso
      length (binding_at "(&mut self") = 1)
  val _ = require "receiver uses reference their binding"
    (use_at "u32 { self.count }\n  fn by_reference" = shorthand andalso
      use_at "u32 { self.count }\n}" = typed)
  val _ = require "the shorthand and typed receivers carry the same roles"
    (sort_distinct string_ord
        (map #1 (reports_at (range_within text "by_shorthand(self" "self") reports)) =
      sort_distinct string_ord
        (map #1 (reports_at (range_within text "by_typed(self" "self") reports)))
in end
\<close>

section\<open> Self patterns \<close>

text\<open>
\<open>Self\<close> in a pattern is a path. Inside an impl of a unit struct it matches the unit value in
\<open>let\<close>, parameters and closure formals; inside an impl of another type it gets the
path-pattern errors.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val ctxt =
    context_after "self-unit-patterns" thy
      (quiet (chunk
        ("impl Beacon {\n" ^
         "  fn let_self(self) -> bool { let Self = self; true }\n" ^
         "  fn parameter_self(Self: Beacon) -> bool { true }\n" ^
         "  fn closure_self(self) -> bool { let check = |Self| { true }; check(self) }\n" ^
         "}\n" ^
         "fn UnitLet(b: Beacon) -> bool { let Beacon = b; true }")))
  val _ = require "unit Self patterns declare"
    (forall (fn name => fact_declared ctxt (name ^ "_def"))
      ["beacon_let_self", "beacon_parameter_self", "beacon_closure_self", "unit_let"])
  val arity = "constructor \"Self\" expects 1 pattern argument(s), but got 0"
  val tally_let = quiet (chunk "impl Tally {\n  fn bad(self) -> bool { let Self = self; true }\n}")
  val _ = rejects_at "self-let-named-struct" [arity] (range_within tally_let "let Self" "Self")
    (fn () => run_commands false "self-let-named-struct" thy tally_let)
  val tally_parameter = quiet (chunk "impl Tally {\n  fn bad(Self: Tally) -> bool { true }\n}")
  val _ = rejects_at "self-parameter-named-struct" [arity]
    (range_within tally_parameter "(Self" "Self")
    (fn () => run_commands false "self-parameter-named-struct" thy tally_parameter)
  val mismatch = quiet (chunk "impl Beacon {\n  fn bad(Self: u32) -> bool { true }\n}")
  val _ = rejects_at "self-parameter-mismatch" ["mismatched types: the pattern Self has type"]
    (range_within mismatch "(Self" "Self")
    (fn () => run_commands false "self-parameter-mismatch" thy mismatch)
in end
\<close>

section\<open> Overlap of unregistered members \<close>

text\<open>
Overlap (Rust E0592) is a property of the impl: a member with \<open>register_notation = false\<close>
still owns its associated path, and a checked-only \<open>name = _\<close> member is checked against
earlier members, so duplicates are rejected in either order.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val overlap = "urust: associated function \"OptOut::d\" is defined in more than one impl"
  fun duplicate label body =
    let val text = quiet (chunk ("struct OptOut { level: u32 }\n" ^ body)) in
      rejects_at label [overlap] (range_within text "fn d" "d")
        (fn () => run_commands false label thy text)
    end
  fun member options = "  " ^ annotation options ^ "\n"
  val _ = duplicate "unregistered-second"
    ("impl OptOut {\n  fn d(self) -> u32 { 0_u32 }\n" ^
     member "register_notation = false, name = \"opt_out_d2\"" ^
     "  fn d(self) -> u32 { 1_u32 }\n}")
  val _ = duplicate "unregistered-first"
    ("impl OptOut {\n" ^ member "register_notation = false" ^ "  fn d(self) -> u32 { 0_u32 }\n}\n" ^
     "impl OptOut {\n" ^ member "name = \"opt_out_d2\"" ^ "  fn d(self) -> u32 { 1_u32 }\n}")
  val _ = duplicate "checked-only-second"
    ("impl OptOut {\n  fn d(self) -> u32 { 0_u32 }\n" ^ member "name = _" ^
     "  fn d(self) -> u32 { 1_u32 }\n}")
  val _ = duplicate "checked-only-first"
    ("impl OptOut {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 0_u32 }\n" ^
     "  fn d(self) -> u32 { 1_u32 }\n}")
  (* Checked-only owners are carried through every later impl of the chunk. *)
  val _ = duplicate "checked-only-first-across-impls"
    ("impl OptOut {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 0_u32 }\n}\n" ^
     "impl OptOut {\n  fn d(self) -> u32 { 1_u32 }\n}")
  val _ = duplicate "checked-only-second-across-impls"
    ("impl OptOut {\n  fn d(self) -> u32 { 0_u32 }\n}\n" ^
     "impl OptOut {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 1_u32 }\n}")
  val _ = duplicate "checked-only-both-across-impls"
    ("impl OptOut {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 0_u32 }\n}\n" ^
     "impl OptOut {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 1_u32 }\n}")
  (* Across commands a checked-only member leaves nothing behind, so a later registered duplicate
     is accepted; a registered member is still found by a later checked-only one. *)
  val _ =
    context_after "checked-only-then-registered-commands" thy
      (quiet (chunk ("struct OptLater { level: u32 }\nimpl OptLater {\n" ^ member "name = _" ^
         "  fn d(self) -> u32 { 0_u32 }\n}") ^ "\n" ^
       chunk "impl OptLater {\n  fn d(self) -> u32 { 1_u32 }\n}"))
  val registered_then_checked =
    quiet (chunk
        "struct OptEarlier { level: u32 }\nimpl OptEarlier {\n  fn d(self) -> u32 { 0_u32 }\n}" ^
      "\n" ^ chunk ("impl OptEarlier {\n" ^ member "name = _" ^ "  fn d(self) -> u32 { 1_u32 }\n}"))
  val _ =
    rejects_at "registered-then-checked-commands"
      ["urust: associated function \"OptEarlier::d\" is defined in more than one impl"]
      (range_within registered_then_checked "fn d" "d")
      (fn () => run_commands false "registered-then-checked-commands" thy registered_then_checked)
in end
\<close>

section\<open> Mutable Self patterns and items named Self \<close>

text\<open>
\<open>Self\<close> is a path pattern, so \<open>mut Self\<close> has no binder to make mutable; and
\<open>Self\<close> is a keyword, so no function, member, type or variant is named \<open>Self\<close>.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun rejects label expected body (context, needle) =
    let val text = quiet body in
      rejects_at label expected (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  val mutable = "urust: Self is a path pattern and cannot be a mutable binding"
  val _ = rejects "mut-self-parameter" [mutable]
    (chunk "impl Beacon {\n  fn mutable_parameter(mut Self: Beacon) -> bool { true }\n}")
    ("mut Self", "Self")
  val _ = rejects "mut-self-let" [mutable]
    (chunk "impl Beacon {\n  fn mutable_let(self) -> bool { let mut Self = self; true }\n}")
    ("mut Self", "Self")
  (* Closure formals are identifiers on this line, so `mut` there is a syntax error. *)
  val _ = rejects "mut-self-closure" ["syntax error"]
    (chunk
      ("impl Beacon {\n  fn mutable_closure(self) -> bool {\n" ^
       "    let f = |mut Self| { true }; f(self)\n  }\n}"))
    ("|mut", "|")
  val function = "urust: Self is a keyword and cannot name a function"
  val _ = rejects "self-free-function" [function]
    ("urust_fn " ^ cartouche " fn Self() -> u32 { 0_u32 } ") ("fn Self", "Self")
  val _ = rejects "self-chunk-function" [function] (chunk "fn Self() -> u32 { 0_u32 }")
    ("fn Self", "Self")
  val _ = rejects "self-member" [function]
    (chunk "impl Tally {\n  fn Self(self) -> u32 { 0_u32 }\n}") ("fn Self", "Self")
  (* One keyword rule (URust_AST.reject_keyword_name) at every name-introducing position, for
     `Self` and `self` alike. *)
  val datatype_name = "urust_datatype: Self is a keyword and cannot name a type"
  val _ = rejects "self-struct" [datatype_name] ("urust_datatype " ^ cartouche " struct Self; ")
    ("struct Self", "Self")
  val _ = rejects "self-enum" [datatype_name] (chunk "enum Self { Only }") ("enum Self", "Self")
  val _ = rejects "self-variant" ["urust_datatype: Self is a keyword and cannot name a variant"]
    (chunk "enum SelfVariant { First, Self }") (", Self", "Self")
  val field = "urust_datatype: Self is a keyword and cannot name a field"
  val _ = rejects "self-struct-field" [field]
    ("urust_datatype " ^ cartouche " struct SelfField { Self: u32 } ") ("{ Self", "Self")
  val _ = rejects "self-variant-field" [field]
    (chunk "enum SelfVariantField { First { Self: u32 }, Second }") ("{ Self", "Self")
  val _ = rejects "self-type-parameter"
    ["urust_datatype: Self is a keyword and cannot name a type parameter"]
    ("urust_datatype " ^ cartouche " struct SelfParameter<Self> { level: u32 } ") ("<Self", "Self")
  val _ = rejects "self-const-parameter"
    ["urust_datatype: Self is a keyword and cannot name a const parameter"]
    ("urust_datatype " ^ cartouche " struct SelfLength<const Self: usize> { level: u32 } ")
    ("const Self", "Self")
  val _ = rejects "self-type-alias" ["urust_type_alias: Self is a keyword and cannot name a type"]
    ("urust_type_alias " ^ cartouche " type Self = u8; ") ("type Self", "Self")
  val _ = rejects "self-alias-parameter"
    ["urust_type_alias: Self is a keyword and cannot name a type parameter"]
    ("urust_type_alias " ^ cartouche " type SelfAlias<Self> = u8; ") ("<Self", "Self")
  (* Lowercase self, accepted as an item name at the base, is rejected too, as in Rust; the
     receiver self remains a parameter form. *)
  fun lower label what body (context, needle) =
    rejects label ["self is a keyword and cannot name " ^ what] body (context, needle)
  val _ = lower "lower-self-function" "a function"
    ("urust_fn " ^ cartouche " fn self() -> u32 { 0_u32 } ")
    ("fn self", "self")
  val _ = lower "lower-self-member" "a function"
    (chunk "impl Tally {\n  fn self() -> u32 { 0_u32 }\n}") ("fn self", "self")
  val _ = lower "lower-self-struct" "a type" ("urust_datatype " ^ cartouche " struct self; ")
    ("struct self", "self")
  val _ = lower "lower-self-variant" "a variant" (chunk "enum LowerVariant { First, self }")
    (", self", "self")
  val _ = lower "lower-self-field" "a field"
    ("urust_datatype " ^ cartouche " struct LowerField { self: u32 } ") ("{ self", "self")
  val _ = lower "lower-self-alias" "a type" ("urust_type_alias " ^ cartouche " type self = u8; ")
    ("type self", "self")
  (* Every member owns its associated path, so importing it is the associated-function rejection
     also for unregistered and checked-only members. *)
  fun import_rejects label options key =
    rejects label ["uRust import: associated function \"Tally::" ^ key ^ "\" cannot be imported"]
      (chunk ("use Tally::" ^ key ^ ";\nimpl Tally {\n  " ^ annotation options ^ "\n  fn " ^ key ^
        "() -> u32 { 0_u32 }\n}"))
      ("use Tally::" ^ key, "Tally::" ^ key)
  val _ = import_rejects "use-checked-only-later" "name = _" "checked_later"
  val _ = import_rejects "use-unregistered-later" "register_notation = false" "unregistered_later"
in end
\<close>

section\<open> Self and impl are reserved \<close>

text\<open>
\<open>Self\<close> is reserved for impl blocks, so no registration key may contain it, and \<open>impl\<close> is
a reserved word that cannot name a binding, function or field (each a syntax error, positioned by
the parser's error correction).
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val reserved = "Self is reserved for impl blocks and cannot be a key segment"
  fun rejects label expected body (context, needle) =
    let val text = quiet body in
      rejects_at label expected (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  val _ = rejects "self-type-key" [reserved] ("urust_type \"Self\" = " ^ cartouche " nat ")
    ("\"Self\"", "Self")
  val _ = rejects "self-qualified-type-key" [reserved]
    ("urust_type \"demo::Self<'t>\" = " ^ cartouche " 't list ")
    ("demo::Self<'t>", "demo::Self<'t>")
  val _ = rejects "self-call-key" [reserved] "micro_rust_notation (call) tally_new (\"Self::make\")"
    ("(\"Self::make\")", "(")
  val _ = rejects "self-urust-notation-key" [reserved]
    "urust_notation (call) tally_new (\"Self::make\")" ("\"Self::make\"", "\"Self::make\"")
  (* Lowercase self is reserved in keys too; a bare literal key self stays an ordinary HOL value
     (Parser_Function_ML_Tests). *)
  val lower = "self is reserved for module paths and cannot be a key segment"
  val _ = rejects "lower-self-type-key" [lower] ("urust_type \"self\" = " ^ cartouche " nat ")
    ("\"self\"", "self")
  val _ = rejects "lower-self-qualified-type-key" [lower]
    ("urust_type \"cc::self\" = " ^ cartouche " nat ") ("cc::self", "cc::self")
  val _ = rejects "lower-self-call-key" [lower]
    "micro_rust_notation (call) tally_new (\"Tally::self\")" ("(\"Tally::self\")", "(")
  val _ = rejects "lower-self-urust-notation-key" [lower]
    "urust_notation (call) tally_new (\"Tally::self\")" ("\"Tally::self\"", "\"Tally::self\"")
  (* With no self key, `impl self` has no target to resolve. *)
  val _ = rejects "impl-lower-self" ["urust: unknown impl target type \"self\""]
    (chunk "impl self {\n  fn f() -> u32 { 0_u32 }\n}") ("impl self", "self")
  val _ =
    context_after "bare-self-literal-key" thy
      (quiet ("definition bare_self_value :: " ^ cartouche " bool " ^ " where " ^
         cartouche " bare_self_value = True " ^ "\n" ^
       "micro_rust_notation (literal) bare_self_value (\"self\")"))
  val _ = rejects "self-alias-path" ["invalid alias path \"Self::Width\"", reserved]
    ("urust_type_alias \"Self::Width\" " ^ cartouche " type Width = u8; ")
    ("Self::Width", "Self::Width")
  val _ = rejects "impl-let" ["syntax error"]
    ("urust_fn " ^ cartouche " fn ImplLet() -> u32 { let impl = 1_u32; impl } ") ("let impl", "let")
  val _ = rejects "impl-function" ["syntax error"]
    ("urust_fn " ^ cartouche " fn impl() -> u32 { 0_u32 } ") ("fn impl", "impl")
  val _ = rejects "impl-field" ["syntax error"]
    ("urust_datatype " ^ cartouche " struct ImplField { impl: u32 } ") ("{ impl", "impl")
in end
\<close>

section\<open> Keyword segments in paths and generated keys \<close>

text\<open>
\<open>Self\<close> and \<open>self\<close> may only start a path (Rust E0433), in every path role, so no key with
such a later segment is reachable; and the \<open>simple_word_enum\<close> registration path applies the
shared key check to its \<open>urust_name:\<close> and every key it derives.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun rejects label expected body (context, needle) =
    let val text = quiet body in
      rejects_at label expected (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  fun start keyword = "`" ^ keyword ^ "` in paths can only be used in start position"
  val _ = rejects "late-self-value" [start "Self"]
    (chunk "impl Tally {\n  fn late() -> u32 { Self::Self::LIMIT }\n}") ("::Self::LIMIT", "Self")
  val _ = rejects "late-self-call" [start "Self"]
    ("urust_fn " ^ cartouche " fn LateCall() -> Tally { Tally::Self() } ") ("::Self", "Self")
  val _ = rejects "late-self-pattern" [start "Self"]
    (chunk ("impl Light {\n  fn late(self) -> bool {\n" ^
      "    match self { Self::Self => true, _ => false }\n  }\n}"))
    ("::Self =>", "Self")
  val _ = rejects "late-self-type" [start "Self"]
    ("urust_fn " ^ cartouche " fn LateType(t: Tally::Self) -> u32 { 0_u32 } ") ("::Self", "Self")
  val _ = rejects "late-lower-self-call" [start "self"]
    ("urust_fn " ^ cartouche " fn LateLower() -> Tally { Tally::self() } ") ("::self", "self")
  val reserved = "Self is reserved for impl blocks and cannot be a key segment"
  val lower = "self is reserved for module paths and cannot be a key segment"
  (* Simple_Word_Enum carries the urust_name as a bare string, so its errors sit at the command. *)
  fun word_enum label expected source =
    rejects label expected source ("simple_word_enum (8)", "simple_word_enum")
  val _ = word_enum "word-enum-self-name" [reserved]
    "simple_word_enum (8) we_self urust_name: \"Self\" = WSA = 1 | WSB = 2"
  val _ = word_enum "word-enum-lower-self-name" [lower]
    "simple_word_enum (8) we_lower urust_name: \"self\" = WLA = 1 | WLB = 2"
  val _ = word_enum "word-enum-qualified-self-name" [reserved]
    "simple_word_enum (8) we_qualified urust_name: \"WeT::Self\" = WQA = 1 | WQB = 2"
  (* A variant key is rejected at the variant's binding. *)
  val _ = rejects "word-enum-self-variant" [reserved]
    "simple_word_enum (8) we_variant urust_name: \"WeVariant\" = Self = 1 | WVB = 2"
    ("= Self", "Self")
  val _ = rejects "word-enum-lower-self-variant" [lower]
    "simple_word_enum (8) we_lower_variant urust_name: \"WeLowerVariant\" = self = 1 | WLVB = 2"
    ("= self", "self")
  val _ =
    rejects "call-bare-self-key" [lower] "micro_rust_notation (call) tally_new (\"self\")"
      ("(\"self\")", "(")
in end
\<close>

section\<open> Macro paths and while let on sole constructors \<close>

text\<open>
A macro path is a path role too: a later \<open>Self\<close> or \<open>self\<close> is rejected, and a leading
\<open>Self\<close> is substituted inside an impl and rejected outside one. The keys below exist only
through the ML API, since every registration command rejects them; none is reachable. A nullary
sole constructor is irrefutable only at \<open>let\<close>/\<open>for\<close> binding sites; \<open>while let\<close> keeps the
base case compilation.
\<close>

declaration \<open>
fn _ =>
  fold (fn key =>
      Micro_Rust_Names.register Micro_Rust_Names.NFunction key \<^term>\<open>tally_new\<close> Position.none)
    ["Tally::Self!", "Tally::self!", "Tally::Self::probe!", "Self::probe!", "Tally::probe!",
     "Tally!"]
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun rejects label expected body (context, needle) =
    let val text = quiet body in
      rejects_at label expected (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  fun start keyword = "`" ^ keyword ^ "` in paths can only be used in start position"
  fun function body = "urust_fn " ^ cartouche (" " ^ body ^ " ")
  val _ = rejects "late-self-macro" [start "Self"]
    (function "fn LateMacro() -> Tally { Tally::Self!() }") ("::Self!", "Self")
  val _ = rejects "late-lower-self-macro" [start "self"]
    (function "fn LateLowerMacro() -> Tally { Tally::self!() }") ("::self!", "self")
  val _ = rejects "late-self-macro-segment" [start "Self"]
    (function "fn LateMacroSegment() -> Tally { Tally::Self::probe!() }") ("::Self::", "Self")
  val _ = rejects "Self-head-macro-outside" ["Self is only available inside an impl block"]
    (function "fn OutsideMacro() -> Tally { Self::probe!() }") ("{ Self", "Self")
  fun calls ctxt name =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))) []
  (* Inside an impl the head is substituted, so Self::probe! is Tally::probe!, never the key
     Self::probe!. *)
  val inside =
    context_after "Self-head-macro-impl" thy
      (quiet (chunk "impl Tally {\n  fn via_probe() -> Tally { Self::probe!() }\n}"))
  val _ = require "a Self macro head names the impl's own path"
    (member (op =) (calls inside "tally_via_probe") \<^const_name>\<open>tally_new\<close>)
  (* The hint names the substituted key, the one a declaration could add. *)
  val _ = rejects "Self-head-macro-impl-unregistered"
    ["qualified path \"Tally::absent!\" requires an exact micro_rust_notation (call) declaration"]
    (chunk "impl Tally {\n  fn via_absent() -> Tally { Self::absent!() }\n}")
    ("Self::absent!", "Self::absent!")
  (* Self alone names a type, never a macro, even with a key named after the target. *)
  val _ = rejects "Self-bang-impl" ["cannot find macro `Self`: Self names a type, not a macro"]
    (chunk "impl Tally {\n  fn bang() -> Tally { Self!() }\n}") ("{ Self!", "Self")
  val markup_text =
    quiet (chunk "impl Tally {\n  fn marked_probe() -> Tally { Self::probe!() }\n}")
  val {reports, ...} = capture true "Self-head-macro-markup" thy markup_text
  val macro_self = range_within markup_text "Self::probe!" "Self"
  val _ = require "a Self macro head has the Self markup of every path role"
    (member (op =) (texts_at macro_self reports) ("typing", "Self = Tally") andalso
      member (op =) (map #1 (texts_at macro_self reports)) Markup.keyword3N)

  (* The base lowering of an exhaustive while let on a nullary sole constructor: the case
     combinator of the constructor's type applied to the matched value. *)
  fun while_let_body ctxt name =
    (case Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def")) of
       _ $ _ $ (Const (\<^const_name>\<open>bounded_while\<close>, _) $ _ $
           (Const (\<^const_name>\<open>Core_Expression.bind\<close>, _) $ _ $ Abs (_, _, body)) $ _) =>
         SOME body
     | _ => NONE)
  fun case_on_bound case_name (Const (name, _) $ _ $ Bound 0) = name = case_name
    | case_on_bound _ _ = false
  val tnil =
    context_after "while-let-sole-constructor" thy
      (quiet ("urust_expr while_let_sole_tnil " ^
        cartouche (" #[fuel(\<epsilon>" ^ cartouche "1 :: nat" ^ ")] while let TNil = TNil { () } ")))
  val _ = require "while let on a nullary sole constructor keeps the case compilation"
    (case while_let_body tnil "while_let_sole_tnil" of
       SOME body => case_on_bound \<^const_name>\<open>case_tnil\<close> body
     | NONE => false)
  (* Through a Self head (Parser_Impl_Examples) the total pattern keeps the case combinator and
     has no fallback clause, exactly as its written-path control. *)
  fun case_names ctxt name =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))) []
    |> filter (fn c => String.isSubstring ".case_" c orelse String.isSuffix ".case" c)
  val examples = \<^context>
  val _ =
    List.app (fn name =>
        require ("a total Self pattern keeps one case combinator: " ^ name)
          (length (case_names examples name) = 1))
      ["beacon_while_self", "beacon_if_self", "solitary_while_only", "sheath_while_inner",
       "pocket_if_fields"]
  (* matches! keeps the base false clause, so a total pattern is rejected as redundant, through
     Self exactly as written (base rows in Parser_Rejection_Examples). *)
  val redundant = "clauses are redundant"
  fun matches_rejects label body =
    ignore (expect_failure label [redundant] (fn () => run_commands false label thy (quiet body)))
  val _ = matches_rejects "matches-total-Self"
    (chunk "impl Beacon {\n  fn matches_self(self) -> bool { matches!(self, Self) }\n}")
  val _ = matches_rejects "matches-total-written"
    (chunk "fn MatchesBeacon(b: Beacon) -> bool { matches!(b, Beacon) }")
in end
\<close>

section\<open> Closure formals, prelude targets and datatype name options \<close>

text\<open>
Closure formals are patterns, so \<open>Self\<close> in them follows the pattern rules: rejected outside
impls, a path whose constructor must take no arguments, and refutable unless it is its family's
only constructor. A closure formal takes no \<open>mut\<close>, so \<open>mut Self\<close> cannot arise there. An
impl of a prelude mapping such as \<open>Option<u8>\<close> declares and registers its members like any
mapping target; the prelude variants have no path registration, so \<open>Self::Some\<close> does not
name one. The \<open>hol_names\<close> and \<open>hol_type_parameters\<close> keys are Rust names of the item, checked
against it, and their cartouche targets are HOL names, which introduce no Rust key.
\<close>

ML\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  fun rejects label expected body (context, needle) =
    let val text = quiet body in
      rejects_at label expected (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  val _ = rejects "closure-Self-outside" ["Self is only available inside an impl block"]
    (chunk "fn ClosureOutside(b: Beacon) -> bool { let check = |Self| { true }; check(b) }")
    ("|Self|", "Self")
  val _ = rejects "closure-Self-not-unit" ["constructor \"Self\" expects 1 pattern argument(s)"]
    (chunk "impl Tally {\n  fn closes_tally(self) -> bool { let check = |Self| { true }; check(self) }\n}")
    ("|Self|", "Self")
  val _ = rejects "closure-Self-refutable"
    ["unsupported or refutable pattern in a closure formal position"]
    (chunk "impl Light {\n  fn closes_dark(self) -> bool { let check = |Self::Dark| { true }; check(self) }\n}")
    ("|Self::Dark|", "Dark")
  fun calls ctxt name =
    Term.add_const_names (Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))) []
  val prelude =
    context_after "impl-prelude-option" thy
      (quiet (chunk ("impl Option<u8> {\n" ^
        "  fn first_or_zero(self) -> u8 { match self { Some(x) => x, None => 0_u8 } }\n}\n" ^
        "fn PreludePath() -> u8 { Option::first_or_zero(Some(1_u8)) }\n" ^
        "fn PreludeMethod(o: Option<u8>) -> u8 { o.first_or_zero() }")))
  val _ = require "an impl of a prelude mapping registers its members"
    (length (entries prelude "Option::first_or_zero") = 1 andalso
      exists (String.isSuffix ".option_first_or_zero") (calls prelude "prelude_path") andalso
      exists (String.isSuffix ".option_first_or_zero") (calls prelude "prelude_method"))
  val _ = rejects "impl-prelude-Self-variant"
    ["the Self path resolves to \"Option::Some\", which cannot be used as a call"]
    (chunk "impl Option<u8> {\n  fn some_one() -> Self { Self::Some(1_u8) }\n}") ("{ Self", "Self")
  fun datatype_command option source =
    "urust_datatype [" ^ option ^ "] " ^ cartouche (" " ^ source ^ " ")
  val _ = rejects "hol-names-Self-key" ["unknown rename key \"Self\""]
    (datatype_command ("hol_names = [\"Self\" \<rightarrow> " ^ cartouche "renamed" ^ "]")
      "enum NameKeyProbe { A, B }") ("\"Self\"", "Self")
  val _ = rejects "hol-type-parameters-Self-key" ["unknown parameter override \"Self\""]
    (datatype_command ("hol_type_parameters = [\"Self\" \<rightarrow> " ^ cartouche "'a" ^ "]")
      "struct ParameterKeyProbe<T> { v: T }") ("\"Self\"", "Self")
  val renamed =
    context_after "hol-names-keyword-target" thy
      (quiet (datatype_command ("hol_names = [\"A\" \<rightarrow> " ^ cartouche "Self" ^ "]")
        "enum NameTargetProbe { A, B }" ^ "\n" ^
       chunk "fn NameTargetUse() -> NameTargetProbe { NameTargetProbe::A }"))
  val _ = require "a keyword HOL target leaves the Rust path of its variant"
    (exists (String.isSuffix ".Self") (calls renamed "name_target_use") andalso
      null (entries renamed "NameTargetProbe::Self"))
in end
\<close>


section\<open> Declared signatures retain Rust keyword rules \<close>

text\<open>
A declared HOL type overrides Rust type interpretation while retaining the lexical rules for
\<open>Self\<close>, \<open>self\<close> and their path positions. These checks traverse retained function-pointer
and \<open>impl Trait\<close> types, nested arguments and associated-type binding values. Unknown Rust type
names still require no mappings under a declared type.
\<close>

ML_val \<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val declared = "nat \<Rightarrow> ('s, nat, 'a, 'i, 'o) function_body"
  (* Term reading freshens type variables; compare the complete quantified schemes. *)
  fun matches_declared ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val actual = Logic.varifyT_global (fastype_of (Syntax.read_term ctxt "declared_syntax"))
      val expected = Logic.varifyT_global (Syntax.read_typ ctxt declared)
    in Sign.typ_instance thy (actual, expected) andalso Sign.typ_instance thy (expected, actual) end
  fun command rust_signature =
    "urust_fn declared_syntax :: " ^ cartouche declared ^ " " ^
      command_source ("fn DeclaredSyntax" ^ rust_signature ^ " { \<llangle>x\<rrangle> }")
  fun rejects label expected rust_signature context needle =
    let val text = quiet (command rust_signature) in
      rejects_at label [expected] (range_within text context needle)
        (fn () => run_commands false label thy text)
    end
  val outside = "Self is only available inside an impl block"
  val _ = List.app (fn (label, rust_signature, context) =>
      rejects label outside rust_signature context "Self")
    [("declared-Self-parameter", "(x: Self) -> nat", "x: Self"),
     ("declared-Self-typed-receiver", "(self: Self) -> nat", "self: Self"),
     ("declared-Self-return", "(x: Unknown) -> Self", "-> Self"),
     ("declared-Self-tuple", "(x: (Unknown, Self)) -> nat", "Unknown, Self"),
     ("declared-Self-reference", "(x: &Self) -> nat", "&Self"),
     ("declared-Self-array", "(x: [Self; 4]) -> nat", "[Self"),
     ("declared-Self-nested", "(x: Unknown<Nested<Self>>) -> nat", "Nested<Self>"),
     ("declared-Self-function-parameter", "(x: fn(Self) -> Unknown) -> nat", "fn(Self)"),
     ("declared-Self-function-result", "(x: fn(Unknown) -> Self) -> nat", "-> Self"),
     ("declared-Self-associated-value", "(x: Cursor<Item = Self>) -> nat", "Item = Self"),
     ("declared-Self-impl-trait", "(x: impl Cursor<Item = Nested<Self>>) -> nat", "Nested<Self>")]
  val late = "in paths can only be used in start position"
  val _ = List.app (fn (label, rust_signature, context, needle) =>
      rejects label late rust_signature context needle)
    [("declared-late-Self", "(x: Unknown::Self) -> nat", "Unknown::Self", "Self"),
     ("declared-late-self", "(x: Unknown::self) -> nat", "Unknown::self", "self"),
     ("declared-late-function", "(x: fn(Unknown::Self) -> Unknown) -> nat", "Unknown::Self", "Self"),
     ("declared-late-associated", "(x: Cursor<Item = Unknown::self>) -> nat", "Unknown::self", "self")]
  val _ = rejects "declared-self-head" "self is reserved for module paths"
    "(x: self) -> nat" "x: self" "self"
  val _ = rejects "declared-self-associated-name" "self is reserved for module paths"
    "(x: Cursor<self = Unknown>) -> nat" "self = Unknown" "self"
  val _ = rejects "declared-Self-associated-name" "Self is reserved for impl blocks"
    "(x: Cursor<Self = Unknown>) -> nat" "Self = Unknown" "Self"
  val same_spelling =
    context_after "declared-impl-trait-return" thy
      (quiet (command "(x: u32) -> impl Counter"))
  val _ = require "the retained impl Trait spelling accepts an authoritative HOL signature"
    (matches_declared same_spelling)
  val accepted =
    context_after "declared-unknown-retained-types" thy
      (quiet (command "(x: fn(Unknown) -> Cursor<Item = Nested<Other>>) -> impl Iterator<Item = Other>"))
  val _ = require "declared retained unknown types still use the authoritative HOL signature"
    (matches_declared accepted)
in end
\<close>

section\<open> Erased impl identities and candidate isolation \<close>

ML_val\<open>
local
  open Impl_Declaration_Test
  structure M = URust_Type_Mappings
  structure N = Micro_Rust_Names
  structure D = Micro_Rust_Dispatch
  val ctxt = \<^context>
  val thy = \<^theory>
  val previous = N.dump ctxt
  val owners = N.associated_source_functions ctxt "ErasureOwner::erased_get"
  val _ = require "same-HOL concrete impl owners retain independent erased identities"
    (length owners = 2 andalso map #self_type owners = [\<^typ>\<open>nat\<close>, \<^typ>\<open>nat\<close>] andalso
     #source_identity (hd owners) <> #source_identity (List.last owners))
  fun key text =
    URust_Parser.parse_type_source ctxt (source "erasure-impl-identity" text)
    |> M.resolve_impl_target_identity ctxt |> #2 |> the |> M.source_identity_name
  val _ = require "impl aliases and expanded spelling share a source key"
    (key "ErasureAlpha" = key "ErasureOwner<Alpha,0>" andalso
     key "ErasureOwner<Alpha,0>" <> key "ErasureOwner<Beta,0>" andalso
     key "ErasureOwner<Alpha,0>" <> key "ErasureOwner<Alpha,1>")
  fun reject label expected item =
    let
      val text = quiet (chunk item)
      val observed = capture false label thy text
      val message = case #result observed of
          Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
        | _ => error (label ^ ": rejected impl fixture was accepted")
      val _ = require (label ^ ": wrong rejection") (String.isSubstring expected message)
      val command_start = #1 (range_of text "urust " 0)
      (* Lexical diagnostics and the failing member's genuine binder type are retained by the
         existing release-on-failure path. Candidate/item/backend navigation must stay absent. *)
      val _ = require (label ^ ": declaration leaked semantic navigation or ordinary output")
        (null (filter (fn event => #1 (report_range event) >= command_start)
           (semantic_entities (#reports observed))) andalso null (#output observed))
    in () end
  val _ = reject "erasure-method-identity" "receiver has no source identity"
    "fn ErasureMissingReceiver(value:ErasureAlpha)->ErasureAlpha{value.erased_get()}"
  val _ = reject "erasure-impl-inference" "explicit type arguments"
    "fn ErasureMissingOwner(value:ErasureAlpha)->ErasureAlpha{ErasureOwner::erased_get(value)}"
  val _ = reject "erasure-alias-conflict" "overlapping Self types"
    ("impl ErasureAlpha {\n" ^ annotation "name = \"erasure_duplicate_get\"" ^
      "\nfn erased_get(self)->Self{self}\n}")
  fun event_control method =
    let
      val calls = Unsynchronized.ref ([]: Position.T list)
      val start = start_position ("erasure-selected-" ^ method)
      fun reference pos =
        (calls := pos :: !calls;
         Micro_Rust_Semantic_Navigation.defer_report ctxt pos (Markup.entity "erasure_parameter" "T"))
      val parameter: M.generic_parameter =
        {rust = "T", pos = start, kind = URust_AST.Type_Parameter,
         hol = ("'erasure_observed", \<^sort>\<open>type\<close>), bounds = [],
         report_reference = reference}
      val scoped = ctxt |> M.with_generic_scope {parameters = [parameter]}
        |> M.with_source_only_parameters ["'erasure_observed"]
        |> Variable.declare_typ (TFree (#hol parameter))
      val body = Parser_Lex_Util.positioned_content_source ("value." ^ method ^ "::<T>(value)") start
      val ((_, events), markup) = Parser_Test_Reports.markup (fn () =>
        M.capture_generic_use_events scoped (fn observed =>
          Parser_Test_Elaboration.function observed
            {raw_type = ("nat => (unit,nat,unit,unit,unit) function_body", start),
             parameters = [("value", start)], parameters_pos = start, body = body}))
      val _ = require "unrelated retained candidate leaked witness demand or duplicated a callback"
        (#source_uses events = ["'erasure_observed"] andalso null (#witness_uses events) andalso
         length (!calls) = 1)
      val position = hd (!calls)
      fun at_source (_, props) =
        Properties.get props Markup.offsetN = Option.map string_of_int (Position.offset_of position)
      val authored = filter at_source markup
      val _ = require "selected source-only argument gains one navigation reference and no HOL typing"
        (length (filter (fn (name, _) => name = Markup.entityN) authored) = 1 andalso
         not (exists (fn (name, _) => name = Markup.typingN) authored))
    in () end
  val _ = event_control "sparse_owner"
  val _ = event_control "reverse_owner"
  fun failed_event_control rust kind hol method expected =
    let
      val calls = Unsynchronized.ref 0
      val start = start_position ("erasure-failed-" ^ method)
      val parameter: M.generic_parameter =
        {rust = rust, pos = start, kind = kind, hol = hol, bounds = [],
         report_reference = fn _ => calls := !calls + 1}
      val scoped = ctxt |> M.with_generic_scope {parameters = [parameter]}
        |> M.with_source_only_parameters [fst hol] |> Variable.declare_typ (TFree hol)
      val prefix = "value." ^ method ^ "::<"
      val body = Parser_Lex_Util.positioned_content_source (prefix ^ rust ^ ">(value)") start
      val ((result, events), markup) = Parser_Test_Reports.markup (fn () =>
        M.capture_generic_use_events scoped (fn observed => Exn.capture0 (fn () =>
          Parser_Test_Elaboration.function observed
            {raw_type = ("nat => (unit,nat,unit,unit,unit) function_body", start),
             parameters = [("value", start)], parameters_pos = start, body = body}) ()))
      val _ = (case result of Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn else
            require "selected failure lost its actual diagnostic"
              (String.isSubstring expected (Runtime.exn_message exn))
        | _ => error "erasure failed native candidate was accepted")
      val _ = require "ambiguous or invalid native selection leaked speculative events or callbacks"
        (null (#source_uses events) andalso null (#witness_uses events) andalso !calls = 0)
      val at_argument = filter (fn (_, props) =>
        Properties.get props Markup.offsetN = SOME (string_of_int (size prefix + 1))) markup
      val _ = require "discarded source argument published semantic navigation or HOL typing/sorting"
        (not (exists (fn (name, _) => member (op =)
          [Markup.entityN, Markup.typingN, Markup.sortingN, Markup.tfreeN, Markup.tvarN] name) at_argument))
    in () end
  val _ = failed_event_control "T" URust_AST.Type_Parameter ("'erasure_failed_t", \<^sort>\<open>type\<close>)
    "ambiguous_erased" "Ambiguous"
  val _ = failed_event_control "N" URust_AST.Const_Parameter ("'erasure_failed_n", \<^sort>\<open>len0\<close>)
    "sparse_owner" "const"
  val position = Position.of_properties [(Markup.lineN, "2"), (Markup.offsetN, "9"),
    (Markup.end_offsetN, "14"), (Markup.fileN, "erasure-sparse-carrier"), ("custom", "a,b;c")]
  val generic = the_single (filter (fn entry =>
    is_none (M.generic_scheme_for_source ctxt (#serial entry)))
    (entries ctxt "sparse_owner"))
  val metadata: D.sparse_generic_arguments =
    {instances = [{source = #serial generic, arguments = [(NONE, position)],
       identities = ["<opaque><segment name=\"Foreign\"/></opaque>"]}],
     pos = position, pending = NONE}
  val marker = D.mk_marker N.NFunction "sparse_owner" position (Free ("sparse_owner", dummyT))
  val wrapped = D.with_sparse_generic_arguments metadata marker
  val _ = require "sparse carrier retains source metadata and arbitrary native positions with no TYPE witness"
    (D.marker_sparse_generic_arguments wrapped = SOME metadata andalso
     is_none (D.marker_generic_arguments wrapped) andalso
     not (Term.exists_subterm (fn Const (name, _) => name = \<^const_name>\<open>Pure.type\<close>
       | _ => false) wrapped) andalso D.dest_marker_untyped wrapped = D.dest_marker_untyped marker)
  val filters = [N.Only_Sources [#serial generic]]
  val _ = require "sparse metadata composes with the existing native source filter"
    (D.restrict_backends filters wrapped aconv
      D.with_sparse_generic_arguments metadata (D.restrict_backends filters marker))
  val _ = List.app (fn bad =>
    ignore (expect_failure "erasure-malformed-carrier" ["malformed urust_dispatch generic arguments"]
      (fn () => D.with_sparse_generic_arguments bad marker)))
    [{instances = [], pos = position, pending = NONE},
     {instances = [{source = #serial generic, arguments = [(NONE, position)], identities = []}],
       pos = position, pending = NONE}]
  val _ = require "source identity, failure and carrier probes leave native entries unchanged"
    (N.dump ctxt = previous)
  val _ = writeln "U2 concrete source identity/alias/conflict/native isolation/reversed order/carrier PASS"
in end
\<close>

section\<open> Combined source owners and backend types \<close>

ML_val\<open>
  local
    open Impl_Declaration_Test
    val ctxt = \<^context>
    val owners = Micro_Rust_Names.associated_source_functions ctxt "ImplCombined::combined_identity"
    val _ = require "combined erased tags collapse owners with the same complete HOL Self type"
      (length owners = 2 andalso #self_type (hd owners) = #self_type (List.last owners) andalso
        #source_identity (hd owners) <> #source_identity (List.last owners))
    fun principal name =
      let
        val typ = Sign.the_const_type \<^theory> (Proof_Context.intern_const ctxt name)
        val substitutions = Term.add_tvarsT typ [] |> rev
          |> map_index (fn (index, variable as (_, sort)) =>
            (variable, TVar (("combined_owner_type", index), sort))) |> TVars.make
      in Term_Subst.instantiateT substitutions typ end
    val _ = require "combined alias/expanded selection changes principal sorts or backend/channel sharing"
      (principal "impl_combined_via_alias" = principal "impl_combined_via_expanded")
    val _ = require "ordinary implicit-only impl changes its complete principal type versus escape twin"
      (principal "impl_backend_only_backend_share" = principal "impl_backend_share_escape")
    fun constant_type name = Sign.the_const_type \<^theory> (Proof_Context.intern_const ctxt name)
    fun shared name =
      let val typ = constant_type name
          val [self, alias, pointer, borrowed] = binder_types typ
          val Type (_, [_, result, _, _, _]) = body_type typ
      in require (name ^ ": Self, alias, pointer and reference have independent roles")
        (self = alias andalso self = pointer andalso self = borrowed andalso result = self) end
    val _ = List.app shared ["impl_backend_only_backend_share", "impl_combined_combined_share"]
    val global_type = constant_type "impl_global_backend_global_share"
    val [global_self, global_alias, Type (_, [Type (_, [address, global]), global', _])] =
      binder_types global_type
    val _ = require "singleton global impl lost index one or introduced an independent pointer global"
      (global_self = Type (\<^type_name>\<open>option\<close>, [global]) andalso global_alias = global_self andalso
        global' = global andalso address <> global)
    structure M = URust_Type_Mappings
    fun parsed current label text = URust_Parser.parse_type_source current (source label text)
    val ambient = TFree ("'urust_address", \<^sort>\<open>ord\<close>)
    val fixed = ctxt |> Variable.declare_typ ambient
      |> Variable.declare_typ (TFree ("'urust_global", \<^sort>\<open>type\<close>))
    val authored_target = "ImplCombined<\<tau>\<open>'urust_address\<close>, Alpha, 0>"
    val (self, identity) = M.resolve_impl_target_identity fixed
      (parsed fixed "combined-rigid-target" authored_target)
    val source = M.with_impl_self_identity (self, identity) fixed
    val [same, alias, pointer] = M.resolve_signature source
      (map (parsed source "combined-rigid-member") ["Self", authored_target,
        "*const \<tau>\<open>'urust_address\<close>"])
    val _ = require "impl role finalization captured or strengthened an ambient/authored variable"
      (same = alias andalso alias = pointer andalso
        member (op =) (Term.add_tfreesT same []) ("'urust_address", \<^sort>\<open>ord\<close>) andalso
        length (Term.add_tfreesT same []) = 3)
    val _ = List.app (fn (argument, expected) => ignore (expect_failure "combined-target-hole"
      [expected] (fn () =>
        M.resolve_impl_target_identity ctxt
          (parsed ctxt "combined-target-hole" ("ImplCombined<" ^ argument ^ ", Alpha, 0>")))))
      [("\<tau>\<open>_\<close>", "urust: an impl target must not contain inference holes"),
       ("\<tau>\<open>?'hole\<close>", "Illegal schematic type variable")]
  in val _ = () end
\<close>

section\<open> Rich member headers reject during denotation \<close>

ML_val\<open>
local
  open Impl_Declaration_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val prior_registry = registry_snapshot ctxt
  val rows =
    [("generic", "T: Sequence<Item = u8>", "", "generic trait bounds are not supported"),
     ("callable-wrapper", "F: [const] FnOnce(u8) -> u8", "", "conditional-const trait bounds are not supported"),
     ("higher-ranked", "F: for<'a> Fn(&'a u8)", "", "higher-ranked trait bounds are not supported"),
     ("conditional-const", "T: [const] Marker", "", "conditional-const trait bounds are not supported"),
     ("const-type", "const N: bool", "", "const parameters require usize"),
     ("where-head", "T", "where (T, u8): Marker ", "where clauses may only bound")]
  val _ = List.app (fn (label, parameters, predicate, expected) =>
    let
      val member_source = "fn late<" ^ parameters ^ ">(self, value: u8) -> u8 " ^ predicate ^ "{ value }"
      val raw = "struct HeaderOwner { value: u8 }\nimpl HeaderOwner {" ^
        " fn early(self, value: u8) -> u8 { value }\n" ^ member_source ^ "\n}"
      val parsed = the_chunk ctxt (label ^ "-parse") raw
      val _ = List.app (fn options =>
        let val printed = URust_Printer.string_of_chunk options parsed
        in require (label ^ ": rich member syntax failed its structured roundtrip")
          (URust_Printer.tokens_of_chunk options parsed =
            URust_Printer.tokens_of_chunk options (the_chunk ctxt (label ^ "-printed") printed))
        end) [URust_Printer.serialized_options, URust_Printer.human_options]
      val reporter = !Private_Output.report_fn
      val writer = !Private_Output.writeln_fn
      val {result, output, reports, ...} =
        capture true (label ^ "-denotation") thy
          ("urust [verbosity = 2] " ^ command_source raw)
      val diagnostic = case result of Exn.Exn exn => Runtime.exn_message exn
        | _ => error (label ^ ": unsupported member denotation was accepted")
      val _ = require (label ^ ": member did not fail at authoritative denotation")
        (String.isSubstring expected diagnostic)
      val _ = require (label ^ ": late member failure leaked chunk output/definitions")
        (null (authored_output output) andalso
          not (exists (fn (name, props) => name = Markup.entityN andalso
            is_some (Properties.get props Markup.defN) andalso
            member (op =) ["constant", "micro_rust_type", "urust_generic_parameter"]
              (the_default "" (Properties.get props Markup.kindN))) (report_events reports)))
      val _ = require (label ^ ": member failure escaped registry/callback state")
        (registry_snapshot ctxt = prior_registry andalso
          PolyML.pointerEq (reporter, !Private_Output.report_fn) andalso
          PolyML.pointerEq (writer, !Private_Output.writeln_fn))
      val recovered = context_after (label ^ "-recovery") thy
        (chunk "struct HeaderOwner { value: u8 }\nimpl HeaderOwner { fn early(self) -> Self { self } }")
      val _ = require (label ^ ": member failure blocked recovery")
        (not (null (entries recovered "HeaderOwner::early")))
    in () end) rows
in val _ = () end
\<close>

chapter\<open> Generic impl ownership and joint schemes \<close>

ML_val\<open>
local
  open Impl_Syntax_Test
  structure N = Micro_Rust_Names
  structure D = Micro_Rust_Dispatch
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val thy = Proof_Context.theory_of ctxt
  val pos = Position.of_properties [(Markup.offsetN, "7"), (Markup.end_offsetN, "19"),
    (Markup.fileN, "generic-impl-neutral"), (Markup.idN, "generic-impl-id"), ("custom", "a:,;")]
  val parameter = TVar (("shared_owner", 0), \<^sort>\<open>type\<close>)
  val name = ("source", 0)
  fun atom primitive = N.Source_Node (N.Primitive_Source primitive, [])
  fun template tree variables = {self_type = \<^typ>\<open>unit\<close>, source = SOME tree,
    variables = variables, requires_source_identity = true}: N.target_template
  val variable = {name = name, kind = N.Type_Source, witness = SOME parameter}: N.source_variable
  val pattern = template (N.Source_Node (N.Mapped_Source "NeutralOwner",
    [N.Source_Variable (name, N.Type_Source)])) [variable]
  fun selection tree evidence = {self_type = \<^typ>\<open>unit\<close>, source = SOME tree,
    source_identity = SOME "opaque compatibility token", evidence = evidence,
    inputs = [([0], ("u8 /* original comment */", pos))], pos = pos}: N.target_selection
  val selected = selection (N.Source_Node (N.Mapped_Source "NeutralOwner", [atom "u8"]))
    [([0], \<^typ>\<open>8 word\<close>)]
  val matched = the (N.match_target ctxt pattern selected (Vartab.empty, 0))
  val _ = require "erased target source evidence constrains the native owner witness"
    (Envir.norm_type (#types matched) parameter = \<^typ>\<open>8 word\<close>)
  val _ = require "an explicit target cannot contradict the same value variable"
    (not (can (Sign.typ_unify thy (parameter, \<^typ>\<open>bool\<close>))
      (#types matched, #maxidx matched)))
  val pair = template (N.Source_Node (N.Tuple_Source,
    [N.Source_Variable (name, N.Type_Source), N.Source_Variable (name, N.Type_Source)])) [variable]
  val _ = require "repeated source variables reject unequal canonical arguments"
    (is_none (N.match_target ctxt pair
      (selection (N.Source_Node (N.Tuple_Source, [atom "u8", atom "u16"])) []) (Vartab.empty, 0)))
  val first_rigid = serial ()
  val second_rigid = serial ()
  fun rigid identity = N.Source_Rigid (identity, N.Type_Source)
  val _ = require "equal HOL witnesses do not collapse distinct rigid caller declarations"
    (is_none (N.match_target ctxt pair
      (selection (N.Source_Node (N.Tuple_Source, [rigid first_rigid, rigid second_rigid]))
        [([0], \<^typ>\<open>bool\<close>), ([1], \<^typ>\<open>bool\<close>)]) (Vartab.empty, 0)))
  val _ = require "repeated references to the same rigid caller declaration agree"
    (is_some (N.match_target ctxt pair
      (selection (N.Source_Node (N.Tuple_Source, [rigid first_rigid, rigid first_rigid]))
        [([0], \<^typ>\<open>bool\<close>), ([1], \<^typ>\<open>bool\<close>)]) (Vartab.empty, 0)))
  val _ = require "source type and const roles remain distinct"
    (is_none (N.match_target ctxt pattern
      (selection (N.Source_Node (N.Mapped_Source "NeutralOwner",
        [N.Source_Node (N.Numeric_Source 3, [])])) []) (Vartab.empty, 0)))
  val concrete = template (N.Source_Node (N.Mapped_Source "NeutralOwner", [atom "u8"])) []
  val other = template (N.Source_Node (N.Mapped_Source "NeutralOwner", [atom "u16"])) []
  val _ = require "generic/concrete source ownership overlaps in both orders"
    (N.overlapping_targets (pattern, concrete) andalso N.overlapping_targets (concrete, pattern))
  val _ = require "erased concrete source owners remain disjoint"
    (not (N.overlapping_targets (concrete, other)))
  val _ = require "native inference does not fabricate an erased concrete source identity"
    (is_none (N.match_target ctxt concrete
      (selection (N.Source_Node (N.Mapped_Source "NeutralOwner",
        [N.Source_HOL (N.Type_Source, TVar (("unknown_source", 9017), \<^sort>\<open>type\<close>))])) [])
      (Vartab.empty, 9017)))
  val old_ctxt = N.reserve_associated_source_function
    {name = "NeutralOwner::legacy", self_type = \<^typ>\<open>unit\<close>, identity = serial (),
      source_identity = SOME "not a serialized identity", pos = pos} (Context.Proof ctxt)
  val _ = ignore (expect_failure "legacy-generic-overlap" ["overlapping Self types"] (fn () =>
    N.reserve_associated_template_function {name = "NeutralOwner::legacy", target = pattern,
      identity = serial (), source_identity = NONE, pos = pos} old_ctxt))
  val marker = D.mk_marker_positions N.NFunction "NeutralOwner::call" pos [pos]
    (Free ("NeutralOwner::call", dummyT))
  val caller = TVar (("caller", 9017), \<^sort>\<open>type\<close>)
  val selected = {self_type = caller, source = SOME (N.Source_HOL (N.Type_Source, caller)),
    source_identity = SOME "opaque : , token", evidence = [([0], caller)],
    inputs = [([0], ("u8 /* : ; original */", pos))], pos = pos}: N.target_selection
  val metadata: D.scoped_sparse_arguments = {instances =
    [{source = 17, target = SOME selected, arguments = NONE, identities = []},
     {source = 19, target = SOME selected, arguments = SOME [(NONE, pos), (SOME caller, pos)],
       identities = ["source-only", "witness"]}], pos = pos, pending = NONE}
  val wrapped = D.with_scoped_sparse_arguments metadata marker
  val actual = the (D.marker_scoped_sparse_arguments wrapped)
  val _ = require "owner-aware carrier preserves canonical structure, caller sharing and every position"
    (actual = metadata andalso D.dest_marker_untyped wrapped = D.dest_marker_untyped marker)
  val _ = require "old scalar and sparse getters do not reinterpret owner-aware instances"
    (is_none (D.marker_generic_arguments wrapped) andalso is_none (D.marker_sparse_generic_arguments wrapped))
  val filters = [N.Exclude_Method_Only, N.Only_Sources [17, 19]]
  val _ = require "owner-aware carrier composes with native filters in either order"
    (D.restrict_backends filters wrapped aconv
      D.with_scoped_sparse_arguments metadata (D.restrict_backends filters marker))
  val old_registration: D.generic_registration = the (D.Generic_Transform.get thy)
  val _ = require "old registration getter retains its exact record"
    (is_some (#sparse_transform old_registration))
  val [entry] = N.lookups ctxt N.NFunction "GenericPocket::irrelevant"
  val scoped = the (M.scoped_generic_scheme_for_source ctxt (#serial entry))
  val _ = require "owner-only scheme exists without granting a member turbofish"
    (is_some (M.scoped_owner scoped) andalso null (M.scoped_parameters scoped) andalso
      is_none (M.generic_scheme_for_source ctxt (#serial entry)))
  val [member] = N.lookups ctxt N.NFunction "GenericPocket::replace"
  val member_scheme = the (M.scoped_generic_scheme_for_source ctxt (#serial member))
  val _ = require "owner and member declaration lists remain separate"
    (map #rust (#parameters (the (M.scoped_owner member_scheme))) = ["T"] andalso
      map #rust (M.scoped_parameters member_scheme) = ["U"])
  val _ = List.app (fn (left, right) => require (left ^ ": full principal type twin")
    (Sign.the_const_type thy left = Sign.the_const_type thy right))
    [(\<^const_name>\<open>generic_pocket_retain\<close>, \<^const_name>\<open>generic_pocket_retain_twin\<close>),
     (\<^const_name>\<open>generic_pocket_pass\<close>, \<^const_name>\<open>generic_pocket_pass_twin\<close>),
     (\<^const_name>\<open>generic_pocket_replace\<close>, \<^const_name>\<open>generic_pocket_replace_twin\<close>),
     (\<^const_name>\<open>generic_pocket_irrelevant\<close>, \<^const_name>\<open>generic_pocket_irrelevant_twin\<close>),
     (\<^const_name>\<open>generic_buffer_capacity\<close>, \<^const_name>\<open>generic_buffer_capacity_twin\<close>),
     (\<^const_name>\<open>generic_buffer_borrow\<close>, \<^const_name>\<open>generic_buffer_borrow_twin\<close>)]
  val _ = require "impl scope never escapes to the next command"
    (is_none (M.generic_scope ctxt) andalso is_none (M.generic_scope_identities ctxt) andalso
      is_none (M.impl_self ctxt))
in end
\<close>

section\<open> Generic impl rejection and recovery \<close>
ML_val\<open>
local
  fun require label condition = if condition then () else error ("generic impl regression: " ^ label)
  val ctxt = \<^context>
  val thy = Proof_Context.theory_of ctxt
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun annotation text = "\<omega>" ^ cartouche text
  fun command body = "urust [verbosity = 0] " ^ cartouche body
  fun run label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
        (Toplevel.make_state (SOME thy))) ()
  val rows =
    [("retained-target-value-contradiction", "fn RejectRetained(value: bool) -> bool { GenericPocket::<u8>::pass(value) }", "no backend"),
     ("erased-target-value-contradiction", "fn RejectErased(value: bool) -> bool { ImplDemandBox::<u8>::pass(value) }", "no backend"),
     ("opaque-target-missing-witness", "fn RejectOpaque(value: bool) -> bool { ImplDemandBox::<UnmappedTag>::pass(value) }", "unknown Rust type"),
     ("member-generic-count", "fn RejectMemberCount(owner: GenericPocket<u8>, value: bool) -> bool { GenericPocket::<u8>::replace::<u8, bool>(owner, value) }", "generic argument"),
     ("member-generic-kind", "fn RejectMemberKind(owner: GenericPocket<u8>, value: bool) -> bool { GenericPocket::<u8>::replace::<3>(owner, value) }", "numeric generic arguments"),
     ("target-generic-count", "fn RejectTargetCount(owner: GenericPocket<u8>) -> GenericPocket<u8> { GenericPocket::<u8, bool>::retain(owner) }", "generic arities"),
     ("target-generic-kind", "fn RejectTargetKind(owner: GenericBuffer<u8, 3>) -> GenericBuffer<u8, 3> { GenericBuffer::<u8, bool>::retain(owner) }", "const"),
     ("owner-only-member-turbofish", "fn RejectOwnerOnly(value: u8) -> u8 { GenericPocket::<u8>::irrelevant::<bool>(value) }", "generic arguments are not supported"),
     ("discarded-alias-const", "impl<const N: usize> ImplDemandDiscard<N> {}", "unconstrained"),
     ("repeated-target-contradiction", "fn RejectRepeated(value: u8) -> u8 { ImplDemandPair::<u8, bool>::repeated(value) }", "no associated function"),
     ("unconstrained-type", "impl<T> GenericPocket<u8> { fn rejected(value: T) -> T { value } }", "unconstrained"),
     ("unconstrained-const", "impl<T, const N: usize> GenericPocket<T> {}", "unconstrained"),
     ("member-shadow-type", "impl<T> GenericPocket<T> { fn rejected<T>(value: T) -> T { value } }", "redeclares an impl parameter"),
     ("member-shadow-lifetime", "impl<'a, T> GenericPocket<T> { fn rejected<'a>() {} }", "duplicate lifetime parameter"),
     ("impl-duplicate-type", "impl<T, T> GenericPocket<T> {}", "duplicate generic parameter"),
     ("impl-const-kind", "impl<const N: bool> GenericBuffer<u8, N> {}", "const parameters require usize"),
     ("member-remaps-inherited", "impl<T> GenericPocket<T> {\n" ^
       annotation ("hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'remapped" ^ "]") ^
       "\n fn rejected<U>(value: U) -> U { value } }", "unknown parameter override"),
     ("member-shadows-inherited-hol", "impl<T> GenericPocket<T> {\n" ^
       annotation ("hol_type_parameters = [\"U\" \<rightarrow> " ^ cartouche "'t" ^ "]") ^
       "\n fn rejected<U>(value: U) -> U { value } }", "redeclares an impl HOL parameter"),
     ("member-concrete-predicate", "impl<T> GenericPocket<T> { fn rejected(self) where u8: Unmapped {} }", "where clauses may only bound"),
     ("body-only-inherited-type", "impl<T> ImplDemandBox<T> { fn body_only(value: u8) -> u8 { let spare = \<epsilon>\<open>literal (undefined :: 't)\<close>; value } }", "signature"),
     ("body-only-const", "impl<const N: usize> GenericBuffer<u8, N> { fn rejected() -> usize { N } }", "signature"),
     ("failed-later-member", "impl<T> GenericPocket<T> { fn first(value: T) -> T { value } fn rejected(value: T) -> T { missing_value } }", "missing_value")]
  val names = Micro_Rust_Names.dump ctxt |> map (fn (kind, key, entry) => (kind, key, #serial entry))
  val types = URust_Type_Mappings.dump ctxt |> map (fn (key, entry) =>
    (key, URust_Type_Mappings.entry_identity entry, URust_Type_Mappings.entry_template entry))
  val _ = List.app (fn (label, body, expected) =>
    let
      val result = Exn.capture0 (fn () => run label (command body)) ()
      val message = case result of Exn.Res _ => error (label ^ ": unexpectedly succeeded")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val _ = require (label ^ ": " ^ message) (String.isSubstring expected message)
      val _ = require (label ^ ": changed the original registry")
        (names = (Micro_Rust_Names.dump ctxt |> map (fn (kind, key, entry) => (kind, key, #serial entry))) andalso
          types = (URust_Type_Mappings.dump ctxt |> map (fn (key, entry) =>
            (key, URust_Type_Mappings.entry_identity entry, URust_Type_Mappings.entry_template entry))))
      val recovery = run (label ^ "-recovery") (command "fn GenericImplRecovery(value: u8) -> u8 { value }")
      val recovered = Toplevel.context_of recovery
      val _ = require (label ^ ": failed to recover or leaked generic state")
        (not (null (Micro_Rust_Names.lookups recovered Micro_Rust_Names.NFunction "GenericImplRecovery")) andalso
          is_none (URust_Type_Mappings.generic_scope recovered) andalso
          is_none (URust_Type_Mappings.impl_self recovered))
    in () end) rows
in end
\<close>

section\<open> Canonical target input provenance and selected effects \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  open URust_AST
  fun require label condition = if condition then () else error ("impl target provenance: " ^ label)
  val ctxt = Context_Position.set_visible true \<^context>
  fun pos offset = Position.make0 1 offset 0 "" "s2-target-origins" "s2-target-origins"
  fun source text offset = Parser_Lex_Util.positioned_content_source text (pos offset)
  fun origin (Rust_Type_Argument typ) = rust_type_position typ
    | origin (Rust_Numeric_Argument integer) = integer_literal_position integer
    | origin _ = raise Fail "unexpected direct target argument"
  fun target name raws =
    let val supplied = map (fn (text, offset) => let val input = source text offset
      in (URust_Parser.parse_generic_argument_source ctxt input, input) end) raws
      val typ = Path_Type ([Rust_Type_Path_Segment (name, pos 1, SOME (map fst supplied),
        make_source_layout (pos 1) [])], make_source_layout (pos 1) [])
    in M.resolve_target_selection_with_inputs ctxt
      (map (fn (argument, input) => (origin argument, input)) supplied) typ end
  val reordered = target "ImplDemandSwap" [("u8 /* original first */", 101),
    ("u16 /* \<alpha> original second */", 201)]
  fun input selection path = the (AList.lookup (op =) (#inputs selection) path)
  val _ = require "canonical reordered slots retain original comments and full native positions"
    (#1 (input reordered [0]) = "u16 /* \<alpha> original second */" andalso
      Position.offset_of (#2 (input reordered [0])) = SOME 201 andalso
      #1 (input reordered [1]) = "u8 /* original first */" andalso
      Position.offset_of (#2 (input reordered [1])) = SOME 101)
  val nested = target "ImplDemandBox" [("ImplDemandSwap<u8 /* \<alpha> inner */, bool>", 301)]
  val _ = require "nested alias slots use authoritative Isabelle symbol spans after escaped comments"
    (#1 (input nested [0]) = "ImplDemandSwap<u8 /* \<alpha> inner */, bool>" andalso
      #1 (input nested [0, 0]) = "bool" andalso
      Position.offset_of (#2 (input nested [0, 0])) = SOME 334 andalso
      #1 (input nested [0, 1]) = "u8" andalso
      Position.offset_of (#2 (input nested [0, 1])) = SOME 316)
  val entry = the_single (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction "ImplDemandPair::first")
  val prepared = M.prepare_scoped_target_selection ctxt (#serial entry) reordered
  val _ = require "selected demand resolves the canonical first slot from its original second input"
    (AList.lookup (op =) (#evidence prepared) [0] = SOME \<^typ>\<open>16 word\<close> andalso
      is_none (AList.lookup (op =) (#evidence prepared) [1]))
  fun collect (XML.Text _) reports = reports
    | collect (XML.Elem (markup, body)) reports = fold collect body (markup :: reports)
  fun reports action =
    let val output = Unsynchronized.ref ([]: string list)
      val result = Unsynchronized.setmp Private_Output.report_fn
        (fn chunks => output := chunks @ !output)
        (fn () => Print_Mode.with_modes [Print_Mode.PIDE] action ()) ()
    in (result, fold collect (maps YXML.parse_body (!output)) []) end
  fun synthetic_control label =
    let
      val input_source = Parser_Lex_Util.positioned_content_source "ImplDemandSwap<u8, u16>"
        (Position.label label (pos 401))
      val synthetic_type = URust_Parser.parse_type_source ctxt input_source
      val expected_origin = case synthetic_type of
        Path_Type ([Rust_Type_Path_Segment (_, _, SOME [_, second], _)], _) => origin second
        | _ => raise Fail "synthetic alias syntax changed"
      val synthetic = M.resolve_target_selection ctxt synthetic_type
      val supplied_origin = #2 (input synthetic [0])
      val _ = require "synthetic marker retains original native label and all authoritative coordinates"
        (Position.label_of supplied_origin = SOME ("urust_synthetic_target_input:" ^ label) andalso
          Position.properties_of (Position.label label supplied_origin) =
            Position.properties_of expected_origin)
      val (prepared, markup) = reports (fn () =>
        M.prepare_scoped_target_selection ctxt (#serial entry) synthetic)
      val _ = require "synthetic demanded witness emits no fabricated authored report ranges"
        (not (exists (fn (_, props) => Properties.get props Markup.idN =
          Position.id_of expected_origin) markup))
      val _ = require "synthetic demand preserves semantic substitution"
        (AList.lookup (op =) (#evidence prepared) [0] = SOME \<^typ>\<open>16 word\<close>)
      val opaque = M.resolve_target_selection ctxt (URust_Parser.parse_type_source ctxt
        (Parser_Lex_Util.positioned_content_source "ImplDemandSwap<u8, MissingWitness>"
          (Position.label label (pos 501))))
      val (result, failed_reports) = reports (fn () => Exn.capture0
        (fn () => M.prepare_scoped_target_selection ctxt (#serial entry) opaque) ())
      val diagnostic = case result of Exn.Exn (ERROR text) => text
        | Exn.Exn exn => Exn.reraise exn | Exn.Res _ => error "opaque synthetic witness accepted"
      val positions = fold collect (YXML.parse_body diagnostic) []
      val _ = require "failed synthetic demand restores original absent/nonempty label in diagnostics"
        (not (String.isSubstring "urust_synthetic_target_input:" diagnostic) andalso
          exists (fn (_, props) => Properties.get props Markup.idN = SOME "s2-target-origins" andalso
            Properties.get props Markup.labelN = (if label = "" then NONE else SOME label)) positions andalso
          not (exists (fn (_, props) => Properties.get props Markup.idN = SOME "s2-target-origins")
            failed_reports))
    in () end
  val _ = synthetic_control ""
  val _ = synthetic_control "authored diagnostic label"
in end
\<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  structure N = Micro_Rust_Names
  structure D = Micro_Rust_Dispatch
  fun require label condition = if condition then () else error ("scoped selected effects: " ^ label)
  val ctxt = \<^context>
  val position = Position.make0 1 1 0 "" "s2-selected-effects" "s2-selected-effects"
  val calls = Unsynchronized.ref 0
  val parameter: M.generic_parameter = {rust = "T", pos = position,
    kind = URust_AST.Type_Parameter, hol = ("'selected_effect", \<^sort>\<open>type\<close>),
    bounds = [], report_reference = fn _ => calls := !calls + 1}
  val scoped = ctxt |> M.with_generic_scope {parameters = [parameter]}
    |> Variable.declare_typ (TFree (#hol parameter))
  val target = M.resolve_target_selection ctxt (URust_Parser.parse_type_source ctxt
    (Parser_Lex_Util.positioned_content_source "ImplDemandBox<UnmappedTag>" position))
  val entry = the_single (N.lookups ctxt N.NFunction "ImplDemandBox::local")
  val payload: D.scoped_sparse_arguments = {instances = [{source = #serial entry,
    target = SOME target, arguments = NONE, identities = []}], pos = position,
    pending = SOME [("T", position)]}
  val body = Type (\<^type_name>\<open>function_body\<close>,
    [\<^typ>\<open>unit\<close>, TFree (#hol parameter), \<^typ>\<open>unit\<close>,
      \<^typ>\<open>unit\<close>, \<^typ>\<open>unit\<close>])
  val occurrence = \<^typ>\<open>unit\<close> --> TFree (#hol parameter) --> body
  val (_, events) = M.capture_generic_use_events scoped (fn observed =>
    let
      val effects = D.filtered_candidates_with_scoped_generic_effects observed [] N.NFunction
        "ImplDemandBox::local" occurrence NONE NONE NONE (SOME payload)
      val _ = require "candidate preparation invokes no original callback" (!calls = 0)
      val (_, commit) = the_single effects
      val _ = commit ()
    in () end)
  val _ = require "selected replay publishes one source/witness event and one original callback"
    (!calls = 1 andalso #source_uses events = [fst (#hol parameter)] andalso
      #witness_uses events = [fst (#hol parameter)])
  val failed_occurrence = \<^typ>\<open>unit\<close> --> \<^typ>\<open>bool\<close> -->
    Type (\<^type_name>\<open>function_body\<close>, replicate 5 \<^typ>\<open>bool\<close>)
  val (_, discarded) = M.capture_generic_use_events scoped (fn observed =>
    ignore (D.filtered_candidates_with_scoped_generic_effects observed [] N.NFunction
      "ImplDemandBox::local" failed_occurrence NONE NONE NONE (SOME payload)))
  val _ = require "discarded native mismatch releases no speculative effects or callbacks"
    (!calls = 1 andalso null (#source_uses discarded) andalso null (#witness_uses discarded))
in end
\<close>

section\<open> Generic owner overlaps and theory merge orders \<close>

ML_val\<open>
local
  structure N = Micro_Rust_Names
  structure M = URust_Type_Mappings
  fun require label condition = if condition then () else error ("generic impl merge: " ^ label)
  val base = \<^theory>
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun chunk text = "urust [verbosity = 0] " ^ cartouche text
  fun run thy label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
      (Toplevel.make_state (SOME thy))) ()
  fun branch name parents text = Theory.begin_theory (name, Position.none) parents
    |> (fn thy => Toplevel.theory_of (run thy name text)) |> Theory.end_theory
  val parent = branch "Generic_Impl_Merge_Parent" [base]
    ("urust_type [erase = " ^ cartouche " 'left, 'right " ^
      "] \"GenericMergeOwner<'left, 'right>\" = " ^ cartouche " unit ")
  fun member declarations target = chunk
    ("impl" ^ declarations ^ " GenericMergeOwner<" ^ target ^
      "> { fn pick(value: T) -> T { value } }")
  val first = branch "Generic_Impl_Merge_First" [parent] (member "<T>" "T, bool")
  val second = branch "Generic_Impl_Merge_Second" [parent] (member "<T>" "T, u16")
  fun merge name parents = Theory.begin_theory (name, Position.none) parents
  fun check_merge (name, parents) =
    let
      val merged = merge name parents
      val ctxt = Proof_Context.init_global merged
      val owners = N.associated_template_functions ctxt "GenericMergeOwner::pick"
      val _ = require "disjoint generic erased targets coexist" (length owners = 2)
      val state = run merged name (chunk
        ("fn GenericMergeFirst(value: u8) -> u8 { GenericMergeOwner::<u8, bool>::pick(value) }\n" ^
         "fn GenericMergeSecond(value: u8) -> u8 { GenericMergeOwner::<u8, u16>::pick(value) }"))
      val result = Toplevel.context_of state
      val _ = require "both canonical selected targets elaborate with complete native types"
        (length (N.lookups result N.NFunction "GenericMergeFirst") = 1 andalso
          length (N.lookups result N.NFunction "GenericMergeSecond") = 1 andalso
          is_none (M.generic_scope result) andalso is_none (M.impl_self result))
    in map #identity owners |> sort int_ord end
  val forward = check_merge ("Generic_Impl_Merge_Forward", [first, second])
  val reverse = check_merge ("Generic_Impl_Merge_Reverse", [second, first])
  val _ = require "same source declarations and selection survive both theory merge orders"
    (forward = reverse)
  val concrete = branch "Generic_Impl_Merge_Concrete" [parent] (chunk
    "impl GenericMergeOwner<u8, bool> { fn pick(value: u8) -> u8 { value } }")
  val crossed = branch "Generic_Impl_Merge_Crossed" [parent] (chunk
    "impl<U> GenericMergeOwner<u8, U> { fn pick(value: u8) -> u8 { value } }")
  fun reject name parents =
    (case Exn.capture0 (fn () => merge name parents) () of
       Exn.Exn (ERROR message) => require "generic overlap diagnostics survive either order"
         (String.isSubstring "overlapping Self types" message)
     | Exn.Exn exn => Exn.reraise exn | Exn.Res _ => error "overlapping generic owners merged")
  val _ = List.app (fn (name, parents) => reject name parents)
    [("Generic_Impl_Overlap_Concrete_Forward", [first, concrete]),
     ("Generic_Impl_Overlap_Concrete_Reverse", [concrete, first]),
     ("Generic_Impl_Overlap_Generic_Forward", [first, crossed]),
     ("Generic_Impl_Overlap_Generic_Reverse", [crossed, first])]
  val _ = require "isolated merge fixture does not register in the caller"
    (null (N.lookups \<^context> N.NFunction "GenericMergeOwner::pick"))
in end
\<close>

section\<open> Generic member freshness, native reports and failed-member rollback \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  structure N = Micro_Rust_Names
  structure D = Micro_Rust_Dispatch
  fun require label condition = if condition then () else error ("generic impl native control: " ^ label)
  val ctxt = \<^context>
  val entry = the_single (N.lookups ctxt N.NFunction "GenericPocket::replace")
  fun check index =
    let
      val inherited = TVar (("owner_caller", index), \<^sort>\<open>type\<close>)
      val local_parameter = TVar (("member_caller", index + 1), \<^sort>\<open>type\<close>)
      val channels = map (fn offset => TVar (("channel_caller", index + offset), \<^sort>\<open>type\<close>)) [2, 3, 4, 5]
      val owner = Type (\<^type_name>\<open>generic_pocket\<close>, [inherited])
      val [state, abort, input, output] = channels
      val occurrence = owner --> local_parameter --> Type (\<^type_name>\<open>function_body\<close>,
        [state, local_parameter, abort, input, output])
      val target: N.target_selection = {self_type = owner,
        source = SOME (N.Source_Node (N.Mapped_Source "GenericPocket",
          [N.Source_HOL (N.Type_Source, inherited)])), source_identity = NONE,
        evidence = [([0], inherited)], inputs = [], pos = Position.none}
      val arguments: D.scoped_sparse_arguments = {instances = [{source = #serial entry,
        target = SOME target, arguments = SOME [(SOME local_parameter, Position.none)], identities = [""]}],
        pending = NONE, pos = Position.none}
      val [(candidate, _)] = D.filtered_candidates_with_scoped_generic_effects ctxt [] N.NFunction
        "GenericPocket::replace" occurrence NONE NONE NONE (SOME arguments)
      val backend = case Term_Position.strip_positions (#term candidate) of
        Const ("_type_constraint_", _) $ term => term | term => term
      val expected = Term.map_types (fn _ => occurrence)
        (Const (\<^const_name>\<open>generic_pocket_replace\<close>, dummyT))
      val _ = require "target, local member and all channel variables share the actual native backend"
        (backend aconv expected)
    in Term.add_tvars backend [] end
  val first = check 9017
  val second = check 12017
  val _ = require "successive owner/member selections retain independent caller variables"
    (null (inter (op =) first second))
  val locale_entries = N.lookups ctxt N.NFunction "ImplLocalePair::locale_replace"
  val _ = require "locale entries retain one declaration serial and distinct complete ambient types"
    (length locale_entries = 2 andalso length (distinct (op =) (map #serial locale_entries)) = 1 andalso
      length (distinct (op =) (map (fastype_of o #hol_term) locale_entries)) = 2)
  val owner_entries = N.associated_template_functions ctxt "ImplLocalePair::locale_replace"
  val _ = require "joint scheme transport retains both native owners"
    (length owner_entries = 2 andalso forall (fn {identity, ...} =>
      is_some (M.scoped_generic_scheme_for_source ctxt identity)) owner_entries)
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun run thy label text = fold (Toplevel.command_exception false)
    (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
    (Toplevel.make_state (SOME thy))
  val label = "generic-failed-member-navigation"
  val text = "urust [verbosity = 0] " ^ cartouche
    "impl<'a, T> GenericPocket<T> { fn earlier<'b>(self) -> Self { self } fn failing(value: T) -> T { missing_value } }"
  val snapshot = N.dump ctxt |> map (fn (kind, key, entry) => (kind, key, #serial entry))
  val (failed, markup) = Parser_Test_Reports.markup (fn () => Exn.capture0
    (fn () => run \<^theory> label text) ())
  val _ = require "failed generic member retains actual error"
    (case failed of Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
      else String.isSubstring "missing_value" (Runtime.exn_message exn) | _ => false)
  val _ = require "earlier member and local lifetime declarations publish no semantic reports"
    (not (exists (fn (name, props) => name = Markup.entityN andalso
      is_some (Properties.get props Markup.defN) andalso
      member (op =) [SOME "'b", SOME "GenericPocket::earlier", SOME "generic_pocket_earlier"]
        (Properties.get props Markup.nameN)) markup))
  val _ = require "failed member preserves caller registry and all generic/lifetime scope boundaries"
    (snapshot = (N.dump ctxt |> map (fn (kind, key, entry) => (kind, key, #serial entry))) andalso
      is_none (M.generic_scope ctxt) andalso is_none (M.impl_self ctxt))
  val recovered = run \<^theory> "generic-member-navigation-recovery"
    ("urust [verbosity = 0] " ^ cartouche "fn GenericNavigationRecovery(value: u8) -> u8 { value }")
  val _ = require "positioned recovery remains monomorphic and closed"
    (is_none (M.generic_scope (Toplevel.context_of recovered)) andalso
      not (null (N.lookups (Toplevel.context_of recovered) N.NFunction "GenericNavigationRecovery")))
in end
\<close>

section\<open> Joint locale schemes and selected effects across theory merges \<close>

ML_val\<open>
local
  structure N = Micro_Rust_Names
  structure M = URust_Type_Mappings
  structure D = Micro_Rust_Dispatch
  fun require label condition = if condition then () else error ("joint locale merge: " ^ label)
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun hol text = "\<tau>" ^ cartouche text
  fun chunk text = "urust [verbosity = 0] " ^ cartouche text
  fun run thy label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
      (Toplevel.make_state (SOME thy))) ()
  fun branch name parents text = Theory.begin_theory (name, Position.none) parents
    |> (fn thy => Toplevel.theory_of (run thy name text)) |> Theory.end_theory
  val parent = branch "Generic_Joint_Merge_Parent" [\<^theory>]
    ("urust_type \"GenericJointOwner<'payload, 'ambient>\" = " ^ cartouche " 'payload * 'ambient " ^
      "\nlocale generic_joint_merge = fixes joint_seed :: 'ambient\nbegin\n" ^
      chunk ("impl<T> GenericJointOwner<T, " ^ hol "'ambient" ^
        "> { fn joint<U>(self, value: U) -> U { let spare = joint_seed; value } }") ^ "\nend")
  val natural = branch "Generic_Joint_Merge_Nat" [parent]
    ("interpretation joint_nat: generic_joint_merge " ^ cartouche "0 :: nat" ^ " .")
  val boolean = branch "Generic_Joint_Merge_Bool" [parent]
    "interpretation joint_bool: generic_joint_merge False ."
  fun check (name, parents) =
    let
      val thy = Theory.begin_theory (name, Position.none) parents
      val ctxt = Proof_Context.init_global thy
      val entries = N.lookups ctxt N.NFunction "GenericJointOwner::joint"
      val _ = require "both interpreted backends and one source serial survive merge"
        (length entries = 2 andalso length (distinct (op =) (map #serial entries)) = 1 andalso
          length (distinct (op =) (map (fastype_of o #hol_term) entries)) = 2)
      val result = run thy name (chunk
        ("fn JointNat(owner: GenericJointOwner<u8, " ^ hol "nat" ^ ">, value: bool) -> bool { " ^
          "GenericJointOwner::<u8, " ^ hol "nat" ^ ">::joint::<bool>(owner, value) }\n" ^
         "fn JointBool(owner: GenericJointOwner<u8, bool>, value: u8) -> u8 { owner.joint::<u8>(value) }"))
      val _ = require "both native selected interpretations elaborate after merge"
        (length (N.lookups (Toplevel.context_of result) N.NFunction "JointNat") = 1 andalso
          length (N.lookups (Toplevel.context_of result) N.NFunction "JointBool") = 1)
      val calls = Unsynchronized.ref 0
      val pos = Position.make0 1 1 0 "" name name
      val parameter: M.generic_parameter = {rust = "V", pos = pos,
        kind = URust_AST.Type_Parameter, hol = ("'joint_observed", \<^sort>\<open>type\<close>),
        bounds = [], report_reference = fn _ => calls := !calls + 1}
      val scoped = ctxt |> M.with_generic_scope {parameters = [parameter]}
        |> Variable.declare_typ (TFree (#hol parameter))
      val target = M.resolve_target_selection scoped (URust_Parser.parse_type_source scoped
        (Parser_Lex_Util.positioned_content_source
          ("GenericJointOwner<u8, " ^ hol "nat" ^ ">") pos))
      val instance: D.scoped_sparse_arguments = {instances = [{source = #serial (hd entries),
        target = SOME target, arguments = NONE, identities = []}], pending = SOME [("V", pos)], pos = pos}
      val occurrence = #self_type target --> TFree (#hol parameter) -->
        Type (\<^type_name>\<open>function_body\<close>,
          [\<^typ>\<open>unit\<close>, TFree (#hol parameter), \<^typ>\<open>unit\<close>,
            \<^typ>\<open>unit\<close>, \<^typ>\<open>unit\<close>])
      val (_, events) = M.capture_generic_use_events scoped (fn observed =>
        let val effects = D.filtered_candidates_with_scoped_generic_effects observed [] N.NFunction
          "GenericJointOwner::joint" occurrence NONE NONE NONE (SOME instance)
          val _ = require "unselected interpretation executes no original callback" (!calls = 0)
          val (_, commit) = the_single effects
        in commit () end)
      val _ = require "selected joint interpretation replays exact source/witness effects once"
        (!calls = 1 andalso #source_uses events = [fst (#hol parameter)] andalso
          #witness_uses events = [fst (#hol parameter)])
    in map #serial entries |> sort int_ord end
  val forward = check ("Generic_Joint_Merge_Forward", [natural, boolean])
  val reverse = check ("Generic_Joint_Merge_Reverse", [boolean, natural])
  val _ = require "both merge orders preserve the same canonical declaration serials"
    (forward = reverse)
in end
\<close>

section\<open> Concrete member arguments in mixed generic ownership \<close>

ML_val\<open>
local
  open Impl_Declaration_Test
  structure N = Micro_Rust_Names
  structure M = URust_Type_Mappings
  val base = \<^theory>
  fun run thy label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    run_commands false label thy (quiet text)) ()
  fun branch name parents text = Theory.begin_theory (name, Position.none) parents
    |> (fn thy => Toplevel.theory_of (run thy name text)) |> Theory.end_theory
  val parent = branch "Impl_Mixed_Dispatch_Parent" [base]
    ("urust_type [erase = " ^ cartouche "'left, 'right" ^
      "] \"MixedDispatchOwner<'left, 'right>\" = " ^ cartouche "unit")
  val generic = branch "Impl_Mixed_Dispatch_Generic" [parent] (chunk
    "impl<T> MixedDispatchOwner<T, bool> { fn pick(value: T) -> T { value } }")
  val concrete = branch "Impl_Mixed_Dispatch_Concrete" [parent] (chunk
    "impl MixedDispatchOwner<u8, u16> { fn pick<U>(value: U) -> U { value } }")
  val concrete_entry = the_single (N.lookups (Proof_Context.init_global concrete)
    N.NFunction "MixedDispatchOwner::pick")
  val generic_entry = the_single (N.lookups (Proof_Context.init_global generic)
    N.NFunction "MixedDispatchOwner::pick")
  val _ = require "concrete/generic owner declarations stay separate from local headers"
    (null (#parameters (the (M.scoped_owner (the
        (M.scoped_generic_scheme_for_source (Proof_Context.init_global concrete)
          (#serial concrete_entry)))))) andalso
      map #rust (#parameters (the (M.scoped_owner (the
        (M.scoped_generic_scheme_for_source (Proof_Context.init_global generic)
          (#serial generic_entry)))))) = ["T"])
  val _ = List.app (fn (label, parents) =>
    let
      val thy = Theory.begin_theory (label, Position.none) parents
      val selected = Toplevel.context_of (run thy (label ^ "-positive") (chunk
        "fn MixedSelectedConcrete(value: bool) -> bool { MixedDispatchOwner::<u8, u16>::pick::<bool>(value) }\n\
        \fn MixedSelectedGeneric(value: u8) -> u8 { MixedDispatchOwner::<u8, bool>::pick(value) }"))
      fun constants name = Term.add_const_names (Thm.prop_of
        (Proof_Context.get_thm selected (name ^ "_def"))) []
      val _ = require "selected concrete local arguments and inherited generic target pick their own backend"
        (exists (fn name => member (op =) (constants "mixed_selected_concrete") name)
            (Term.add_const_names (#hol_term concrete_entry) []) andalso
          exists (fn name => member (op =) (constants "mixed_selected_generic") name)
            (Term.add_const_names (#hol_term generic_entry) []))
      val wrong_kind = quiet (chunk
        "fn MixedWrongKind(value: u8) -> u8 { MixedDispatchOwner::<u8, u16>::pick::<3>(value) }")
      val _ = rejects_at (label ^ "-kind") ["wrong type or const kind"]
        (range_within wrong_kind "::pick::<3>" "3")
        (fn () => run_commands false (label ^ "-kind") thy wrong_kind)
      val contradiction = quiet (chunk
        "fn MixedTargetContradiction(value: bool) -> bool { MixedDispatchOwner::<u8, bool>::pick(value) }")
      val _ = expect_failure (label ^ "-target") ["no backend"]
        (fn () => run_commands false (label ^ "-target") thy contradiction)
    in () end)
    [("Impl_Mixed_Dispatch_Forward", [generic, concrete]),
     ("Impl_Mixed_Dispatch_Reverse", [concrete, generic])]
in end
\<close>

section\<open> Native equivalence and conservative retained ownership \<close>

ML_val\<open>
local
  structure N = Micro_Rust_Names
  fun require label condition = if condition then () else error ("impl native equivalence: " ^ label)
  val base = \<^theory>
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun hol text = "\<tau>" ^ cartouche text
  fun chunk text = "urust [verbosity = 0] " ^ cartouche text
  fun run thy label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
      (Toplevel.make_state (SOME thy))) ()
  fun branch name parents text = Theory.begin_theory (name, Position.none) parents
    |> (fn thy => Toplevel.theory_of (run thy name text)) |> Theory.end_theory
  val parent = branch "Impl_Equivalent_Parent" [base]
    ("urust_type \"ImplEquivalentByte\" = " ^ cartouche "8 word" ^ "\n" ^
     "urust_type \"ImplEquivalentList<'item>\" = " ^ cartouche "'item list" ^ "\n" ^
     "urust_type \"ImplEquivalentSequence<'item>\" = " ^ cartouche "'item list")
  fun concrete target result = chunk ("impl Duo<" ^ target ^
    "> { fn concrete_equivalent(value: " ^ result ^ ") -> " ^ result ^ " { value } }")
  val primitive = branch "Impl_Equivalent_Primitive" [parent] (concrete "u8" "u8")
  val escaped = branch "Impl_Equivalent_Escape" [parent] (concrete (hol "8 word") "u8")
  val mapped = branch "Impl_Equivalent_Mapping" [parent] (concrete "ImplEquivalentByte" "u8")
  val disjoint = branch "Impl_Equivalent_Disjoint" [parent] (concrete "u16" "u16")
  fun generic parameter target = chunk ("impl<" ^ parameter ^ "> Duo<" ^ target ^
    "> { fn retained_equivalent(value: " ^ parameter ^ ") -> " ^ parameter ^ " { value } }")
  val generic_list = branch "Impl_Equivalent_Generic_List" [parent]
    (generic "T" "ImplEquivalentList<T>")
  val generic_sequence = branch "Impl_Equivalent_Generic_Sequence" [parent]
    (generic "U" "ImplEquivalentSequence<U>")
  val concrete_list = branch "Impl_Equivalent_Concrete_List" [parent]
    (chunk ("impl Duo<" ^ hol "nat list" ^
      "> { fn retained_equivalent(value: " ^ hol "nat" ^ ") -> " ^ hol "nat" ^ " { value } }"))
  fun owner thy key = the_single (N.associated_template_functions (Proof_Context.init_global thy) key)
  val cases =
    [("primitive-escape", "Duo::concrete_equivalent", primitive, escaped),
     ("equal-rhs-mapping", "Duo::concrete_equivalent", primitive, mapped),
     ("generic-concrete", "Duo::retained_equivalent", generic_list, concrete_list),
     ("generic-generic", "Duo::retained_equivalent", generic_list, generic_sequence)]
  fun rejected label action =
    case Exn.capture0 action () of
      Exn.Exn (ERROR message) => require (label ^ ": overlap diagnostic")
        (String.isSubstring "overlapping Self types" message)
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error (label ^ ": equivalent native owners were admitted")
  fun reserve ({target, identity, pos, source_identity}:
      {target: N.target_template, identity: serial, pos: Position.T, source_identity: string option}) =
    N.reserve_associated_template_function
      {name = "ImplEquivalentOwner::probe", target = target, identity = identity,
       source_identity = source_identity, pos = pos}
  val _ = List.app (fn (label, key, left, right) =>
    let
      val first = owner left key
      val second = owner right key
      val _ = require (label ^ ": authoritative source-insensitive targets")
        (not (#requires_source_identity (#target first)) andalso
          not (#requires_source_identity (#target second)))
      val _ = require (label ^ ": native overlap in both orders")
        (N.overlapping_targets (#target first, #target second) andalso
          N.overlapping_targets (#target second, #target first))
      val context = Context.Proof \<^context>
      val _ = rejected (label ^ "-reserve-forward")
        (fn () => reserve second (reserve first context))
      val _ = rejected (label ^ "-reserve-reverse")
        (fn () => reserve first (reserve second context))
      val _ = rejected (label ^ "-merge-forward")
        (fn () => Theory.begin_theory ("Impl_Equivalent_" ^ label ^ "_Forward", Position.none)
          [left, right])
      val _ = rejected (label ^ "-merge-reverse")
        (fn () => Theory.begin_theory ("Impl_Equivalent_" ^ label ^ "_Reverse", Position.none)
          [right, left])
    in () end) cases
  val _ = List.app (fn parents =>
    let val merged = Theory.begin_theory ("Impl_Equivalent_Disjoint_Merge", Position.none) parents
    in require "native-disjoint concrete owners survive either merge order"
      (length (N.associated_template_functions (Proof_Context.init_global merged)
        "Duo::concrete_equivalent") = 2) end) [[primitive, disjoint], [disjoint, primitive]]
  val selected = Toplevel.context_of (run generic_list "Impl_Equivalent_Structural_Selection"
    (chunk ("fn EquivalentStructured(value: " ^ hol "nat" ^ ") -> " ^ hol "nat" ^
      " { Duo::<ImplEquivalentList<" ^ hol "nat" ^ ">>::retained_equivalent(value) }")))
  val _ = require "canonical retained generic structure selects its actual backend"
    (length (N.lookups selected N.NFunction "EquivalentStructured") = 1)
  val representation = Exn.capture0 (fn () => run generic_list "Impl_Equivalent_HOL_Selection"
    (chunk ("fn EquivalentRepresentation(value: " ^ hol "nat" ^ ") -> " ^ hol "nat" ^
      " { Duo::<" ^ hol "nat list" ^ ">::retained_equivalent(value) }"))) ()
  val _ = require "generic representation selection remains an explicit structural boundary"
    (case representation of Exn.Exn exn =>
      String.isSubstring "no associated function" (Runtime.exn_message exn) | _ => false)
in end
\<close>

section\<open> Grouped alias provenance with equal source arguments \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  open URust_AST
  val ctxt = \<^context>
  val pos = Position.make0 1 601 0 "" "s2-grouped-origins" "s2-grouped-origins"
  fun nominal (Group_Type (typ, _)) = nominal typ
    | nominal typ = typ
  fun check root nested =
    let
      val written = if nested then "((ImplDemandSwap<u8 /* \<alpha> first */, u8 /* second */>))"
        else "(ImplDemandSwap<u8 /* \<alpha> first */, u8 /* second */>)"
      val raw = Parser_Lex_Util.positioned_content_source written pos
      val argument = URust_Parser.parse_generic_argument_source ctxt raw
      val (group_pos, first_pos, second_pos) = case argument of Rust_Type_Argument group =>
        (case nominal group of Path_Type ([Rust_Type_Path_Segment (_, _, SOME
          [Rust_Type_Argument first, Rust_Type_Argument second], _)], _) =>
            (rust_type_position group, rust_type_position first, rust_type_position second)
         | _ => raise Fail "grouped alias syntax changed")
        | _ => raise Fail "grouped argument syntax changed"
      val arguments = [argument] @ (if root = "ImplLocalePair" then
        [Rust_Type_Argument (Primitive_Type (DPT_Bool, Position.none))] else [])
      val target = Path_Type ([Rust_Type_Path_Segment (root, pos, SOME arguments,
        make_source_layout pos [])], make_source_layout pos [])
      val selected = M.resolve_target_selection_with_inputs ctxt [(group_pos, raw)] target
      fun input path = the (AList.lookup (op =) (#inputs selected) path)
      val _ = if #1 (input [0]) = Input.string_of raw andalso
        Position.offset_of (#2 (input [0, 0])) = Position.offset_of second_pos andalso
        Position.offset_of (#2 (input [0, 1])) = Position.offset_of first_pos then ()
        else error "grouped equal canonical arguments lost distinct original subtree associations"
    in () end
  val _ = List.app (fn (root, nested) => check root nested)
    [("ImplDemandBox", false), ("ImplDemandBox", true),
     ("ImplLocalePair", false), ("ImplLocalePair", true)]
in end
\<close>


section\<open> Outlives impl scope, sparse schemes and native navigation \<close>

ML_val\<open>
local
  open Impl_Declaration_Test
  structure M = URust_Type_Mappings
  structure N = Micro_Rust_Names
  val ctxt = \<^context>
  val thy = \<^theory>
  val existing_capture = capture
  fun capture interactive label thy text =
    if is_some (Position.id_of (Position.thread_data ()))
    then existing_capture interactive label thy text
    else Position.setmp_thread_data (Position.make0 1 1 0 "" label label)
      (fn () => existing_capture interactive label thy text) ()
  fun source key = the_single (N.lookups ctxt N.NFunction key)
  fun scheme key = the (M.scoped_generic_scheme_for_source ctxt (#serial (source key)))
  val carry = scheme "OutlivesPocket::carry"
  val owner = the (M.scoped_owner carry)
  val _ = require "outlives preserve separate ordered owner and local member schemes"
    (map #rust (#parameters owner) = ["T"] andalso
      map #rust (M.scoped_parameters carry) = ["U"] andalso
      forall (null o #bounds) (#parameters owner @ M.scoped_parameters carry))
  val ordered = the_single (#parameters (the (M.scoped_owner (scheme "OutlivesMixedOwner::ordered"))))
  val sibling_parameter = the_single (#parameters (the (M.scoped_owner (scheme "OutlivesMixedOwner::sibling"))))
  val _ = require "mixed inherited trait/outlives refinement strengthens only the selected member"
    (#sort ordered = \<^sort>\<open>ord\<close> andalso #bounds ordered = ["impl_scope::Ordered"] andalso
      #sort sibling_parameter = \<^sort>\<open>type\<close> andalso null (#bounds sibling_parameter))
  val erased = the (M.scoped_owner (scheme "OutlivesErasedBox::irrelevant"))
  val forwarded = the (M.scoped_owner (scheme "OutlivesErasedBox::source_forward"))
  val _ = require "erased heads add no member witness, role, slot, or source-use bit"
    (map #hol (#parameters erased) = [NONE] andalso
      map #source_used (#parameters erased) = [SOME false] andalso
      map #hol (#parameters forwarded) = [NONE] andalso
      #parameters erased = #parameters (the (M.scoped_owner (scheme "ImplDemandBox::irrelevant"))) andalso
      #parameters forwarded = #parameters (the (M.scoped_owner (scheme "ImplDemandBox::source_forward"))) andalso
      null (M.scoped_parameters (scheme "OutlivesErasedBox::source_forward")))
  val _ = List.app (fn (actual, plain) => require "outlives impl complete native constant type twin"
    (Sign.the_const_type thy actual = Sign.the_const_type thy plain))
    [(\<^const_name>\<open>outlives_pocket_carry\<close>, \<^const_name>\<open>outlives_pocket_carry_plain\<close>),
     (\<^const_name>\<open>outlives_erased_box_source_forward\<close>,
      \<^const_name>\<open>outlives_erased_forward_plain\<close>)]
  fun selection index =
    let
      val inherited = TVar (("outlives_owner", index), \<^sort>\<open>type\<close>)
      val local_parameter = TVar (("outlives_member", index + 1), \<^sort>\<open>type\<close>)
      val address = TVar (("outlives_address", index + 2), \<^sort>\<open>type\<close>)
      val global = TVar (("outlives_global", index + 3), \<^sort>\<open>type\<close>)
      val [state, abort, input, output] = map (fn offset =>
        TVar (("outlives_channel", index + offset), \<^sort>\<open>type\<close>)) [4, 5, 6, 7]
      val owner = Type (\<^type_name>\<open>outlives_pocket\<close>, [inherited])
      fun reference target = Term.typ_subst_atomic
        [(\<^typ>\<open>'address\<close>, address), (\<^typ>\<open>'global\<close>, global),
         (\<^typ>\<open>'target\<close>, target)]
        \<^typ>\<open>('address, 'global, 'target) Global_Store.ref\<close>
      val occurrence = reference owner --> reference local_parameter -->
        Type (\<^type_name>\<open>function_body\<close>, [state, reference local_parameter, abort, input, output])
      val target: N.target_selection = {self_type = owner,
        source = SOME (N.Source_Node (N.Mapped_Source "OutlivesPocket",
          [N.Source_HOL (N.Type_Source, inherited)])), source_identity = NONE,
        evidence = [([0], inherited)], inputs = [], pos = Position.none}
      val arguments: Micro_Rust_Dispatch.scoped_sparse_arguments =
        {instances = [{source = #serial (source "OutlivesPocket::carry"),
          target = SOME target, arguments = SOME [(SOME local_parameter, Position.none)], identities = [""]}],
         pending = NONE, pos = Position.none}
      val [(candidate, _)] = Micro_Rust_Dispatch.filtered_candidates_with_scoped_generic_effects ctxt []
        N.NFunction "OutlivesPocket::carry" occurrence NONE NONE NONE (SOME arguments)
      val backend = case Term_Position.strip_positions (#term candidate) of
        Const ("_type_constraint_", _) $ term => term | term => term
      val expected = Const (\<^const_name>\<open>outlives_pocket_carry\<close>, occurrence)
      val _ = require "outlives selection shares exact inherited/local/reference and outer channel variables"
        (backend aconv expected)
    in Term.add_tvars backend [] end
  val first = selection 9017
  val second = selection 12017
  val _ = require "successive outlives owner/member selections freshen independently"
    (null (inter (op =) first second))
  val transported = N.lookups ctxt N.NFunction "OutlivesLocalePair::replace"
  val _ = require "outlives locale transports retain one source serial and both native ambient types"
    (length transported = 2 andalso length (distinct (op =) (map #serial transported)) = 1 andalso
      length (distinct (op =) (map (fastype_of o #hol_term) transported)) = 2 andalso
      forall (fn backend => is_some (M.scoped_generic_scheme_for_source ctxt (#serial backend)))
        transported)

  val prefix = "/* " ^ Symbol.open_ ^ " navigation " ^ Symbol.close ^ " */ "
  val raw = prefix ^ "struct OutlivesNavigationOwner<T> { value: T }\n" ^
    "impl<'a: 'b, 'b: 'a, T: 'b> OutlivesNavigationOwner<T> " ^
    "where Self: 'static, &'a Self: 'b {\n" ^
    "fn first<'c: 'a, U: 'c>(&'a mut self, value: &'c mut U) -> &'c mut U where T: 'c { value }\n" ^
    "fn second<'c: 'b>() where 'a: 'c {}\n}"
  val text = quiet (chunk raw)
  val {result, reports, ...} = capture true "outlives-impl-navigation" thy text
  val completed = result_context result
  fun definitions token occurrence kind =
    entity_ids_at (range_of text token occurrence) kind true reports
  fun references token occurrence kind =
    entity_ids_at (range_of text token occurrence) kind false reports
  val a = the_single (definitions "'a" 0 "urust_lifetime")
  val b = the_single (definitions "'b" 1 "urust_lifetime")
  val c = the_single (definitions "'c" 0 "urust_lifetime")
  val sibling = the_single (definitions "'c" 5 "urust_lifetime")
  val _ = require "impl and member lifetime declarations have distinct native identities"
    (length (distinct (op =) [a, b, c, sibling]) = 4)
  val _ = List.app (fn occurrence => require "impl lifetime references preserve the original declaration ID"
    (references "'a" occurrence "urust_lifetime" = [a])) [1, 2, 3, 4, 5]
  val _ = List.app (fn occurrence => require "forward/cyclic impl bounds use the exact later declaration"
    (references "'b" occurrence "urust_lifetime" = [b])) [0, 2, 3, 4]
  val _ = List.app (fn occurrence => require "member local bounds and signature use the exact local ID"
    (references "'c" occurrence "urust_lifetime" = [c])) [1, 2, 3, 4]
  val _ = require "sibling local bound uses its own fresh declaration"
    (references "'c" 6 "urust_lifetime" = [sibling])
  val target_id = definitions "OutlivesNavigationOwner" 0 "micro_rust_type_mapping"
  val _ = require "checked Self predicate navigation uses the single actual target mapping"
    (length target_id = 1 andalso
      references "Self" 0 "micro_rust_type_mapping" = target_id andalso
      references "Self" 1 "micro_rust_type_mapping" = target_id)
  val _ = List.app (fn occurrence => require "erased Self has lexical keyword markup without HOL typing"
    (exists (fn (role, _) => role = Markup.keyword3N)
      (texts_at (range_of text "Self" occurrence) reports) andalso
      not (exists (fn (role, _) => role = Markup.typingN)
        (texts_at (range_of text "Self" occurrence) reports)))) [0, 1]
  val _ = require "impl outlives closes all generic/Self state"
    (is_none (M.generic_scope completed) andalso is_none (M.impl_self completed) andalso
      is_none (M.generic_scope_identities completed))
  val _ = writeln "S3 impl/member masks, exact channels, locale source identity and checked Self/lifetime native navigation PASS"
in end
\<close>

ML_val\<open>
local
  open Impl_Declaration_Test
  structure M = URust_Type_Mappings
  val thy = \<^theory>
  val ctxt = \<^context>
  val existing_capture = capture
  fun capture interactive label thy text =
    if is_some (Position.id_of (Position.thread_data ()))
    then existing_capture interactive label thy text
    else Position.setmp_thread_data (Position.make0 1 1 0 "" label label)
      (fn () => existing_capture interactive label thy text) ()
  val before_state = registry_snapshot ctxt
  val callbacks = (!Private_Output.writeln_fn, !Private_Output.writeln_urgent_fn,
    !Private_Output.warning_fn, !Private_Output.report_fn)
  val rows =
    [("impl-unknown-bound", "undeclared lifetime", "impl<'a: 'missing, T> GenericPocket<T> {}", "'missing", 0),
     ("member-unknown-bound", "undeclared lifetime",
      "impl<'a, T> GenericPocket<T> { fn early() {} fn late<'b: 'missing>() {} }", "'missing", 0),
     ("member-local-leak", "undeclared lifetime",
      "impl<'a, T> GenericPocket<T> { fn early<'b: 'a>() {} fn late() where T: 'b {} }", "'b", 1),
     ("member-placeholder", "placeholder lifetime",
      "impl<'a, T> GenericPocket<T> { fn early() {} fn late() where T: '_ {} }", "'_", 0),
     ("member-const-head", "const parameters cannot be used as type where heads",
      "impl<const N: usize> GenericBuffer<u8, N> { fn early() {} fn late() where N: 'static {} }", "N", 2),
     ("member-type-length", "type parameters cannot be used as const where operands",
      "impl<T> GenericPocket<T> { fn early() {} fn late() where [u8; T]: 'static {} }", "T", 2),
     ("impl-self-projection", "associated paths on scoped parameters",
      "impl<T> GenericPocket<T> where Self::Item: 'static {}", "Self", 0),
     ("free-self", "Self is only available inside an impl",
      "fn OutlivesFree(value: u8) -> u8 where Self: 'static { value }", "Self", 0),
     ("impl-target-self", "Self is only available inside an impl", "impl Self {}", "Self", 0),
     ("member-body-only", "does not occur in the signature",
      "impl<'a, T> OutlivesErasedBox<T> { fn late(value: u8) -> u8 where T: 'a { let spare = \<llangle>undefined :: 't\<rrangle>; value } }", "T", 0)]
  val _ = List.app (fn (label, expected, raw, token, occurrence) =>
    let
      val text = quiet (chunk raw)
      val {result, output, reports, ...} = capture true label thy text
      val diagnostic = (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": original positioned error: " ^ diagnostic)
        (String.isSubstring expected diagnostic andalso
          position_range (hd (message_positions diagnostic)) = range_of text token occurrence)
      val _ = require (label ^ ": report transaction leaked a successful member or declaration")
        (null output andalso not (exists (fn (name, props) => name = Markup.entityN andalso
          is_some (Properties.get props Markup.defN) andalso
          Properties.get props Markup.kindN <> SOME "urust_var")
          (fold Parser_Test_Reports.collect_markup reports [])))
      val (w, u, n, r) = callbacks
      val _ = require (label ^ ": failed impl changed callback objects or the caller registry")
        (registry_snapshot ctxt = before_state andalso PolyML.pointerEq (w, !Private_Output.writeln_fn) andalso
          PolyML.pointerEq (u, !Private_Output.writeln_urgent_fn) andalso
          PolyML.pointerEq (n, !Private_Output.warning_fn) andalso
          PolyML.pointerEq (r, !Private_Output.report_fn))
      val recovered = context_after (label ^ "-recovery") thy (quiet (chunk
        "impl<'a, 'b: 'a, T: 'b> GenericPocket<T> { fn outlives_recovery(value: u8) -> u8 where T: 'static { value } }"))
      val _ = require "failed outlives impl recovers with an isolated checked member"
        (not (null (entries recovered "GenericPocket::outlives_recovery")) andalso
          is_none (M.generic_scope recovered) andalso is_none (M.impl_self recovered))
    in () end) rows
  val _ = writeln "S3 impl-header Self boundaries, inherited kinds, member isolation/body availability, atomic reports and recovery PASS"
in end
\<close>

section\<open> Bounded locale schemes in both theory merge orders \<close>

ML_val\<open>
local
  structure N = Micro_Rust_Names
  structure M = URust_Type_Mappings
  fun require label condition = if condition then () else error ("outlives merge: " ^ label)
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun hol text = "\<tau>" ^ cartouche text
  fun chunk text = "urust [verbosity = 0] " ^ cartouche text
  fun run thy label text = Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
    fold (Toplevel.command_exception false)
      (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
      (Toplevel.make_state (SOME thy))) ()
  fun branch name parents text = Theory.begin_theory (name, Position.none) parents
    |> (fn thy => Toplevel.theory_of (run thy name text)) |> Theory.end_theory
  val parent = branch "Outlives_Merge_Parent" [\<^theory>]
    ("urust_type \"OutlivesMergeOwner<'payload, 'ambient>\" = " ^ cartouche " 'payload * 'ambient " ^
      "\nlocale outlives_merge_locale = fixes seed :: 'ambient\nbegin\n" ^
      chunk ("impl<'a, T: 'a> OutlivesMergeOwner<T, " ^ hol "'ambient" ^
        "> where Self: 'static { fn joint<'b: 'a, U: 'b>(self, value: U) -> U where T: 'b { let spare = seed; value } }") ^
      "\nend")
  val natural = branch "Outlives_Merge_Nat" [parent]
    ("interpretation outlives_merge_nat: outlives_merge_locale " ^ cartouche "0 :: nat" ^ " .")
  val boolean = branch "Outlives_Merge_Bool" [parent]
    "interpretation outlives_merge_bool: outlives_merge_locale False ."
  fun check (name, parents) =
    let val thy = Theory.begin_theory (name, Position.none) parents
      val ctxt = Proof_Context.init_global thy
      val entries = N.lookups ctxt N.NFunction "OutlivesMergeOwner::joint"
      val _ = require "both native ambient types retain one declaration in either merge order"
        (length entries = 2 andalso length (distinct (op =) (map #serial entries)) = 1 andalso
          length (distinct (op =) (map (fastype_of o #hol_term) entries)) = 2)
      val result = run thy name (chunk
        ("fn OutlivesMergeNat(owner: OutlivesMergeOwner<u8, " ^ hol "nat" ^ ">, value: bool) -> bool { " ^
          "OutlivesMergeOwner::<u8, " ^ hol "nat" ^ ">::joint::<bool>(owner, value) }\n" ^
         "fn OutlivesMergeBool(owner: OutlivesMergeOwner<u8, bool>, value: u8) -> u8 { owner.joint::<u8>(value) }"))
      val _ = require "selected bounded locale calls remain available after merge"
        (length (N.lookups (Toplevel.context_of result) N.NFunction "OutlivesMergeNat") = 1 andalso
          length (N.lookups (Toplevel.context_of result) N.NFunction "OutlivesMergeBool") = 1 andalso
          is_none (M.generic_scope (Toplevel.context_of result)))
    in map #serial entries |> sort int_ord end
  val forward = check ("Outlives_Merge_Forward", [natural, boolean])
  val reverse = check ("Outlives_Merge_Reverse", [boolean, natural])
  val _ = require "canonical declaration identities survive both bounded locale merge orders" (forward = reverse)
  val _ = writeln "S3 bounded locale/morphism schemes and native selection in both theory merge orders PASS"
in end
\<close>


section\<open> Scoped Self conflicts and option positions \<close>

ML_val\<open>
local
  open Impl_Syntax_Test
  val thy = \<^theory>
  fun representation key typ = "[\"" ^ key ^ "\" \<rightarrow> " ^ cartouche typ ^ "]"
  val block = "impl ScopedOwner {\n" ^
    "  fn earlier(self: Self) -> bool { false }\n" ^
    "  \<omega>" ^ cartouche ("model_parameters = " ^ representation "address" "int") ^ "\n" ^
    "  fn conflict(self: Self, pointer: *const u8) -> bool { false }\n}"
  val annotation = "\<omega>" ^ cartouche ("model_parameters = [\"address\" \<rightarrow> " ^ cartouche "nat" ^
    ", \"global\" \<rightarrow> " ^ cartouche "unit" ^
    ", \"epoch\" \<rightarrow> " ^ cartouche "bool" ^ "]")
  val command = "urust " ^ command_source (annotation ^ "\n" ^ block)
  val _ = ignore (expect_failure "scoped Self conflict" ["conflicts with checked Self"]
    (fn () => run_commands false "scoped-self-conflict" thy command))
  fun unrelated_hole hole =
    "urust_type [implicit = " ^ cartouche "address = 'a" ^
      "] \"ScopedUnrelatedHoleOwner<'value>\" = " ^ cartouche "'a option * 'value" ^ "\n" ^
    "urust " ^ command_source
      ("\<omega>" ^ cartouche ("model_parameters = " ^ representation "address" "_ option") ^
       "\nimpl ScopedUnrelatedHoleOwner<\<tau>" ^ cartouche hole ^
       "> { fn ignored(self: Self) -> bool { false } }")
  val _ = List.app (fn hole =>
    ignore (expect_failure "unrelated scoped impl hole"
      ["an impl target must not contain inference holes"]
      (fn () => run_commands false "scoped-unrelated-hole" thy (unrelated_hole hole))))
    ["_", "_ option"]
  val recovered = run_commands false "scoped-self-recovery" thy
    ("urust_fn _ " ^ cartouche "fn ScopedRecovery(value: bool) -> bool { value }")
  val _ = require "failed scoped impl changed the original theory"
    (is_none (Parser_Test_Calls.lookup (Toplevel.context_of recovered) "ScopedOwner::earlier") andalso
     is_none (URust_Type_Mappings.lookup (Toplevel.context_of recovered) "ScopedUnrelatedHoleOwner"))
in val _ = writeln "scoped Self conflict and subsequent recovery PASS" end
\<close>

section\<open> Shared callable policy inheritance \<close>

ML_val\<open>
local
  open Impl_Syntax_Test
  val thy = \<^theory>
  fun policy key mode = "shared_references = [" ^ quote key ^ " \<rightarrow> " ^ cartouche mode ^ "]"
  fun annotation options = "\<omega>" ^ cartouche options ^ "\n"
  fun command text = "urust " ^ command_source text
  val header = annotation (policy "type:T" "value") ^
    "impl<T, U, F: Fn(&T) -> &T> SharedCallableOwner<T, U, F> {\n"
  val _ = command_rejects thy "shared-impl-slot-key"
    ["impl shared_references accepts only type:NAME keys"]
    (command (annotation (policy "arg:0" "value") ^
      "impl<T, U, F> SharedCallableOwner<T, U, F> {}")) "arg:0" 0
  val conflict = command (header ^ annotation (policy "type:T" "reference") ^
    "fn conflict(self: Self) -> bool where F: Fn(&T) -> &T { false }\n}")
  val message = expect_failure "shared impl member recipe conflict"
    ["incompatible callable bounds with different checked native types",
     "shared-impl-conflicting-member-bound"]
    (fn () => run_commands false "shared-impl-conflicting-member-bound" thy conflict)
  val _ = require "conflicting member recipe lost its bound positions"
    (range_of conflict "Fn" 0 = message_range message andalso
      exists (fn pos => position_range pos = range_of conflict "Fn" 1) (message_positions message))
  fun canonical typ = Term_Subst.instantiateT (TVars.make
    (rev (Term.add_tvarsT typ []) |> map_index
      (fn (index, variable as (_, sort)) => (variable, TVar (("shared_impl_twin", index), sort))))) typ
  fun constant_type name = canonical (Sign.the_const_type thy (Proof_Context.intern_const \<^context> name))
  val _ = List.app (fn (native, escaped) =>
    require (native ^ ": principal type, sorts or sharing changed")
      (constant_type native = constant_type escaped))
    [("shared_callable_owner_keep", "shared_callable_owner_keep_escape"),
     ("shared_callable_owner_readonly_other", "shared_callable_owner_readonly_escape"),
     ("shared_callable_owner_ordinary_again", "shared_callable_owner_reference_escape"),
     ("shared_callable_owner_slot_other", "shared_callable_owner_slot_escape"),
     ("shared_callable_owner_ordinary_after_slot", "shared_callable_owner_reference_escape"),
     ("shared_nominal_callable_owner_keep", "shared_nominal_callable_owner_keep_escape")]
in val _ = writeln "shared impl header policies, partial overrides and member isolation PASS" end
\<close>

ML_val\<open>
local
  val thy = \<^theory>
  fun cartouche text = Symbol.open_ ^ "\n" ^ text ^ "\n" ^ Symbol.close
  fun run label text = fold (Toplevel.command_exception false)
    (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label) text)
    (Toplevel.make_state (SOME thy)) |> Toplevel.context_of
  fun annotation options = "\<omega>" ^ cartouche options ^ "\n"
  fun policy mode = "shared_references = [\"type:T\" \<rightarrow> " ^ cartouche mode ^ "]"
  fun inspect mode =
    let
      val ctxt = run ("shared-callable-inferred-" ^ mode) ("urust " ^ cartouche
        ("struct SharedInferredCallableOwner<T, F> { value: T, callback: F }\n" ^
         annotation (policy mode) ^
         "impl<T, F: Fn(&T) -> &T> SharedInferredCallableOwner<T, F> {\n" ^
         "fn weak(self: Self, value: &T) -> bool { false }\n}"))
      val typ = Sign.the_const_type (Proof_Context.theory_of ctxt)
        (Proof_Context.intern_const ctxt "shared_inferred_callable_owner_weak")
      val [Type (_, [_, Type ("fun", [input, _])]), value] = binder_types typ
    in writeln (mode ^ ": " ^ ML_Syntax.print_typ typ);
       if input = value then writeln "inferred roles shared PASS"
       else error "inferred roles lost" end
  val _ = List.app inspect ["reference", "readonly"]
  val conflict = "urust " ^ cartouche
    ("struct SharedBoundCallableOwner<T, F> { value: T, callback: F }\n" ^
     annotation (policy "reference" ^
       ", model_parameters = [\"address\" \<rightarrow> " ^ cartouche "nat" ^
       ", \"global\" \<rightarrow> " ^ cartouche "unit" ^ "]") ^
     "impl<T, F: Fn(&T) -> &T> SharedBoundCallableOwner<T, F> {\n" ^
     annotation ("model_parameters = [\"address\" \<rightarrow> " ^ cartouche "bool" ^ "]") ^
     "fn weak(self: Self, value: &T) -> bool { false }\n}")
  val _ = case Exn.capture0 (fn () => run "shared-callable-header-role-conflict" conflict) () of
      Exn.Res ctxt => error ("conflicting header role accepted: " ^
        ML_Syntax.print_typ (Sign.the_const_type (Proof_Context.theory_of ctxt)
          (Proof_Context.intern_const ctxt "shared_bound_callable_owner_weak")))
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
        else if String.isSubstring "conflicts with checked Self" (Runtime.exn_message exn) then ()
        else Exn.reraise exn
in end
\<close>

ML_val\<open>
local
  val thy = \<^theory>
  fun cartouche text = Symbol.open_ ^ "\n" ^ text ^ "\n" ^ Symbol.close
  fun run label text = fold (Toplevel.command_exception false)
    (Outer_Syntax.parse_text thy (K thy) (Position.make0 1 1 0 "" label label)
      ("declare [[urust_verbosity = 0]]\n" ^ text))
    (Toplevel.make_state (SOME thy)) |> Toplevel.context_of
  fun typ ctxt name = Sign.the_const_type (Proof_Context.theory_of ctxt)
    (Proof_Context.intern_const ctxt name)
  fun require label ok = if ok then () else error label
  val retained = run "shared-nested-impl-frame" ("urust " ^ cartouche
    "struct SharedNestedRoleOwner<T> { value: T }\n\
    \impl<'a> SharedNestedRoleOwner<&'a mut u8> {\n\
    \  fn weak(self: Self, pointer: *const u8) -> bool { false }\n}")
  val [Type (_, [nested]), pointer] = binder_types (typ retained "shared_nested_role_owner_weak")
  val _ = require "retained nested impl argument did not share member roles" (nested = pointer)
  fun annotation options = "\<omega>" ^ cartouche options ^ "\n"
  val erased_command =
    "urust_type [erase = " ^ cartouche "'f" ^ "] \"SharedErasedRoleOwner<'t, 'f>\" = " ^
    cartouche "'t option" ^ "\nurust " ^ cartouche
      (annotation ("shared_references = [\"type:T\" \<rightarrow> " ^ cartouche "reference" ^
         "], model_parameters = [\"address\" \<rightarrow> " ^ cartouche "nat" ^
         ", \"global\" \<rightarrow> " ^ cartouche "unit" ^ "]") ^
       "impl<T, F: Fn(&T) -> &T> SharedErasedRoleOwner<T, F> {\n\
       \  fn weak(self: Self, value: &T) -> bool { false }\n}\n") ^
    "\nurust_fn " ^ cartouche "fn SharedAfterImpl(pointer: *const u8) -> bool { false }"
  val erased = run "shared-erased-impl-frame" erased_command
  val [Type (_, [element]), value] = binder_types (typ erased "shared_erased_role_owner_weak")
  val expected = Term.typ_subst_atomic [(TFree ("'element", \<^sort>\<open>type\<close>), element)]
    \<^typ>\<open>(nat, unit, 'element) ref\<close>
  val _ = require "roles established only by erased callable evidence were lost" (value = expected)
  val later = the_single (binder_types (typ erased "shared_after_impl"))
  val _ = require "checked header roles escaped into a later free function"
    (length (Term.add_tvarsT later []) = 2)
in val _ = writeln "retained arguments, erased callable roles and impl-context exit PASS" end
\<close>


section\<open> Shared navigation and checked-header recovery \<close>

ML_val\<open>
local
  open Chunk_Test
  val thy = \<^theory>
  val declaration = "urust_type [shared = " ^ cartouche "value" ^
    "] \"SharedReportFlag\" = " ^ cartouche "bool"
  val read_declarations =
    "\nurust_type [shared = " ^ cartouche "reference" ^
      "] \"SharedReportStorageFlag\" = " ^ cartouche "bool" ^
    "\nurust_type [shared = " ^ cartouche "readonly" ^
      "] \"SharedReportReadonlyFlag\" = " ^ cartouche "bool"
  val success = declaration ^ read_declarations ^ "\nurust_fn [pp_test] " ^ command_source
    "fn SharedReportIdentity<'a>(value: &'a SharedReportFlag) -> &'a SharedReportFlag { value }"
  val {result, reports, ...} = capture true "shared-native-reports" thy success
  val success_ctxt = result_context result
  fun events (XML.Elem ((name, properties), body)) =
        (name, properties, XML.content_of body) :: maps events body
    | events (XML.Text _) = []
  val all = maps events reports
  val range = range_of success "&'a SharedReportFlag" 0
  val _ = require "shared borrow lost positioned policy tooltip"
    (exists (fn (name, properties, body) => name = Markup.typingN andalso
      position_range (Position.of_properties properties) = range andalso
      String.isSubstring "shared representation = value" body andalso
      String.isSubstring "shared-native-reports" body) all)
  val _ = require "shared nominal borrow lost native mapping reference"
    (exists (fn (name, properties, _) => name = Markup.entityN andalso
      position_range (Position.of_properties properties) = range andalso
      Properties.get properties Markup.kindN = SOME "micro_rust_type_mapping" andalso
      is_some (Properties.get properties Markup.refN)) all)
  val _ = require "policy payload lost native semantic markup"
    (exists (fn (name, properties, _) => name = (fst Markup.keyword2) andalso
      position_range (Position.of_properties properties) = range_of success "value" 0) all)
  val base = Proof_Context.theory_of success_ctxt
  fun policy key mode = "shared_references = [" ^ quote key ^ " \<rightarrow> " ^ cartouche mode ^ "]"
  val generic = "urust_fn [pp_test, " ^ policy "type:T" "readonly" ^ "] " ^ command_source
    "fn SharedReportGeneric<T>(value: &T) -> bool { false }"
  val {result = generic_result, reports = generic_reports, ...} =
    capture true "shared-generic-native-reports" base generic
  val _ = result_context generic_result
  fun entity_ids range definition = reports_at range generic_reports |> map_filter
    (fn (name, properties) => if name = Markup.entityN andalso
      Properties.get properties Markup.kindN = SOME "urust_generic_parameter"
    then Properties.get properties (if definition then Markup.defN else Markup.refN) else NONE)
  val definitions = entity_ids (range_within generic "<T>" "T") true
  val references = entity_ids (range_of generic "type:T" 0) false
  val _ = require "generic override key did not reference the exact header declaration"
    (length definitions = 1 andalso references = definitions)
  val _ = require "generic borrow lost exact selected-policy tooltip"
    (exists (fn (name, properties, body) => name = Markup.typingN andalso
      position_range (Position.of_properties properties) = range_of generic "&T" 0 andalso
      String.isSubstring "shared representation = readonly" body andalso
      String.isSubstring "shared-generic-native-reports" body) (maps events generic_reports))
  fun rejected label expected text = expect_failure label [expected]
    (fn () => run_commands false label base text)
  fun rejected_command options = "urust_fn [" ^ options ^ "] " ^ command_source
    "fn SharedReportRejected(value: &SharedReportFlag) -> bool { false }"
  val bad_key = rejected_command (policy "body" "value")
  val _ = require "invalid shared key lost its exact authored range"
    (message_range (rejected "shared-bad-key-range" "unknown shared-reference key" bad_key) =
      range_of bad_key "body" 0)
  val bad_mode = rejected_command (policy "arg:0" "implicit")
  val _ = require "invalid shared mode lost its exact authored range"
    (message_range (rejected "shared-bad-mode-range" "expects value, reference, or readonly" bad_mode) =
      range_of bad_mode "implicit" 0)
  val duplicate = rejected_command ("shared_references = [\"arg:0\" \<rightarrow> " ^ cartouche "value" ^
    ", \"arg:0\" \<rightarrow> " ^ cartouche "readonly" ^ "]")
  val duplicate_message = rejected "shared-duplicate-author-ranges" "duplicate shared-reference override" duplicate
  val _ = require "duplicate override lost an author's source range"
    (message_range duplicate_message = range_of duplicate "arg:0" 1 andalso
      forall (fn range => exists (fn pos => position_range pos = range)
        (message_positions duplicate_message))
      [range_of duplicate "arg:0" 0, range_of duplicate "arg:0" 1])
  fun annotation options = "\<omega>" ^ cartouche options ^ "\n"
  val header = "struct SharedReportOwner<T, F> { value: T, callback: F }\n" ^
    annotation (policy "type:T" "reference" ^
      ", model_parameters = [\"address\" \<rightarrow> " ^ cartouche "nat" ^
      ", \"global\" \<rightarrow> " ^ cartouche "unit" ^ "]") ^
    "impl<T, F: Fn(&T) -> &T> SharedReportOwner<T, F> {\n"
  val failed = "urust [pp_test] " ^ command_source (header ^
    "fn earlier(self: Self, value: &T, pointer: &mut u8) -> bool { false }\n\
    \fn invalid(self: Self, value: &bool) -> bool { false }\n}")
  val callbacks = (!Private_Output.writeln_fn, !Private_Output.writeln_urgent_fn,
    !Private_Output.warning_fn, !Private_Output.report_fn)
  val {result = rejected_result, output, reports = rejected_reports, ...} =
    capture true "shared-report-rollback" base failed
  val message = failure_message "shared failed later member" ["require an explicit representation"] rejected_result
  val _ = require "missing policy diagnostic lost exact borrow range"
    (message_range message = range_of failed "&bool" 0)
  val _ = require "failed later shared member emitted successful declarations"
    (null output andalso null (semantic_entities rejected_reports) andalso
      not (exists (fn (name, properties) => name = Markup.entityN andalso
        member (op =) [SOME "urust_generic_parameter", SOME "urust_lifetime"]
          (Properties.get properties Markup.kindN)) (report_events rejected_reports)))
  val (w, u, n, r) = callbacks
  val _ = require "failed shared impl changed callback objects"
    (PolyML.pointerEq (w, !Private_Output.writeln_fn) andalso
      PolyML.pointerEq (u, !Private_Output.writeln_urgent_fn) andalso
      PolyML.pointerEq (n, !Private_Output.warning_fn) andalso
      PolyML.pointerEq (r, !Private_Output.report_fn))
  val recovered = run_commands false "shared-report-recovery" base
    ("urust [pp_test] " ^ command_source (header ^
      "fn recovered(self: Self, value: &T, pointer: &mut u8) -> bool { false }\n}") ^
      "\nurust_fn [pp_test] " ^ command_source "fn SharedAfterReport(pointer: *const u8) -> bool { false }")
  val recovered_ctxt = Toplevel.context_of recovered
  val _ = require "shared recovery failed or retained an abandoned member"
    (not (null (Micro_Rust_Names.lookups recovered_ctxt Micro_Rust_Names.NFunction
        "SharedReportOwner::recovered")) andalso
      null (Micro_Rust_Names.lookups recovered_ctxt Micro_Rust_Names.NFunction "SharedReportOwner::earlier") andalso
      is_none (URust_Type_Mappings.generic_scope recovered_ctxt) andalso
      is_none (URust_Type_Mappings.impl_self recovered_ctxt))
  val later_type = Sign.the_const_type (Proof_Context.theory_of recovered_ctxt)
    (Proof_Context.intern_const recovered_ctxt "shared_after_report")
  val _ = require "successful or failed impl left a backend ledger in a subsequent free item"
    (length (Term.add_tvarsT (the_single (binder_types later_type)) []) = 2)
  val partial = run_commands false "shared-header-partial-model-overlay" base
    ("urust " ^ command_source
      ("struct SharedReportPartial<T> { value: T }\n" ^
       annotation ("model_parameters = [\"address\" \<rightarrow> " ^ cartouche "nat" ^
         ", \"global\" \<rightarrow> " ^ cartouche "unit" ^ "]") ^
       "impl<T> SharedReportPartial<T> {\n" ^
       annotation ("model_parameters = [\"global\" \<rightarrow> " ^ cartouche "bool" ^ "]") ^
       "fn overlay(self: Self, pointer: &mut u8) -> bool { false }\n\
       \fn inherited(self: Self, pointer: &mut u8) -> bool { false }\n}"))
  val partial_ctxt = Toplevel.context_of partial
  fun declared current name = Sign.the_const_type (Proof_Context.theory_of current)
    (Proof_Context.intern_const current name)
  val _ = require "partial member model overlay lost header address or leaked to the next member"
    (nth (binder_types (declared partial_ctxt "shared_report_partial_overlay")) 1 =
        \<^typ>\<open>(nat, bool, 8 word) ref\<close> andalso
      nth (binder_types (declared partial_ctxt "shared_report_partial_inherited")) 1 =
        \<^typ>\<open>(nat, unit, 8 word) ref\<close>)
  val nested = run_commands false "shared-header-nested-model-holes" base
    ("urust " ^ command_source
      ("struct SharedReportHoles<T, F> { value: T, callback: F }\n" ^
       annotation (policy "type:T" "reference" ^
         ", model_parameters = [\"address\" \<rightarrow> " ^ cartouche "_ option" ^
         ", \"global\" \<rightarrow> " ^ cartouche "_ list" ^ "]") ^
       "impl<T, F: Fn(&T) -> &T> SharedReportHoles<T, F> {\n\
       \fn first(self: Self, value: &T, pointer: &mut u8) -> bool { false }\n\
       \fn second(self: Self, value: &T, pointer: &mut u8) -> bool { false }\n}"))
  val nested_ctxt = Toplevel.context_of nested
  fun check_nested name =
    let
      val [Type (_, [_, callback]), value, pointer] = binder_types (declared nested_ctxt name)
      fun roles (Type (_, [Type (_, [address, global]), global', _])) =
            (require "nested role lost the global sharing equation" (global = global'); (address, global))
        | roles _ = error "nested header role lost its reference carrier"
      val pair as (address, global) = roles value
      val _ = require "nested header holes lost sharing through Self callback and member pointer"
        (roles (the_single (binder_types callback)) = pair andalso roles pointer = pair)
      val Type (_, [a]) = address
      val Type (_, [g]) = global
    in require "nested header holes were flattened, conflated or strengthened"
      (Term.is_TVar a andalso Term.is_TVar g andalso a <> g andalso
        address = Type (\<^type_name>\<open>option\<close>, [a]) andalso
        global = Type (\<^type_name>\<open>list\<close>, [g])) end
  val _ = List.app check_nested ["shared_report_holes_first", "shared_report_holes_second"]
  val _ = List.app (fn nominal => ignore (rejected ("shared-no-auto-read-" ^ nominal)
      "Type unification failed" ("urust_fn " ^ command_source
        ("fn SharedNoAutomaticRead(value: &" ^ nominal ^ ") -> bool { value }"))))
    ["SharedReportStorageFlag", "SharedReportReadonlyFlag"]
in val _ = writeln "shared printer, nominal/generic navigation, exact diagnostics and generic ledger rollback/recovery PASS" end
\<close>

end
