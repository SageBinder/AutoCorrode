(* Internal audits for the urust chunk examples in Parser_Chunk_Tests.  *)

theory Parser_Chunk_Regression_Tests
  imports Parser_Chunk_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Test support \<close>

text\<open>
Command-level audits run synthetic theory text in a private toplevel state. Positions carry
symbol offsets and a synthetic identity, so diagnostics and reports can be located exactly;
output, warnings and reports of that synthetic file are captured privately.
\<close>

ML\<open>
structure Chunk_Test =
struct
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  val omega = "\<omega>"
  fun annotation text = omega ^ cartouche text
  fun command_source text = cartouche ("\n" ^ text ^ "\n")

  fun start_position label = Position.make0 1 1 0 "" label ("chunk-test-" ^ label)

  fun source label text =
    Parser_Lex_Util.positioned_content_source text (start_position label)

  fun parse ctxt label text = URust_Parser.parse_chunk_source ctxt (source label text)

  fun the_chunk ctxt label text =
    (case parse ctxt label text of
       SOME chunk => chunk
     | NONE => error (label ^ ": chunk parsed as empty"))

  fun require label condition =
    if condition then () else error ("chunk audit: " ^ label)

  fun failure_message label expected result =
    (case result of
       Exn.Res _ => error ("chunk audit: " ^ label ^ " unexpectedly succeeded")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             if forall (fn fragment => String.isSubstring fragment message) expected
             then message
             else
               error
                 ("chunk audit: " ^ label ^ " produced the wrong diagnostic:\n" ^ message)
           end)

  fun expect_failure label expected f = failure_message label expected (Exn.result f ())

  (* Positions named by a positioned diagnostic, in message order. *)
  fun message_positions message =
    let
      fun collect (XML.Elem ((name, properties), body)) positions =
            fold collect body
              (if name = Markup.positionN
               then Position.of_properties properties :: positions
               else positions)
        | collect (XML.Text _) positions = positions
    in rev (fold collect (YXML.parse_body message) []) end

  fun message_range message =
    (case message_positions message of
       pos :: _ => (the_default ~1 (Position.offset_of pos), the_default ~1 (Position.end_offset_of pos))
     | [] => (~1, ~1))

  (* Symbol offsets of the nth occurrence (from 0) of needle in text with the source starting
     at offset 1. Raw indices are used only to locate the needle; offsets count symbols. *)
  fun raw_index text needle occurrence =
    let
      fun search from n =
        let
          val limit = size text - size needle
          fun scan index =
            if index > limit then error ("chunk audit: missing " ^ quote needle)
            else if String.substring (text, index, size needle) = needle then index
            else scan (index + 1)
          val found = scan from
        in if n = 0 then found else search (found + size needle) (n - 1) end
    in search 0 occurrence end

  fun symbol_offset text raw = length (Symbol.explode (String.substring (text, 0, raw))) + 1

  fun range_of text needle occurrence =
    let
      val raw = raw_index text needle occurrence
      val start = symbol_offset text raw
    in (start, start + length (Symbol.explode needle)) end

  (* Range of needle inside the first occurrence of a disambiguating context. *)
  fun range_within text context needle =
    let
      val raw = raw_index text context 0 + raw_index context needle 0
      val start = symbol_offset text raw
    in (start, start + length (Symbol.explode needle)) end

  fun position_range pos =
    (the_default ~1 (Position.offset_of pos), the_default ~1 (Position.end_offset_of pos))

  fun quiet_prefix extra =
    "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 0" ^
      extra ^ "]]\n"

  fun run_commands interactive label thy text =
    let
      val transitions = Outer_Syntax.parse_text thy (K thy) (start_position label) text
    in
      fold (Toplevel.command_exception interactive) transitions
        (Toplevel.make_state (SOME thy))
    end

  fun plain message =
    XML.content_of (YXML.parse_body message)
    |> Symbol.explode
    |> filter_out Symbol.is_control
    |> implode

  (* Successful command output of the synthetic file, warnings and PIDE reports. *)
  fun capture interactive label thy text =
    let
      val output = Synchronized.var ("chunk output " ^ label) ([]: string list)
      val warnings = Synchronized.var ("chunk warnings " ^ label) ([]: string list)
      val reports = Synchronized.var ("chunk reports " ^ label) ([]: string list)
      fun collect target chunks =
        if Position.file_of (Position.thread_data ()) = SOME label
        then Synchronized.change target (fn messages => messages @ [implode chunks])
        else ()
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Print_Mode.with_modes [Print_Mode.PIDE]
            (fn () =>
              Unsynchronized.setmp Private_Output.report_fn (collect reports)
                (fn () =>
                  Unsynchronized.setmp Private_Output.writeln_fn (collect output)
                    (fn () =>
                      Unsynchronized.setmp Private_Output.warning_fn (collect warnings)
                        (fn () => Exn.result (run_commands interactive label thy) text) ())
                    ())
                ()) ())
    in
      {result = result,
       output = map plain (Synchronized.value output),
       warnings = map plain (Synchronized.value warnings),
       reports = maps YXML.parse_body (Synchronized.value reports)}
    end

  fun result_context (Exn.Res state) = Toplevel.context_of state
    | result_context (Exn.Exn exn) = Exn.reraise exn

  (* Each report tree is markup applied at one position; nested elements share it. *)
  fun report_events reports =
    let
      fun events (XML.Elem ((name, properties), body)) =
            (name, properties) :: maps events body
        | events (XML.Text _) = []
    in maps events reports end

  fun report_range (_, properties) = position_range (Position.of_properties properties)

  fun reports_at range reports =
    filter (fn event => report_range event = range) (report_events reports)

  fun entity_kinds_at range reports =
    reports_at range reports
    |> map_filter (fn (name, properties) =>
        if name = Markup.entityN then Properties.get properties Markup.kindN else NONE)

  val semantic_kinds =
    ["urust_item", "urust_constructor", "urust_field", "urust_function",
     Micro_Rust_Names.notationN, Markup.constantN, Markup.type_nameN]

  fun semantic_entities reports =
    report_events reports
    |> filter (fn (name, properties) =>
        name = Markup.entityN andalso
          (case Properties.get properties Markup.kindN of
             SOME kind => member (op =) semantic_kinds kind
           | NONE => false))

  (* Output authored by the uRust commands; native backend constant listings are excluded. *)
  fun authored_output output =
    filter_out (fn message => String.isPrefix "consts" message) output

  fun registry_snapshot ctxt =
    {notations =
       Micro_Rust_Names.dump ctxt
       |> map (fn (kind, name, entry) =>
           (Micro_Rust_Names.kind_to_string kind, name, #hol_term entry)),
     types = map URust_Item_Scope.type_rust_name (URust_Item_Scope.dump_types ctxt),
     constructors =
       map URust_Item_Scope.constructor_rust_path (URust_Item_Scope.dump_constructors ctxt),
     functions =
       map URust_Item_Scope.function_rust_name (URust_Item_Scope.dump_functions ctxt),
     mappings = map #1 (URust_Type_Mappings.dump ctxt)}

  fun const_declared ctxt name =
    Sign.declared_const (Proof_Context.theory_of ctxt)
      (Sign.full_bname (Proof_Context.theory_of ctxt) name)

  fun type_declared ctxt name =
    Sign.declared_tyname (Proof_Context.theory_of ctxt)
      (Sign.full_bname (Proof_Context.theory_of ctxt) name)

  fun fact_declared ctxt name =
    Global_Theory.defined_fact (Proof_Context.theory_of ctxt)
      (Sign.full_bname (Proof_Context.theory_of ctxt) name)
end
\<close>


section\<open> Parsed chunks, envelopes and source slices \<close>

ML\<open>
local
  open Chunk_Test
  val text =
    "\n  " ^ annotation "renames = [\"a\" \<rightarrow> \"b\"], name = \<open>pair\<close>" ^ "\n" ^
    "  struct ChunkAstNamed { a: u32 }\n\n" ^
    "  fn ChunkAstFunction(x: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { let s = \"} " ^ annotation "x" ^ "\"; x }\n" ^
    "  // " ^ annotation "comment text" ^ " stays a comment\n" ^
    "  struct ChunkAstUnit;\n" ^
    "  struct ChunkAstTuple(u32, \<tau>\<open>bool\<close>);\n" ^
    "  /* fn struct enum */ struct ChunkAstEmpty {}\n" ^
    "  struct ChunkAstEmptyTuple();\n" ^
    "  \<comment> \<open>enum after a formal comment\<close>\n" ^
    "  enum ChunkAstEnum { First, Second(u32), Third { value: u32 } }\n" ^
    "  " ^ annotation "backend = hol" ^ "\n" ^
    "  #[repr(u8)]\n" ^
    "  enum ChunkAstRepr { Low = 1 }\n" ^
    "  type ChunkAstAlias = u16;\n" ^
    "  fn ChunkAstLast() { \<epsilon>\<open>skip\<close> }\n"
  val chunk = the_chunk \<^context> "ast" text
  val items = URust_AST.chunk_items chunk
  fun kind (URust_AST.Datatype_Item _) = "datatype"
    | kind (URust_AST.Function_Item_Node _) = "fn"
    | kind (URust_AST.Type_Alias_Item_Node _) = "type"
  val _ =
    require "chunk member kinds or order changed"
      (map (kind o URust_AST.annotated_item_item) items =
        ["datatype", "fn", "datatype", "datatype", "datatype", "datatype", "datatype",
         "datatype", "type", "fn"])
  val payloads =
    map (Option.map (Input.string_of o URust_AST.annotation_payload) o
      URust_AST.annotated_item_annotation) items
  val _ =
    require "annotation ownership changed"
      (payloads =
        [SOME ("renames = [\"a\" \<rightarrow> \"b\"], name = \<open>pair\<close>"), NONE, NONE, NONE,
         NONE, NONE, NONE, SOME "backend = hol", NONE, NONE])
  val slices = map (Input.string_of o URust_AST.annotated_item_source) items
  val _ =
    require "item source slices changed"
      (slices =
        ["struct ChunkAstNamed { a: u32 }",
         "fn ChunkAstFunction(x: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> { let s = \"} " ^ annotation "x" ^ "\"; x }",
         "struct ChunkAstUnit;", "struct ChunkAstTuple(u32, \<tau>\<open>bool\<close>);",
         "struct ChunkAstEmpty {}", "struct ChunkAstEmptyTuple();",
         "enum ChunkAstEnum { First, Second(u32), Third { value: u32 } }",
         "#[repr(u8)]\n  enum ChunkAstRepr { Low = 1 }", "type ChunkAstAlias = u16;",
         "fn ChunkAstLast() { \<epsilon>\<open>skip\<close> }"])
  val _ =
    require "item source ranges are not symbol ranges"
      (map (position_range o Input.pos_of o URust_AST.annotated_item_source) items =
        [(#1 (range_of text "struct ChunkAstNamed" 0), #2 (range_of text "u32 }" 0)),
         (#1 (range_of text "fn ChunkAstFunction" 0), #2 (range_of text "x }" 0)),
         (#1 (range_of text "struct ChunkAstUnit" 0), #2 (range_of text "ChunkAstUnit;" 0)),
         (#1 (range_of text "struct ChunkAstTuple" 0), #2 (range_of text (Symbol.close ^ ");") 0)),
         (#1 (range_of text "struct ChunkAstEmpty " 0), #2 (range_of text "ChunkAstEmpty {}" 0)),
         (#1 (range_of text "struct ChunkAstEmptyTuple" 0), #2 (range_of text "();" 0)),
         (#1 (range_of text "enum ChunkAstEnum" 0), #2 (range_of text "u32 } }" 0)),
         (#1 (range_of text "#[repr" 0), #2 (range_of text "Low = 1 }" 0)),
         (#1 (range_of text "type ChunkAstAlias" 0), #2 (range_of text "u16;" 0)),
         (#1 (range_of text "fn ChunkAstLast" 0), #2 (range_of text (Symbol.close ^ " }") 0))])
  val SOME first_annotation = URust_AST.annotated_item_annotation (hd items)
  val layout = URust_AST.annotation_source_layout first_annotation
  val annotation_text = annotation "renames = [\"a\" \<rightarrow> \"b\"], name = \<open>pair\<close>"
  val (annotation_start, annotation_stop) = range_of text annotation_text 0
  val _ =
    require "annotation span is not the complete marker and cartouche"
      (position_range (URust_AST.annotation_position first_annotation) =
        (annotation_start, annotation_stop))
  val _ =
    require "annotation token layout changed"
      (map (fn (token, pos) => (token, position_range pos)) (URust_AST.source_tokens layout) =
        [(URust_AST.Literal_Token, (annotation_start, annotation_start + 1)),
         (URust_AST.Delimiter_Token Symbol.open_, (annotation_start + 1, annotation_start + 2)),
         (URust_AST.Delimiter_Token Symbol.close, (annotation_stop - 1, annotation_stop))])
  val _ =
    require "annotation payload range is not symbol-counted"
      (position_range (Input.pos_of (URust_AST.annotation_payload first_annotation)) =
        (annotation_start + 2, annotation_stop - 1))
  val serialized = URust_Printer.string_of_chunk URust_Printer.serialized_options chunk
  val reparsed = the_chunk \<^context> "ast-roundtrip" serialized
  val _ =
    require "serialized chunk tokens changed after reparsing"
      (URust_Printer.tokens_of_chunk URust_Printer.serialized_options chunk =
        URust_Printer.tokens_of_chunk URust_Printer.serialized_options reparsed)
  val _ =
    require "serialized chunk lost an annotation"
      (String.isSubstring (annotation "backend = hol") serialized andalso
        String.isSubstring annotation_text serialized)
  val _ =
    require "layout-only chunks are not empty"
      (is_none (parse \<^context> "empty" "  // nothing\n  /* still nothing */\n  \<comment> \<open>none\<close>\n"))
in
  val _ = writeln "chunk AST, envelope, slice and serialized roundtrip audits passed"
end
\<close>


section\<open> Annotation placement and lexer state \<close>

ML\<open>
local
  open Chunk_Test
  val item = "fn ChunkPlaced() {}"
  fun rejects label expected text needle occurrence =
    let
      val message =
        expect_failure label expected (fn () => parse \<^context> label text)
    in
      require (label ^ " diagnostic is not at the explanatory span")
        (message_range message = range_of text needle occurrence)
    end
  val a = annotation "abbrev"
  val _ =
    rejects "same-line" ["must be on the line before its declaration"]
      (a ^ " " ^ item) item 0
  val _ =
    rejects "preceding-source" ["must start its own line"]
      ("fn ChunkBefore() {} " ^ a ^ "\n" ^ item) a 0
  val _ =
    rejects "trailing-source" ["must end its line"]
      (a ^ " trailing words\n" ^ item) "trailing words" 0
  val _ =
    rejects "consecutive" ["must be the only annotation"]
      (a ^ "\n" ^ annotation "pretty" ^ "\n" ^ item) (omega ^ Symbol.open_) 1
  val _ =
    rejects "consecutive-same-line" ["must be the only annotation"]
      (a ^ annotation "pretty" ^ "\n" ^ item) (omega ^ Symbol.open_) 1
  val _ =
    rejects "blank-line" ["remove the blank line"]
      (a ^ "\n   \n" ^ item) "\n" 1
  val _ =
    rejects "line-comment" ["put declaration comments before it"]
      (a ^ "\n  // note\n" ^ item) "//" 0
  val _ =
    rejects "block-comment" ["put declaration comments before it"]
      (a ^ "\n/* note */\n" ^ item) "/*" 0
  val _ =
    rejects "formal-comment" ["put declaration comments before it"]
      (a ^ "\n" ^ Symbol.comment ^ " " ^ cartouche "note" ^ "\n" ^ item) Symbol.comment 0
  val _ =
    rejects "dangling-newline" ["not the end of input"] (item ^ "\n" ^ a ^ "\n  ") a 0
  val _ =
    rejects "dangling" ["not the end of input"] (item ^ "\n" ^ a) a 0
  val _ =
    rejects "unterminated" ["unterminated \<omega> annotation"]
      (omega ^ Symbol.open_ ^ "abbrev\n" ^ item) omega 0
  val _ =
    rejects "field" ["cannot be annotated"]
      ("struct ChunkField {\n  " ^ a ^ "\n  value: u32\n}") omega 0
  val _ =
    rejects "parameter" ["cannot be annotated"]
      ("fn ChunkParameter(\n  " ^ a ^ "\n  value: u32) {}") omega 0
  val _ =
    rejects "variant" ["cannot be annotated"]
      ("enum ChunkVariant {\n  " ^ a ^ "\n  First }") omega 0
  val body_message =
    expect_failure "body" ["syntax error", "<\<omega> annotation>"]
      (fn () => parse \<^context> "body" ("fn ChunkBody() {\n  " ^ a ^ "\n  ()\n}"))
  val _ =
    expect_failure "trailing-item-source" ["syntax error"]
      (fn () => parse \<^context> "trailing" (item ^ "\n  1 + 2"))
  val expression_source = source "expression" (a ^ "\n1")
  val _ =
    expect_failure "expression-mode" ["only supported before declarations of a urust chunk"]
      (fn () => URust_Parser.parse_source \<^context> expression_source)
  val _ =
    expect_failure "item-mode" ["only supported before declarations of a urust chunk"]
      (fn () => URust_Parser.parse_function_source \<^context> (source "item" (a ^ "\n" ^ item)))
  (* A successful chunk parse must not leave annotations enabled for later single-item parses. *)
  val _ = the_chunk \<^context> "enabled" (a ^ "\n" ^ item)
  val _ =
    expect_failure "stale-enabled" ["only supported before declarations of a urust chunk"]
      (fn () => URust_Parser.parse_source \<^context> expression_source)
  (* A rejected chunk must not leave capture state for the next chunk. *)
  val _ =
    expect_failure "stale-capture" ["unterminated \<omega> annotation"]
      (fn () => parse \<^context> "stale" (omega ^ Symbol.open_ ^ "abbrev"))
  val recovered = the_chunk \<^context> "recovered" (annotation "pretty" ^ "\n" ^ item)
  val _ =
    require "recovered chunk lost its annotation"
      (map (Option.map (Input.string_of o URust_AST.annotation_payload) o
          URust_AST.annotated_item_annotation) (URust_AST.chunk_items recovered) =
        [SOME "pretty"])
  val multiline =
    the_chunk \<^context> "multiline"
      ("  " ^ annotation "state = \<open>'s\<close>,\n    abort = \<open>bool\<close>" ^ "\n  " ^ item)
  val _ =
    require "multi-line annotation payload changed"
      (map (Option.map (Input.string_of o URust_AST.annotation_payload) o
          URust_AST.annotated_item_annotation) (URust_AST.chunk_items multiline) =
        [SOME "state = \<open>'s\<close>,\n    abort = \<open>bool\<close>"])
in
  val _ = writeln "annotation placement, member, mode and lexer-state audits passed"
end
\<close>


section\<open> Outer and annotation option diagnostics \<close>

ML\<open>
local
  open Chunk_Test
  fun chunk outer body =
    quiet_prefix "" ^ "urust " ^ outer ^ command_source body
  fun rejects_within label expected text range =
    let
      val {result, output, ...} = capture true label \<^theory> text
      val message = failure_message label expected result
      val _ =
        (case range of
           NONE => ()
         | SOME range =>
             require (label ^ " diagnostic is not at the explanatory span:\n" ^ message)
               (message_range message = range))
      val _ = require (label ^ " printed successful output") (null (authored_output output))
    in () end
  fun rejects label expected text needle occurrence =
    rejects_within label expected text
      (if needle = "" then NONE else SOME (range_of text needle occurrence))
  (* Outer syntax errors name the offending token after the start of the failed entry list. *)
  fun rejects_at label expected text context needle =
    let
      val {result, ...} = capture true label \<^theory> text
      val message = failure_message label expected result
    in
      require (label ^ " diagnostic does not name the offending token:\n" ^ message)
        (exists
          (fn pos => position_range pos = range_within text context needle)
          (message_positions message))
    end
  val item = "fn ChunkOption(value: u32) -> u32 { value }"
  val datatype_item = "struct ChunkOptionCell { value: u32 }"
  val enum_item = "enum ChunkOptionChoice { First, Second }"
  fun annotated payload declaration = annotation payload ^ "\n" ^ declaration
  val _ =
    List.app
      (fn option =>
        rejects ("outer-" ^ option) ["option " ^ quote option, "is declaration-specific"]
          (chunk ("[" ^ option ^ " = true] ") item) option 0)
      ["abbrev", "application_def", "name", "renames", "state", "backend", "attrs"]
  val _ =
    rejects "outer-unknown" ["unknown uRust command option \"colour\""]
      (chunk "[colour] " item) "colour" 0
  val _ =
    rejects "outer-prefixed" ["unknown uRust command option \"urust_verbosity\""]
      (chunk "[urust_verbosity = 1] " item) "urust_verbosity" 1
  val _ =
    rejects "outer-duplicate" ["duplicate uRust command option \"verbosity\""]
      (chunk "[verbosity = 1, verbosity = 2] " item) "verbosity" 2
  val _ =
    rejects "outer-mistyped" ["\"verbosity\" expects an integer from 0 to 2"]
      (chunk "[verbosity = true] " item) "true" 0
  val _ =
    rejects "fn-renames" ["option \"renames\" does not apply to fn declarations"]
      (chunk "" (annotated "renames = [\"value\" \<rightarrow> \"v\"]" item)) "renames" 0
  val _ =
    rejects "struct-abbrev" ["option \"abbrev\" does not apply to struct or enum declarations"]
      (chunk "" (annotated "abbrev" datatype_item)) "abbrev" 0
  val _ =
    rejects "enum-state" ["option \"state\" does not apply to struct or enum declarations"]
      (chunk "" (annotated "state = \<open>unit\<close>" enum_item)) "state" 0
  val _ =
    rejects "annotation-unknown" ["unknown uRust command option \"colour\""]
      (chunk "" (annotated "renames = [\"value\" \<rightarrow> \"v\"], colour" datatype_item))
      "colour" 0
  val _ =
    rejects "annotation-prefixed" ["unknown uRust command option \"urust_abbrev\""]
      (chunk "" (annotated "urust_abbrev" item)) "urust_abbrev" 0
  val _ =
    rejects "annotation-duplicate" ["duplicate uRust command option \"abbrev\""]
      (chunk "" (annotated "abbrev, abbrev = false" item)) "abbrev" 1
  val _ =
    rejects "annotation-name-mistyped" ["\"name\" expects a HOL binding or _"]
      (chunk "" (annotated "name = 3" item)) "3" 0
  val _ =
    rejects "annotation-name-missing" ["\"name\" expects a HOL binding"]
      (chunk "" (annotated "name" datatype_item)) "name" 0
  val anonymous_datatype = chunk "" (annotated "name = _" datatype_item)
  val _ =
    rejects_within "datatype-anonymous" ["_ is not a datatype naming placeholder"]
      anonymous_datatype (SOME (range_within anonymous_datatype "name = _" "_"))
  val _ =
    rejects "annotation-empty" ["must contain at least one option"]
      (chunk "" (annotated "  " item)) (annotation "  ") 0
  val _ =
    rejects_at "annotation-trailing" ["Outer syntax error", "\",\" or end of annotation expected"]
      (chunk "" (annotated "abbrev pretty" item)) "abbrev pretty" "pretty"
  val _ =
    rejects "annotation-comma" ["Outer syntax error"]
      (chunk "" (annotated "abbrev," item)) "" 0
  val verbosity_text = chunk "" (annotated "verbosity = 3" item)
  val _ =
    rejects_within "annotation-verbosity" ["must be 0, 1, or 2, but found 3"]
      verbosity_text (SOME (range_within verbosity_text "verbosity = 3" "3"))
  val _ =
    rejects "annotation-backend" ["backend expects auto, enum, hol, or simple_word_enum"]
      (chunk "" (annotated "backend = custom" enum_item)) "custom" 0
  val width_text = chunk "" (annotated "word_width = 0" enum_item)
  val _ =
    rejects_within "annotation-width" ["\"word_width\" expects a positive word width"]
      width_text (SOME (range_within width_text "word_width = 0" "0"))
  val _ =
    rejects "anonymous-attrs" ["attrs is not supported for anonymous declarations"]
      (chunk "" (annotated "name = _, attrs = [micro_rust_simps]" item)) "attrs" 0
  val _ =
    rejects "abbrev-application" ["abbreviation mode cannot be combined with `application_def`"]
      (chunk "" (annotated "abbrev, application_def" item)) "" 0
  val scoped_abbrev =
    quiet_prefix ", urust_abbrev = true" ^ "urust " ^
      command_source (annotated "application_def" item)
  val _ =
    rejects "scoped-abbrev-application" ["abbreviation mode cannot be combined"]
      scoped_abbrev "" 0
  val overridden =
    quiet_prefix ", urust_abbrev = true" ^ "urust " ^
      command_source (annotated "abbrev = false, application_def" item)
  val overridden_ctxt =
    result_context (#result (capture true "scoped-abbrev-override" \<^theory> overridden))
  val _ =
    require "an inline false abbrev did not override the scoped setting"
      (fact_declared overridden_ctxt "chunk_option_def")
  val _ =
    rejects "type-alias-member"
      ["type alias items are not chunk members; declare them with urust_type_alias"]
      (chunk "" ("type ChunkOptionAlias = u16;\n" ^ item)) "ChunkOptionAlias" 0
  val _ =
    rejects "empty-chunk" ["urust: empty chunk"] (chunk "" "  // only a comment") "" 0
  val _ =
    rejects "single-item-annotation" ["only supported before declarations of a urust chunk"]
      (quiet_prefix "" ^ "urust_fn " ^ command_source (annotated "abbrev" item)) omega 0
in
  val _ = writeln "outer, annotation, schema and member diagnostics passed"
end
\<close>


section\<open> Precedence, output order and context isolation \<close>

ML\<open>
local
  open Chunk_Test
  val prefix =
    "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 2, " ^
      "urust_register_notation = false]]\n"
  val text =
    prefix ^ "urust [verbosity = 1, register_notation = true] " ^
      command_source
        (annotation "verbosity = 0, abbrev" ^ "\n" ^
         "fn ChunkOrderFirst(value: u32) -> u32 { value }\n" ^
         "fn ChunkOrderSecond(value: u32) -> u32 { ChunkOrderFirst(value) }\n" ^
         annotation "verbosity = 2, register_notation = false" ^ "\n" ^
         "struct ChunkOrderCell { value: u32 }\n" ^
         annotation "verbosity = 2, pretty" ^ "\n" ^
         "fn ChunkOrderThird(cell: ChunkOrderCell) -> ChunkOrderCell { cell }\n" ^
         "fn ChunkOrderFourth() -> u32 { 4 }\n") ^
      "\nurust_fn chunk_order_after " ^
      command_source "fn ChunkOrderAfter() -> u32 { ChunkOrderSecond(1) }"
  fun compact name message =
    String.isPrefix ("definition " ^ name ^ "_def:") message andalso
      String.isSubstring "..." message andalso not (String.isSubstring "\<equiv>" message)
  fun complete name message =
    String.isPrefix ("definition " ^ name ^ "_def:") message andalso
      String.isSubstring "\<equiv>" message
  val {result, output, ...} = capture true "order" \<^theory> text
  val ctxt = result_context result
  val authored = authored_output output
  val _ =
    require ("output count or order changed:\n" ^ cat_lines authored)
      (length authored = 5 andalso
        compact "chunk_order_second" (nth authored 0) andalso
        String.isPrefix "urust_datatype generated artifacts" (nth authored 1) andalso
        complete "chunk_order_third" (nth authored 2) andalso
        String.isSubstring "FunctionBody \<mu>" (nth authored 2) andalso
        compact "chunk_order_fourth" (nth authored 3) andalso
        complete "chunk_order_after" (nth authored 4) andalso
        not (String.isSubstring "\<mu>" (nth authored 4)))
  val _ =
    require "an annotation leaked abbreviation mode to the next item"
      (not (fact_declared ctxt "chunk_order_first_def") andalso
        fact_declared ctxt "chunk_order_second_def")
  val functions = map URust_Item_Scope.function_rust_name (URust_Item_Scope.dump_functions ctxt)
  val _ =
    require "outer register_notation did not override the scoped setting"
      (member (op =) functions "ChunkOrderSecond" andalso
        member (op =) functions "ChunkOrderFourth")
  val field_aliases = Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NField "value"
  val _ =
    require "annotation register_notation = false did not suppress the field-lens alias"
      (not (exists (fn entry =>
          String.isSubstring "chunk_order_cell" (Syntax.string_of_term ctxt (#hol_term entry)))
        field_aliases))
  val _ =
    require "the chunk changed scoped configuration values"
      (not (Config.get ctxt URust_Command.urust_pp_test) andalso
        not (member (op =) functions "ChunkOrderAfter"))
in
  val _ = writeln "three-level precedence, isolation and source-order output passed"
end
\<close>

end
