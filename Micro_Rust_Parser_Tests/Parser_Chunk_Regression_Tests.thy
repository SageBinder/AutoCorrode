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

  (* Semantic entities authored by uRust (item, constructor, field, function, notation and type
     mapping) and resolved references to HOL constants and types. The parse-only baseline below
     is the stricter audit; this coarse filter keeps diagnostics short. *)
  val authored_kinds =
    ["urust_item", "urust_constructor", "urust_field", "urust_function",
     Micro_Rust_Names.notationN, "micro_rust_type_mapping"]

  fun semantic_entities reports =
    report_events reports
    |> filter (fn (name, properties) =>
        name = Markup.entityN andalso
          is_some (Position.offset_of (Position.of_properties properties)) andalso
          (case Properties.get properties Markup.kindN of
             SOME kind =>
               member (op =) authored_kinds kind orelse
                 (member (op =) [Markup.constantN, Markup.type_nameN] kind andalso
                   is_some (Properties.get properties Markup.refN))
           | NONE => false))

  (* Reports of a parse-only pass over the first cartouche of the text, tokenized at the same
     positions as the command run: the chunk lexer and the annotation payload tokens. These are
     the lexical reports a rejected chunk may leave behind. *)
  fun lexical_reports label thy text =
    let
      val ctxt = Proof_Context.init_global thy
      val keywords = Thy_Header.get_keywords' ctxt
      val tokens = Token.explode keywords (start_position label) text
      val after_command =
        (case find_index (fn token => Token.is_command token andalso Token.content_of token = "urust")
            tokens of
           ~1 => error ("chunk audit: no urust command in " ^ label)
         | index => drop index tokens)
      val cartouche =
        (case List.find (fn token => Token.kind_of token = Token.Cartouche) after_command of
           SOME token => token
         | NONE => error ("chunk audit: no cartouche in " ^ label))
      val source = Parser_Lex_Util.cartouche_source cartouche
      val captured = Synchronized.var ("lexical reports " ^ label) ([]: string list)
      fun collect chunks = Synchronized.change captured (fn messages => messages @ [implode chunks])
      fun schema (URust_AST.Function_Item_Node _) = URust_Command.Function_Annotation
        | schema _ = URust_Command.Datatype_Annotation
      fun read envelope =
        (case URust_AST.annotated_item_annotation envelope of
           SOME annotation =>
             ignore
               (URust_Command.read_annotation_options ctxt
                 (schema (URust_AST.annotated_item_item envelope)) annotation)
         | NONE => ())
      val _ =
        Parser_Test_Report_Lock.run (fn () =>
          Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
            Unsynchronized.setmp Private_Output.report_fn collect (fn () =>
              (case URust_Parser.parse_chunk_source ctxt source of
                 SOME chunk => List.app read (URust_AST.chunk_items chunk)
               | NONE => ())) ()) ())
    in maps YXML.parse_body (Synchronized.value captured) end

  (* One key per positioned report: markup, entity kind, symbol range and report text. *)
  fun report_keys reports =
    reports
    |> map_filter
        (fn XML.Elem ((name, properties), body) =>
              let val (start, stop) = position_range (Position.of_properties properties) in
                if start < 0 then NONE
                else
                  SOME
                    (start,
                     name ^ "|" ^ the_default "" (Properties.get properties Markup.kindN) ^ "|" ^
                       string_of_int start ^ "|" ^ string_of_int stop ^ "|" ^
                       XML.content_of body)
              end
          | XML.Text _ => NONE)

  (* Positioned reports of the command span that a parse-only pass does not produce. *)
  fun non_lexical_reports label thy text command_start reports =
    let
      val lexical = map #2 (report_keys (lexical_reports label thy text))
    in
      report_keys reports
      |> filter (fn (start, _) => start >= command_start)
      |> map #2
      |> filter_out (member (op =) lexical)
      |> sort_distinct string_ord
    end

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

  (* Name-space lookups, independent of the theory that declared the entity. *)
  fun const_declared ctxt name =
    can (Proof_Context.read_const {proper = true, strict = true} ctxt) name

  fun type_declared ctxt name =
    can (Proof_Context.read_type_name {proper = true, strict = true} ctxt) name

  fun fact_declared ctxt name = can (Proof_Context.get_thm ctxt) name
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


section\<open> Equivalence with single-item declarations \<close>

ML\<open>
local
  open Chunk_Test
  val ctxt = \<^context>
  val thy = \<^theory>
  val consts = Proof_Context.consts_of ctxt
  fun full name = Consts.intern consts name
  fun const_type name = Sign.the_const_type thy (full name)
  fun definition name = Proof_Context.get_thm ctxt (name ^ "_def")
  fun equation name = Logic.dest_equals (Thm.prop_of (definition name))
  fun executable_equations name =
    let
      val (_, equations) = Code.equations_of_cert thy (Code.get_cert ctxt [] (full name))
    in map_filter (fn (_, (SOME theorem, _)) => SOME theorem | _ => NONE) (the equations) end
  (* Application definitions name their arguments with fresh lexical variables; compare the
     right-hand side abstracted over the left-hand-side arguments. *)
  fun closed_definition name =
    let val (lhs, rhs) = equation name
    in fold_rev Term.lambda (snd (strip_comb lhs)) rhs end
  fun same_definition chunk control =
    let
      val (chunk_lhs, _) = equation chunk
      val (control_lhs, _) = equation control
    in
      require (chunk ^ " and " ^ control ^ " have different types")
        (const_type chunk = const_type control);
      require (chunk ^ " and " ^ control ^ " have different definitions")
        (closed_definition chunk aconv closed_definition control);
      require (chunk ^ " and " ^ control ^ " have different definition shapes")
        (length (snd (strip_comb chunk_lhs)) = length (snd (strip_comb control_lhs)));
      require (chunk ^ " and " ^ control ^ " have different code equations")
        (length (executable_equations chunk) = 1 andalso
          length (executable_equations control) = 1)
    end
  val _ = same_definition "chunk_packet_value" "control_packet_value"
  val _ = same_definition "chunk_with_attributes" "control_with_attributes"
  val _ = same_definition "chunk_channels" "control_channels"
  val (identity_type, identity_rhs) = Consts.the_abbreviation consts (full "chunk_identity")
  val (control_identity_type, control_identity_rhs) =
    Consts.the_abbreviation consts (full "control_identity")
  val _ =
    require "chunk and single-item abbreviations differ"
      (identity_type = control_identity_type andalso identity_rhs aconv control_identity_rhs)
  val _ =
    require "an abbreviation item installed a definition or code equation"
      (not (fact_declared ctxt "chunk_identity_def") andalso
        (case try executable_equations "chunk_identity" of
           NONE => true
         | SOME equations => null equations))
  val simps = Proof_Context.get_fact ctxt (Facts.named "micro_rust_simps")
  fun in_simps name = exists (fn theorem => Thm.eq_thm_prop (theorem, definition name)) simps
  val _ =
    require "annotation attrs did not decorate the definition like the outer list"
      (in_simps "chunk_with_attributes" andalso in_simps "control_with_attributes" andalso
        not (in_simps "chunk_packet_value"))
  val functions = map URust_Item_Scope.function_rust_name (URust_Item_Scope.dump_functions ctxt)
  val _ =
    require "callable registration differs from the single-item commands"
      (member (op =) functions "ChunkPacketValue" andalso
        member (op =) functions "ControlPacketValue" andalso
        not (member (op =) functions "ChunkIdentity") andalso
        not (member (op =) functions "ControlIdentity") andalso
        not (member (op =) functions "ChunkCheckedOnly"))
  val _ =
    require "an anonymous chunk function installed a constant"
      (not (const_declared ctxt "chunk_checked_only"))

  fun rename_type from to (Type (name, arguments)) =
        Type (if name = from then to else name, map (rename_type from to) arguments)
    | rename_type _ _ T = T
  fun strip_prefix prefix name =
    if String.isPrefix prefix name then String.extract (name, size prefix, NONE) else name
  fun term_name (Const (name, _)) = name
    | term_name term = Syntax.string_of_term ctxt term
  fun datatype_profile rust_name =
    let
      val type_entry = the (URust_Item_Scope.lookup_type ctxt rust_name)
      val hol_name = URust_Item_Scope.type_hol_name type_entry
      val local_name = strip_prefix (Long_Name.base_name hol_name ^ "_") o Long_Name.base_name
      val normalize = rename_type hol_name "datatype"
      val constructors =
        URust_Item_Scope.dump_constructors ctxt
        |> filter (fn entry => URust_Item_Scope.constructor_rust_type entry = rust_name)
        |> map (fn entry =>
            (strip_prefix (rust_name ^ "::") (URust_Item_Scope.constructor_rust_path entry)
             |> (fn path => if path = rust_name then "" else path),
             normalize (fastype_of (URust_Item_Scope.constructor_scheme entry)),
             map (fn (field, selector) =>
                 (field, local_name (term_name selector), normalize (fastype_of selector)))
               (URust_Item_Scope.constructor_fields entry)))
        |> sort (string_ord o apply2 #1)
      val mapping = the (URust_Type_Mappings.lookup ctxt rust_name)
    in
      (constructors, normalize (URust_Type_Mappings.entry_template mapping),
       URust_Type_Mappings.entry_arities mapping)
    end
  fun same_datatype chunk control =
    require (chunk ^ " and " ^ control ^ " have different generated artifacts:\n" ^
        @{make_string} (datatype_profile chunk) ^ "\n" ^ @{make_string} (datatype_profile control))
      (datatype_profile chunk = datatype_profile control)
  val _ = same_datatype "ChunkPacket" "ControlPacket"
  val _ = same_datatype "ChunkChoice" "ControlChoice"
  val _ = same_datatype "ChunkHolder" "ControlHolder"
  val _ =
    require "renamed field lenses and aliases differ"
      (const_declared ctxt "chunk_packet_sample_lens" andalso
        const_declared ctxt "control_packet_sample_lens" andalso
        let
          val lenses =
            map (term_name o #hol_term)
              (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NField "sampleValue")
        in
          exists (String.isSuffix "chunk_packet_sample_lens") lenses andalso
            exists (String.isSuffix "control_packet_sample_lens") lenses
        end)
  fun full_type name =
    dest_Type_name (Proof_Context.read_type_name {proper = true, strict = true} ctxt name)
  val _ =
    require "word enum conversions differ"
      (rename_type (full_type "chunk_word") "word" (const_type "chunk_word_to_u16_pure") =
        rename_type (full_type "control_word") "word" (const_type "control_word_to_u16_pure"))
in
  val _ = writeln "chunk declarations match the equivalent single-item declarations"
end
\<close>


section\<open> Whole-command atomicity \<close>

text\<open>
A failure in the last member of a chunk whose earlier functions and datatypes would succeed
leaves no declaration, registry entry, semantic report or successful output. The same names are
then available to a successful chunk.
\<close>

ML\<open>
structure Chunk_Atomicity =
struct
  open Chunk_Test
  val loud = "declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]\n"
  val earlier =
    "  " ^ annotation "pretty, verbosity = 0" ^ "\n" ^
    "  fn AtomicFirst(value: u32) -> u32 { let doubled = value; doubled }\n" ^
    "  fn AtomicEscapes(value: \<tau>\<open>nat\<close>) -> u32 {\n" ^
    "    let x = \<epsilon>\<open>literal (of_nat (Suc 0))\<close>; x\n" ^
    "  }\n" ^
    "  " ^ annotation "attrs = [micro_rust_simps]" ^ "\n" ^
    "  fn AtomicAttributed(value: u32) -> u32 { value }\n" ^
    "  " ^ annotation "renames = [\"atomicValue\" \<rightarrow> \"atomic_value\"]" ^ "\n" ^
    "  struct AtomicRecord { atomicValue: u32 }\n" ^
    "  enum AtomicChoice { AtomicYes, AtomicNo(u32) }\n" ^
    "  #[repr(u8)]\n" ^
    "  enum AtomicLevel { AtomicLow = 1, AtomicHigh = 2 }\n" ^
    "  fn AtomicUse(record: AtomicRecord) -> u32 { AtomicFirst(record.atomicValue) }\n"
  val names =
    {constants =
       ["atomic_first", "atomic_escapes", "atomic_attributed", "atomic_use",
        "atomic_record.atomic_value", "atomic_record_atomic_value_lens"],
     types = ["atomic_record", "atomic_choice", "atomic_level"],
     facts = ["atomic_first_def", "atomic_escapes_def", "atomic_attributed_def", "atomic_use_def"],
     rust_types = ["AtomicRecord", "AtomicChoice", "AtomicLevel"],
     functions = ["AtomicFirst", "AtomicEscapes", "AtomicAttributed", "AtomicUse"]}
  fun declared ctxt =
    {constants = filter (const_declared ctxt) (#constants names),
     types = filter (type_declared ctxt) (#types names),
     facts = filter (fact_declared ctxt) (#facts names),
     rust_types = filter (is_some o URust_Item_Scope.lookup_type ctxt) (#rust_types names),
     mappings = filter (is_some o URust_Type_Mappings.lookup ctxt) (#rust_types names),
     functions = filter (is_some o URust_Item_Scope.lookup_function ctxt) (#functions names),
     notations =
       filter (fn (_, name, _) => String.isPrefix "Atomic" name orelse name = "atomicValue")
         (Micro_Rust_Names.dump ctxt)
       |> map #2}
  val base_ctxt = Proof_Context.init_global \<^theory>
  val _ =
    require "atomicity fixtures already exist"
      (declared base_ctxt =
        {constants = [], types = [], facts = [], rust_types = [], mappings = [],
         functions = [], notations = []})
  val failures =
    [("typing", "  fn AtomicBroken() -> bool { 1u32 }\n", ["Type unification failed"]),
     ("registration", "  fn AtomicRecord() {}\n",
       ["Rust function path \"AtomicRecord\" is already owned by a Rust constructor item"]),
     ("late-attribute",
       "  " ^ annotation "attrs = [OF refl]" ^
         "\n  fn AtomicLate(late: u32) -> u32 { late }\n",
       ["OF: no unifiers"]),
     ("binding",
       "  " ^ annotation "name = \"atomic_first\"" ^ "\n  fn AtomicDuplicate() -> u32 { 0 }\n",
       ["atomic_first"]),
     ("datatype", "  struct AtomicBad { value: AtomicMissing }\n",
       ["unknown Rust type \"AtomicMissing\""]),
     ("validation", "  " ^ annotation "abbrev, application_def" ^ "\n  fn AtomicMode() {}\n",
       ["abbreviation mode cannot be combined"]),
     ("rename", "  " ^ annotation "renames = [\"value\" \<rightarrow> \"a\", \"value\" \<rightarrow> \"b\"]" ^
        "\n  struct AtomicRenamed { value: u32 }\n", ["duplicate rename key"]),
     ("forward",
       "  fn AtomicForward() -> u32 { AtomicLater() }\n  fn AtomicLater() -> u32 { 1 }\n",
       ["unresolved body name \"AtomicLater\""]),
     ("self-call", "  fn AtomicSelf(value: u32) -> u32 { AtomicSelf(value) }\n",
       ["unresolved body name \"AtomicSelf\""]),
     ("recursive-datatype", "  struct AtomicNode { next: AtomicNode }\n",
       ["recursive Rust datatype reference \"AtomicNode\" is not supported"]),
     ("existing-function", "  fn ChunkRegistered() {}\n",
       ["Rust function path \"ChunkRegistered\" is already owned by a Rust function item"]),
     ("existing-datatype", "  struct ChunkPacket { other: u32 }\n",
       ["conflicting active mappings for \"ChunkPacket\""]),
     ("rename-collision",
       "  " ^ annotation "renames = [\"first\" \<rightarrow> \"atomic_pair_second\"]" ^
         "\n  struct AtomicPair { first: u32, second: u32 }\n",
       ["duplicate generated HOL field \"atomic_pair_second\""])]
  fun failing_case target wrap (label, failing, expected) =
    let
      val label = "atomic-" ^ target ^ "-" ^ label
      val text = loud ^ wrap ("urust " ^ command_source (earlier ^ failing))
      val {result, output, warnings, reports} = capture true label \<^theory> text
      val _ = failure_message ("atomic " ^ label) expected result
      (* The locale command of a wrapped scenario prints its own specification. *)
      val chunk_output =
        filter_out (String.isPrefix "locale atomic_loc") (authored_output output)
      val _ =
        require ("failed " ^ label ^ " chunk printed successful output:\n" ^
            cat_lines chunk_output)
          (null chunk_output)
      val command_start = #1 (range_of text "urust " 0)
      val _ =
        require ("failed " ^ label ^ " chunk replayed semantic reports")
          (null (filter (fn event => #1 (report_range event) >= command_start)
            (semantic_entities reports)))
      val _ =
        require ("failed " ^ label ^ " chunk emitted warnings:\n" ^ cat_lines warnings)
          (null warnings)
      (* Every report positioned in the earlier members, which would have succeeded, is one that
         a parse-only pass over the same command also produces. *)
      val failing_start = #1 (range_of text failing 0)
      fun key_start key =
        (case space_explode "|" key of
           _ :: _ :: start :: _ => the_default 0 (Int.fromString start)
         | _ => 0)
      val non_lexical = non_lexical_reports label \<^theory> text command_start reports
      val leaked = filter (fn key => key_start key < failing_start) non_lexical
      val _ =
        require ("failed " ^ label ^ " chunk left non-lexical reports of earlier members:\n" ^
            cat_lines leaked)
          (null leaked)
      (* The failing member releases its own elaboration markup with its error. *)
      val _ =
        if String.isSuffix "late-attribute" label then
          require ("failed " ^ label ^ " chunk did not release the failing member's markup")
            (exists (fn key => key_start key >= failing_start andalso
                String.isPrefix "entity|urust_var|" key) non_lexical)
        else ()
    in () end

  fun in_locale body =
    "locale atomic_loc =\n  fixes atomic_param :: nat\nbegin\n" ^ body ^ "\nend\n"
  fun in_context body =
    "context\n  fixes atomic_fixed :: nat\nbegin\n" ^ body ^ "\nend\n"
end
\<close>

ML\<open>
local
  open Chunk_Atomicity
  val _ = List.app (failing_case "theory" I) failures
  val success_text = loud ^ "urust " ^ command_source earlier
  val {result, output, reports, ...} = capture true "atomic-success" \<^theory> success_text
  val success_ctxt = result_context result
  val _ =
    require "the successful chunk did not declare every artifact"
      (declared success_ctxt =
        {constants = #constants names, types = #types names, facts = #facts names,
         rust_types = #rust_types names, mappings = #rust_types names,
         functions = #functions names,
         notations = #notations (declared success_ctxt)} andalso
        not (null (#notations (declared success_ctxt))))
  val _ =
    require "the successful chunk did not print every item in source order"
      (case authored_output output of
         [escapes, attributed, record, choice, level, use] =>
           String.isPrefix "definition atomic_escapes_def:" escapes andalso
           String.isPrefix "definition atomic_attributed_def:" attributed andalso
           String.isSubstring "AtomicRecord" record andalso
           String.isSubstring "AtomicChoice" choice andalso
           String.isSubstring "AtomicLevel" level andalso
           String.isPrefix "definition atomic_use_def:" use
       | _ => false)
  val _ =
    require "the successful chunk did not replay its semantic reports"
      (member (op =) (entity_kinds_at (range_of success_text "AtomicRecord" 0) reports)
          "urust_item" andalso
        member (op =) (entity_kinds_at (range_of success_text "AtomicFirst" 0) reports)
          "urust_function")
  (* A failed chunk followed by the corrected chunk in one document sequence. *)
  val sequence =
    loud ^ "urust " ^ command_source (earlier ^ "  fn AtomicBroken() -> bool { 1u32 }\n") ^
      "\nurust " ^ command_source earlier
  val transitions =
    Outer_Syntax.parse_text \<^theory> (K \<^theory>) (start_position "atomic-sequence") sequence
  fun step transition (state, failures) =
    (case Exn.result (Toplevel.command_exception true transition) state of
       Exn.Res state' => (state', failures)
     | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else (state, failures + 1))
  val (final_state, failed) =
    Parser_Test_Report_Lock.run (fn () =>
      Unsynchronized.setmp Private_Output.writeln_fn (K ()) (fn () =>
        Unsynchronized.setmp Private_Output.warning_fn (K ()) (fn () =>
          Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
            fold step transitions (Toplevel.make_state (SOME \<^theory>), 0)) ()) ()) ())
  val _ =
    require "the corrected chunk did not reuse the names of the failed chunk"
      (failed = 1 andalso
        #functions (declared (Toplevel.context_of final_state)) = #functions names)
in
  val _ = writeln "last-item failures leave no declarations, registrations, reports or output"
end
\<close>

text\<open> The same failures inside a locale target and inside a nested context with fixes. \<close>

ML\<open>
  List.app (Chunk_Atomicity.failing_case "locale" Chunk_Atomicity.in_locale)
    Chunk_Atomicity.failures
\<close>

ML\<open>
  List.app (Chunk_Atomicity.failing_case "context" Chunk_Atomicity.in_context)
    Chunk_Atomicity.failures
\<close>

section\<open> Failure markup of a single-item declaration \<close>

text\<open>
A failing single-item declaration releases its own queued uRust markup with its error, as a
failing chunk member does.
\<close>

ML\<open>
local
  open Chunk_Test
  fun released label command =
    let
      val text = quiet_prefix "" ^ command
      val {result, reports, ...} = capture true label \<^theory> text
      val _ = failure_message label ["OF: no unifiers"] result
    in
      require (label ^ " did not release its elaboration markup")
        (exists
          (fn (markup, properties) =>
            markup = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_var")
          (reports_at (range_of text "late" 1) reports))
    end
  val _ =
    released "single-late-function"
      ("urust_fn [attrs = [OF refl]] " ^ command_source "  fn SingleLate(late: u32) -> u32 { late }")
in
  val _ = writeln "failing single-item declarations release their own markup"
end
\<close>


section\<open> Markup equivalence and escaped source positions \<close>

ML\<open>
local
  open Chunk_Test
  (* Report multisets at corresponding source tokens, without serials or positions. *)
  fun events label text needles =
    let
      val {result, reports, ...} = capture true label \<^theory> text
      val _ = result_context result
      fun summary (name, properties) =
        name ^ "/" ^ the_default "" (Properties.get properties Markup.kindN) ^ "/" ^
          Bool.toString (is_some (Properties.get properties Markup.defN)) ^ "/" ^
          Bool.toString (is_some (Properties.get properties Markup.refN))
    in
      map (fn (needle, occurrence) =>
          sort string_ord (map summary (reports_at (range_of text needle occurrence) reports)))
        needles
    end
  val body =
    "  struct MarkupPacket { sampleValue: u32 }\n" ^
    "  fn MarkupRead(packet: MarkupPacket) -> u32 { packet.sampleValue }\n"
  val chunk_text = quiet_prefix "" ^ "urust " ^ command_source body
  val single_text =
    quiet_prefix "" ^
      "urust_datatype " ^ command_source "  struct MarkupPacket { sampleValue: u32 }" ^ "\n" ^
      "urust_fn " ^ command_source "  fn MarkupRead(packet: MarkupPacket) -> u32 { packet.sampleValue }"
  val needles =
    [("MarkupPacket", 0), ("sampleValue", 0), ("MarkupRead", 0), ("packet", 0),
     ("MarkupPacket", 1), ("packet", 1), ("sampleValue", 1), ("u32", 1)]
  val _ =
    require "chunk markup differs from the equivalent single-item commands"
      (events "markup-chunk" chunk_text needles = events "markup-single" single_text needles)
  (* Embedded HOL sources, signature escapes and annotation attributes: their native markup is
     released with the chunk transaction and equals the single-item command's. *)
  val escape_function =
    "  fn MarkupEscape(value: \<tau>\<open>nat\<close>) -> u32 {\n" ^
    "    let x = \<epsilon>\<open>literal (of_nat (Suc 0))\<close>; x\n  }"
  val escape_chunk =
    quiet_prefix "" ^ "urust " ^
      command_source
        ("  " ^ annotation "attrs = [micro_rust_simps]" ^ "\n" ^ escape_function ^ "\n" ^
         "  fn MarkupEscapeUse() -> u32 { MarkupEscape(\<llangle>2\<rrangle>) }")
  val escape_single =
    quiet_prefix "" ^
      "urust_fn [attrs = [micro_rust_simps]] " ^ command_source escape_function ^ "\n" ^
      "urust_fn " ^ command_source "  fn MarkupEscapeUse() -> u32 { MarkupEscape(\<llangle>2\<rrangle>) }"
  val escape_needles =
    [("micro_rust_simps", 0), ("MarkupEscape", 0), ("value", 0), ("nat", 0), ("literal", 0),
     ("of_nat", 0), ("Suc", 0), ("0", 1), ("x", 1), ("MarkupEscape", 2), ("2", 0)]
  val escape_chunk_events = events "markup-escape-chunk" escape_chunk escape_needles
  val _ =
    require "embedded-source markup differs from the equivalent single-item commands"
      (escape_chunk_events =
        events "markup-escape-single" escape_single escape_needles)
  val _ =
    require "embedded-source markup was not released after the successful chunk"
      (exists (exists (String.isPrefix "typing")) escape_chunk_events andalso
        exists (exists (String.isPrefix "entity/attribute")) escape_chunk_events)
  val annotated =
    quiet_prefix "" ^ "urust " ^
      command_source
        ("  " ^ annotation "renames = [\"sampleValue\" \<rightarrow> \"sample\"], name = \"markup_packet\"" ^ "\n" ^
         "  struct MarkupPacket { sampleValue: u32 }\n" ^
         "  " ^ annotation "state = \<open>'s::linorder\<close>, attrs = [micro_rust_simps]" ^ "\n" ^
         "  fn MarkupRead(packet: MarkupPacket) -> u32 { packet.sampleValue }")
  val {result, reports, ...} = capture true "markup-annotated" \<^theory> annotated
  val _ = result_context result
  fun names_at needle occurrence =
    map #1 (reports_at (range_of annotated needle occurrence) reports)
  val _ =
    require "annotation marker, delimiter or payload markup changed"
      (member (op =) (names_at omega 0) Markup.literalN andalso
        member (op =) (names_at Symbol.open_ 1) Markup.delimiterN andalso
        member (op =) (names_at Symbol.close 0) Markup.delimiterN andalso
        member (op =) (names_at "\"sampleValue\"" 0) Markup.stringN andalso
        member (op =) (names_at "\<rightarrow>" 0) Markup.delimiterN andalso
        member (op =) (names_at "\"markup_packet\"" 0) Markup.stringN andalso
        member (op =) (names_at omega 1) Markup.literalN)
  val _ =
    require "nested payload sources lost their native markup"
      (member (op =) (names_at "linorder" 0) Markup.entityN andalso
        member (op =) (names_at "micro_rust_simps" 0) Markup.entityN)
  val _ =
    require "declaration navigation after escaped payload symbols is misplaced"
      (member (op =) (entity_kinds_at (range_of annotated "MarkupPacket" 0) reports) "urust_item" andalso
        member (op =) (entity_kinds_at (range_of annotated "sampleValue" 1) reports) "urust_field" andalso
        member (op =) (entity_kinds_at (range_of annotated "MarkupRead" 0) reports) "urust_function")
in
  val _ = writeln "chunk markup matches single-item commands and annotation sources"
end
\<close>


section\<open> Independent type environments \<close>

ML\<open>
local
  open Chunk_Test
  val text =
    quiet_prefix "" ^ "urust " ^
      command_source
        ("  " ^ annotation "state = \<open>'s\<close>" ^ "\n" ^
         "  fn ChunkFreeState(value: \<tau>\<open>'a\<close>) -> \<tau>\<open>'a\<close> { value }\n" ^
         "  " ^ annotation "state = \<open>'s::linorder\<close>" ^ "\n" ^
         "  fn ChunkOrderedState(value: \<tau>\<open>'a::order\<close>) -> \<tau>\<open>'a\<close> { value }\n" ^
         "  fn ChunkUsesBoth(value: u32) -> u32 { ChunkFreeState(ChunkOrderedState(value)) }\n")
  val ctxt = result_context (#result (capture true "type-variables" \<^theory> text))
  fun const_type name =
    Sign.the_const_type (Proof_Context.theory_of ctxt)
      (Consts.intern (Proof_Context.consts_of ctxt) name)
  fun sorts name = map #2 (Term.add_tvarsT (const_type name) []) |> sort_distinct (list_ord string_ord)
  val _ =
    require "annotation or escape type variables leaked between chunk members"
      (sorts "chunk_free_state" = [["HOL.type"]] andalso
        member (op =) (sorts "chunk_ordered_state") ["Orderings.linorder"] andalso
        member (op =) (sorts "chunk_ordered_state") ["Orderings.order"])
  val _ =
    require "a later member could not instantiate earlier polymorphic constants"
      (fact_declared ctxt "chunk_uses_both_def")
in
  val _ = writeln "chunk members keep independent type and sort environments"
end
\<close>


section\<open> Serialized roundtrip of every payload kind and read-only pretty replay \<close>

ML\<open>
local
  open Chunk_Test
  val body =
    "  " ^ annotation "pp_test, pretty = false, verbosity = 2, register_notation = true" ^ "\n" ^
    "  fn ReplayFirst(value: u32) -> u32 { value }\n" ^
    "  " ^ annotation "renames = [\"replayValue\" \<rightarrow> \"replay_value\"], name = replay_cell" ^ "\n" ^
    "  struct ReplayCell { replayValue: u32 }\n" ^
    "  " ^ annotation "parameters = [\"T\" \<rightarrow> \"'element::ord\"], backend = hol, plugins = (plugins only: code)" ^ "\n" ^
    "  struct ReplayHolder<T> { element: T }\n" ^
    "  " ^ annotation "backend = \"simple_word_enum\", word_width = 8" ^ "\n" ^
    "  enum ReplayWord { ReplayLow = 1, ReplayHigh = 2 }\n" ^
    "  " ^ annotation "state = \<open>'s\<close>, abort = \<open>bool\<close>, input = \<open>unit\<close>, output = \<open>unit\<close>, attrs = [micro_rust_simps, code]" ^ "\n" ^
    "  fn ReplayChannels(cell: ReplayCell) -> u32 { cell.replayValue }\n" ^
    "  " ^ annotation "name = _, abbrev = false, application_def" ^ "\n" ^
    "  fn ReplayAnonymous(value: u32) -> u32 { ReplayFirst(value) }\n" ^
    "  " ^ annotation "abbrev" ^ "\n" ^
    "  fn ReplayAbbreviation() -> u32 { 1 }\n"
  val chunk = the_chunk \<^context> "replay-ast" body
  val serialized = URust_Printer.string_of_chunk URust_Printer.serialized_options chunk
  val reparsed = the_chunk \<^context> "replay-reparsed" serialized
  val _ =
    require "serialized chunk with every payload kind changed after reparsing"
      (URust_Printer.tokens_of_chunk URust_Printer.serialized_options chunk =
        URust_Printer.tokens_of_chunk URust_Printer.serialized_options reparsed andalso
        map (Option.map (Input.string_of o URust_AST.annotation_payload) o
            URust_AST.annotated_item_annotation) (URust_AST.chunk_items chunk) =
          map (Option.map (Input.string_of o URust_AST.annotation_payload) o
            URust_AST.annotated_item_annotation) (URust_AST.chunk_items reparsed))
  fun run pretty label =
    let
      val text =
        "declare [[urust_pp_test = true, urust_verbosity = 2, urust_pretty = " ^
          (if pretty then "true" else "false") ^ "]]\n" ^ "urust " ^ command_source body
      val {result, output, ...} = capture true label \<^theory> text
    in (registry_snapshot (result_context result), authored_output output) end
  val (pretty_registry, pretty_output) = run true "replay-pretty"
  val (plain_registry, _) = run false "replay-plain"
  val _ =
    require "pretty replay registered additional entries"
      (pretty_registry = plain_registry)
  val _ =
    require "pretty output was not produced per effective option"
      (exists (String.isSubstring "normalized uRust declaration") pretty_output andalso
        exists (String.isSubstring "FunctionBody \<mu>") pretty_output andalso
        exists (String.isPrefix "definition replay_first_def:") pretty_output andalso
        not (exists (fn message =>
            String.isPrefix "definition replay_first_def:" message andalso
            String.isSubstring "\<mu>" message) pretty_output))
in
  val _ = writeln "serialized roundtrip and read-only pretty replay passed"
end
\<close>


section\<open> A moderately sized chunk \<close>

ML\<open>
local
  open Chunk_Test
  val count = 24
  fun item index =
    let val n = string_of_int index in
      "  struct BulkCell" ^ n ^ " { bulkValue" ^ n ^ ": u32 }\n" ^
      "  " ^ annotation ("name = bulk_read_" ^ n) ^ "\n" ^
      "  fn BulkRead" ^ n ^ "(cell: BulkCell" ^ n ^ ") -> u32 { cell.bulkValue" ^ n ^ " }\n"
    end
  val text = quiet_prefix "" ^ "urust " ^ command_source (implode (map item (1 upto count)))
  val start = Timing.start ()
  val {result, reports, ...} = capture true "bulk" \<^theory> text
  val timing = Timing.result start
  val ctxt = result_context result
  val _ =
    require "the moderately sized chunk lost declarations"
      (forall (fn index => fact_declared ctxt ("bulk_read_" ^ string_of_int index ^ "_def"))
        (1 upto count))
  fun definitions kind context needle =
    length (filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME kind andalso
          is_some (Properties.get properties Markup.defN))
      (reports_at (range_within text context needle) reports))
  val _ =
    require "chunk semantic reports were not replayed exactly once"
      (forall (fn index =>
          let val n = string_of_int index in
            definitions "urust_item" ("struct BulkCell" ^ n ^ " ") ("BulkCell" ^ n) = 1 andalso
            definitions "urust_function" ("fn BulkRead" ^ n ^ "(") ("BulkRead" ^ n) = 1
          end)
        (1 upto count))
in
  val _ =
    writeln ("moderately sized chunk with " ^ string_of_int (2 * count) ^
      " declarations: " ^ Timing.message timing)
end
\<close>


section\<open> Attribute lines, command lines and line endings \<close>

ML\<open>
local
  open Chunk_Test
  val a = annotation "abbrev"
  fun rejects label expected text needle occurrence =
    let
      val message =
        expect_failure label expected (fn () => parse \<^context> label text)
    in
      require (label ^ " diagnostic is not at the explanatory span")
        (message_range message = range_of text needle occurrence)
    end
  val _ =
    rejects "repr-between" ["must precede the attributes of its declaration"]
      ("#[repr(u8)]\n" ^ a ^ "\nenum ChunkReprPlaced { Low = 1 }") a 0
  val _ =
    rejects "repr-between-indented" ["must precede the attributes of its declaration"]
      ("  #[repr(u8)]\n  " ^ a ^ "\n  enum ChunkReprPlaced { Low = 1 }") a 0
  (* A delimited source, like a command cartouche, starts on the command line. *)
  val first_line = a ^ "\nfn ChunkFirstLine() {}"
  fun delimited label text =
    let val start = start_position label in
      Parser_Lex_Util.delimited_content_source text
        (Position.range (start, Position.symbol_explode text start))
    end
  val message =
    expect_failure "first-line" ["must start its own line"]
      (fn () => URust_Parser.parse_chunk_source \<^context> (delimited "first-line" first_line))
  val _ =
    require "first-line diagnostic is not at the annotation"
      (message_range message = range_of first_line a 0)
  val _ =
    require "an annotation after the opening line of a delimited source was rejected"
      (is_some (URust_Parser.parse_chunk_source \<^context>
        (delimited "second-line" ("\n" ^ first_line))))
  val _ = the_chunk \<^context> "content-first-line" first_line
  val crlf =
    the_chunk \<^context> "crlf"
      ("fn ChunkCrlfA() {}\r\n" ^ a ^ "\r\nfn ChunkCrlfB() {}\r\n")
  val _ =
    require "CR LF chunk members or annotations changed"
      (map (Input.string_of o URust_AST.annotated_item_source) (URust_AST.chunk_items crlf) =
          ["fn ChunkCrlfA() {}", "fn ChunkCrlfB() {}"] andalso
        map (Option.map (Input.string_of o URust_AST.annotation_payload) o
            URust_AST.annotated_item_annotation) (URust_AST.chunk_items crlf) =
          [NONE, SOME "abbrev"])
  val command_first_line =
    quiet_prefix "" ^ "urust " ^ cartouche (a ^ "\n  fn ChunkCommandFirstLine() {}\n")
  val {result, ...} = capture true "command-first-line" \<^theory> command_first_line
  val message = failure_message "command-first-line" ["must start its own line"] result
  val _ =
    require "command first-line diagnostic is not at the annotation"
      (message_range message = range_of command_first_line a 0)
in
  val _ = writeln "attribute-line, command-line and CR LF placement audits passed"
end
\<close>


section\<open> Clause boundary of the chunk theory \<close>

text\<open>
Importing the chunk theory makes \<open>urust\<close> a command keyword. Here a \<open>simple_word_enum\<close>
declaration with a \<open>urust: "Name"\<close> clause splits at the keyword and is rejected; theories that
import only \<open>Parser_Impl_Command\<close> keep the clause (\<open>Parser_Simple_Word_Enum_Clause_Tests\<close>).
\<close>

ML\<open>
local
  open Chunk_Test
  val _ =
    require "urust is not a command keyword in a theory importing the chunk theory"
      (Keyword.is_command (Thy_Header.get_keywords' \<^context>) "urust")
  val clause =
    "simple_word_enum (8) chunk_clause_kind urust: \"ChunkClauseKind\" =\n" ^
    "  CCK_First = 1 | CCK_Second = 2\n"
  val {result, ...} = capture true "clause-limitation" \<^theory> clause
  val _ = failure_message "clause-limitation" ["Outer syntax error"] result
in
  val _ = writeln "the recorded clause limitation of the chunk theory is reproduced"
end
\<close>


section\<open> Validation before the first declaration \<close>

text\<open>
Every annotation payload, schema and option combination is validated before any member is
declared, so such a diagnostic of a later member wins over an elaboration failure of an earlier
member.
\<close>

ML\<open>
local
  open Chunk_Test
  val earlier_failure = "  fn ChunkValidatedBroken() -> bool { 1u32 }\n"
  fun case_ label later expected =
    let
      val text = quiet_prefix "" ^ "urust " ^ command_source (earlier_failure ^ later)
      val {result, ...} = capture true ("validated-" ^ label) \<^theory> text
    in ignore (failure_message ("validated " ^ label) expected result) end
  val _ =
    case_ "unknown" ("  " ^ annotation "colour" ^ "\n  fn ChunkValidatedLater() {}\n")
      ["unknown uRust command option \"colour\""]
  val _ =
    case_ "combination"
      ("  " ^ annotation "abbrev, application_def" ^ "\n  fn ChunkValidatedLater() {}\n")
      ["abbreviation mode cannot be combined"]
  val _ =
    case_ "anonymous-attrs"
      ("  " ^ annotation "name = _, attrs = [micro_rust_simps]" ^
        "\n  fn ChunkValidatedLater() {}\n")
      ["attrs is not supported for anonymous declarations"]
  val _ =
    case_ "unknown-attribute"
      ("  " ^ annotation "attrs = [chunk_no_such_attribute]" ^
        "\n  fn ChunkValidatedLater() {}\n")
      ["chunk_no_such_attribute"]
  val _ =
    case_ "rename-key"
      ("  " ^ annotation "renames = [\"missing\" \<rightarrow> \"a\"]" ^
        "\n  struct ChunkValidatedCell { value: u32 }\n")
      ["unknown rename key \"missing\""]
  val _ =
    case_ "type-alias" "  type ChunkValidatedAlias = u16;\n"
      ["type alias items are not chunk members"]
in
  val _ = writeln "annotation and option validation precede every declaration"
end
\<close>


section\<open> Later calls to unavailable members \<close>

ML\<open>
local
  open Chunk_Test
  fun rejects label body callee =
    let
      val text = quiet_prefix "" ^ "urust " ^ command_source body
      val {result, ...} = capture true label \<^theory> text
      val message =
        failure_message label ["unresolved body name " ^ quote callee] result
    in
      require (label ^ " diagnostic is not at the later body")
        (message_range message = range_of text ("{ " ^ callee ^ "() }") 0)
    end
  val _ =
    rejects "anonymous-call"
      ("  " ^ annotation "name = _" ^ "\n  fn ChunkHidden() -> u32 { 1 }\n" ^
        "  fn ChunkCallsHidden() -> u32 { ChunkHidden() }\n")
      "ChunkHidden"
  val _ =
    rejects "unregistered-call"
      ("  " ^ annotation "register_notation = false" ^ "\n  fn ChunkUnlisted() -> u32 { 1 }\n" ^
        "  fn ChunkCallsUnlisted() -> u32 { ChunkUnlisted() }\n")
      "ChunkUnlisted"
in
  val _ = writeln "later members cannot call anonymous or unregistered members"
end
\<close>


section\<open> Backend and plugin annotations take effect \<close>

ML\<open>
local
  open Chunk_Test
  val ctxt = \<^context>
  fun full_type name =
    dest_Type_name (Proof_Context.read_type_name {proper = true, strict = true} ctxt name)
  val _ =
    require "the backend = hol annotation was not applied"
      (is_some (BNF_FP_Def_Sugar.fp_sugar_of ctxt (full_type "chunk_native")) andalso
        is_none (BNF_FP_Def_Sugar.fp_sugar_of ctxt (full_type "chunk_choice")))
  val _ =
    require "the plugin filter annotation was not applied"
      (const_declared ctxt "chunk_word_to_u16_pure" andalso
        not (const_declared ctxt "chunk_word_to_u16") andalso
        const_declared ctxt "chunk_word_plugins_to_u16_pure" andalso
        const_declared ctxt "chunk_word_plugins_to_u16")
  val _ =
    require "the backend = enum annotation was not applied to a repr enum"
      (not (const_declared ctxt "chunk_repr_custom_to_u8_pure") andalso
        const_declared ctxt "chunk_repr_default_to_u8_pure")
  val payload_word =
    "#[repr(u8)]\n  enum ChunkPayloadWord { PayloadWord(u32) }\n"
  val annotated_payload =
    quiet_prefix "" ^ "urust " ^
      command_source ("  " ^ annotation "backend = \"simple_word_enum\"" ^ "\n  " ^ payload_word)
  val {result, ...} = capture true "simple-word-payload" \<^theory> annotated_payload
  val _ =
    failure_message "simple-word-payload"
      ["simple_word_enum requires an explicit width and no payload"] result
  val plain_payload = quiet_prefix "" ^ "urust " ^ command_source ("  " ^ payload_word)
  val _ = result_context (#result (capture true "plain-payload" \<^theory> plain_payload))
in
  val _ = writeln "backend, plugin and simple_word_enum annotations are applied"
end
\<close>


section\<open> Printed results and function definition entities \<close>

text\<open>
Installed results are restated in the returned context: verbosity-2 output carries no local
definition hypothesis, and each function name carries the definition entity of its HOL constant,
for single-item and chunk declarations in theory, locale and context targets.
\<close>

ML\<open>
local
  open Chunk_Test
  val prefix = "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 2]]\n"
  val zero = "  fn PrintedZero() -> u32 { 1 }"
  val argument = "  fn PrintedArgument(value: u32) -> u32 { value }"
  val chunk = "urust " ^ command_source (zero ^ "\n" ^ argument)
  val single =
    "urust_fn " ^ command_source zero ^ "\nurust_fn " ^ command_source argument
  fun in_locale body =
    "locale printed_loc =\n  fixes printed_param :: nat\nbegin\n" ^ body ^ "\nend\n"
  fun in_context body = "context\n  fixes printed_fixed :: nat\nbegin\n" ^ body ^ "\nend\n"
  (* Bound names of lexical locals carry fresh serials. *)
  fun normalize message =
    let
      fun strip (#"_" :: #"u" :: #"r" :: #"u" :: #"s" :: #"t" :: #"_" :: #"l" :: #"o" :: #"c" ::
            #"a" :: #"l" :: #"_" :: rest) =
            #"#" :: strip (drop_prefix Char.isDigit rest)
        | strip (c :: rest) = c :: strip rest
        | strip [] = []
    in String.implode (strip (String.explode message)) end
  fun definitions output =
    map normalize (filter (String.isPrefix "definition ") (authored_output output))
  val expected =
    ["definition printed_zero_def:\nprinted_zero \<equiv> FunctionBody (ascribeu32 1)",
     "definition printed_argument_def:\nprinted_argument \<equiv> \<lambda>#_value. " ^
       "FunctionBody (ascribeu32 #_value)"]
  fun constant_definitions text reports name occurrence =
    filter
      (fn (markup, properties) =>
        markup = Markup.entityN andalso
          Properties.get properties Markup.kindN = SOME Markup.constantN andalso
          is_some (Properties.get properties Markup.defN))
      (reports_at (range_of text name occurrence) reports)
  fun scenario label wrap body =
    let
      val text = prefix ^ wrap body
      val {result, output, reports, ...} = capture true label \<^theory> text
      val _ = result_context result
      val _ =
        require (label ^ " printed results changed:\n" ^ cat_lines (definitions output))
          (definitions output = (if String.isSubstring "PrintedArgument" body
                                 then expected else [hd expected]))
      val _ =
        require (label ^ " lost the constant definition entity at a function name")
          (length (constant_definitions text reports "PrintedZero" 0) = 1 andalso
            (not (String.isSubstring "PrintedArgument" body) orelse
              length (constant_definitions text reports "PrintedArgument" 0) = 1))
    in () end
  val _ = scenario "printed-theory-chunk" I chunk
  val _ = scenario "printed-theory-single" I single
  val _ = scenario "printed-locale-chunk" in_locale chunk
  val _ = scenario "printed-locale-single" in_locale single
  val _ = scenario "printed-context-chunk" in_context chunk
  val _ = scenario "printed-context-single" in_context single
  (* Expression definitions share the installation path. *)
  val expression = prefix ^ "urust_expr printed_expression " ^ cartouche " 1 "
  val {result, output, ...} = capture true "printed-expression" \<^theory> expression
  val _ = result_context result
  val _ =
    require ("expression definition output changed:\n" ^ cat_lines (definitions output))
      (definitions output = ["definition printed_expression_def:\nprinted_expression \<equiv> literal 1"])
in
  val _ = writeln "printed results and function definition entities match native definitions"
end
\<close>


section\<open> Definitions without a source binding position \<close>

ML\<open>
local
  open Chunk_Test
  fun definition_entities reports range =
    filter
      (fn (markup, properties) =>
        markup = Markup.entityN andalso is_some (Properties.get properties Markup.defN))
      (reports_at range reports)
  fun check label command =
    let
      val text = quiet_prefix "" ^ command ^ command_source "  struct UnboundCell { unboundValue: u32 }"
      val {result, reports, ...} = capture true label \<^theory> text
      val ctxt = result_context result
      val keyword_start = #1 (range_of text command 0)
      val keyword = (keyword_start, keyword_start + size (Symbol.trim_blanks command))
      val _ =
        require (label ^ " reported a regenerated definition at the command keyword")
          (null (definition_entities reports keyword))
      val _ = require (label ^ " lost its lens") (const_declared ctxt "unbound_cell_unbound_cell_unbound_value_lens")
    in () end
  val _ = check "unbound-chunk" "urust "
  val _ = check "unbound-single" "urust_datatype "
in
  val _ = writeln "regenerated definitions are reported only at proper binding positions"
end
\<close>

end
