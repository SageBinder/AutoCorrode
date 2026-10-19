(* ML audits for urust chunks and Rust use imports. The readable examples are in
   Parser_Chunk_Use_Examples. *)

theory Parser_Chunk_Use_ML_Tests
  imports
    Parser_Chunk_Use_Examples
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

ML\<open>
structure Parser_Use_Test =
struct
  structure S = URust_Import_Scope

  val layout = URust_AST.make_source_layout Position.none []
  fun segment name = (name, Position.none)
  fun leaf names alias =
    URust_AST.mk_use_path (map segment names, Option.map segment alias, layout)
  fun self_member alias = leaf ["self"] alias
  fun group prefix members = URust_AST.mk_use_group (map segment prefix, members, layout)
  fun item tree = URust_AST.mk_use_item (tree, layout)

  fun require label condition =
    if condition then () else error ("import regression: " ^ label)

  fun failure action =
    (case Exn.result action () of
       Exn.Res _ => NONE
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else SOME (Runtime.exn_message exn))

  fun rejects label expected action =
    (case failure action of
       NONE => error ("import regression: " ^ label ^ " was accepted")
     | SOME message =>
         require (label ^ " rejected for the wrong reason: " ^ message)
           (String.isSubstring expected message))

  fun lookup_key ctxt namespace alias =
    Option.map #key (S.lookup ctxt namespace alias)

  fun lookup_roles ctxt namespace alias =
    Option.map #roles (S.lookup ctxt namespace alias)

  fun batch trees = URust_Imports.validate_batch (map item trees)
  fun prepare_with policy ctxt trees = URust_Imports.prepare_batch policy ctxt (batch trees)
  fun prepare ctxt trees = prepare_with URust_Imports.Require_Targets ctxt trees

  fun cartouche body = Symbol.open_ ^ body ^ Symbol.close
  fun start label =
    Position.make0 1 1 0 "" label "" |> Position.copy_id (Position.thread_data ())
  fun initial thy = Toplevel.make_state (SOME thy)
  fun run_from state label text =
    let val thy = Toplevel.theory_of state
    in fold (Toplevel.command_exception true) (Outer_Syntax.parse_text thy (K thy) (start label) text) state end
  fun command_rejects thy label expected text =
    rejects label expected (fn () => run_from (initial thy) label text)
end
\<close>

chapter\<open> Source-ordered uRust chunks \<close>

section\<open> Locale contexts \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

ML_val \<open>
  @{assert} (is_none (URust_Item_Scope.lookup_function \<^context> "ChunkConfinedOne"));
  @{assert} (is_none (URust_Item_Scope.lookup_function \<^context> "ChunkConfinedTwo"))
\<close>

chapter\<open> Chunk audits \<close>

section\<open> Test support \<close>

text\<open>
Command-level audits run synthetic theory text in a private toplevel state. Positions carry
symbol offsets and the current PIDE command identity, so diagnostics and reports can be located exactly;
output, warnings and reports of that synthetic file are captured privately.
\<close>

ML\<open>
structure Chunk_Test =
struct
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  val omega = "\<omega>"
  fun annotation text = omega ^ cartouche text
  fun command_source text = cartouche ("\n" ^ text ^ "\n")

  fun start_position label =
    Position.make0 1 1 0 "" label ""
    |> Position.copy_id (Position.thread_data ())

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
  (* An outer channel option names the scoped default that shares a type across the chunk. *)
  val _ =
    List.app
      (fn option =>
        rejects ("outer-channel-" ^ option)
          ["option " ^ quote option, "or set the scoped urust_" ^ option ^ " default"]
          (chunk ("[" ^ option ^ " = " ^ cartouche "unit" ^ "] ") item) option 0)
      ["state", "abort", "input", "output"]
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

section\<open> The simple word enum clause next to the chunk command \<close>

text\<open>
Importing the chunk theory makes \<open>urust\<close> a command keyword. The \<open>simple_word_enum\<close> clause
is spelled \<open>urust_name: "Name"\<close>, so it stays one command and registers its source paths here;
the former \<open>urust: "Name"\<close> spelling splits at the keyword and is rejected.
\<close>

ML\<open>
local
  open Chunk_Test
  val _ =
    require "urust is not a command keyword in a theory importing the chunk theory"
      (Keyword.is_command (Thy_Header.get_keywords' \<^context>) "urust")
  fun clause keyword =
    "simple_word_enum (8) chunk_clause_kind " ^ keyword ^ " \"ChunkClauseKind\" =\n" ^
    "  CCK_First = 1 | CCK_Second = 2\n"
  val {result, ...} = capture true "clause-renamed" \<^theory> (clause "urust_name:")
  val ctxt = result_context result
  fun backend name =
    Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral ("ChunkClauseKind::" ^ name)
    |> map #hol_term
  val found =
    map (map (Long_Name.base_name o fst o dest_Const)) [backend "CCK_First", backend "CCK_Second"]
  val _ =
    require ("the urust_name: clause did not register the variant paths: " ^
        ML_Syntax.print_list (ML_Syntax.print_list ML_Syntax.print_string) found)
      (found = [["CCK_First"], ["CCK_Second"]])
  val {result, ...} = capture true "clause-former" \<^theory> (clause "urust:")
  val _ = failure_message "clause-former" ["Outer syntax error"] result
in
  val _ = writeln "the urust_name: clause works next to the chunk command; urust: is rejected"
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
  (* Bound names of lexical locals print with their source spellings. *)
  fun definitions output =
    filter (String.isPrefix "definition ") (authored_output output)
  val expected =
    ["definition printed_zero_def:\nprinted_zero \<equiv> FunctionBody (ascribeu32 1)",
     "definition printed_argument_def:\nprinted_argument \<equiv> \<lambda>value. " ^
       "FunctionBody (ascribeu32 value)"]
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
  (* Input abbreviations print without a local hypothesis and carry the definition entity of
     their installed constant at the Rust name. *)
  val abbreviation = "  fn PrintedAbbrev(value: u32) -> u32 { value }"
  val abbreviation_chunk =
    "urust " ^ command_source ("  " ^ annotation "abbrev" ^ "\n" ^ abbreviation)
  val abbreviation_single = "urust_fn [abbrev] " ^ command_source abbreviation
  fun abbreviation_scenario label wrap body =
    let
      val text = prefix ^ wrap body
      val {result, output, reports, ...} = capture true label \<^theory> text
      val _ = result_context result
      val printed = filter (String.isPrefix "abbreviation ") (authored_output output)
      val _ =
        require (label ^ " printed abbreviation changed:\n" ^ cat_lines printed)
          (case printed of
             [message] =>
               String.isPrefix "abbreviation printed_abbrev:\nprinted_abbrev \<equiv> " message andalso
                 not (String.isSubstring "[" message)
           | _ => false)
      val _ =
        require (label ^ " lost the constant definition entity at the abbreviation name")
          (length (constant_definitions text reports "PrintedAbbrev" 0) = 1)
    in () end
  val _ = abbreviation_scenario "abbreviation-theory-chunk" I abbreviation_chunk
  val _ = abbreviation_scenario "abbreviation-theory-single" I abbreviation_single
  val _ = abbreviation_scenario "abbreviation-locale-chunk" in_locale abbreviation_chunk
  val _ = abbreviation_scenario "abbreviation-locale-single" in_locale abbreviation_single
  val _ = abbreviation_scenario "abbreviation-context-chunk" in_context abbreviation_chunk
  val _ = abbreviation_scenario "abbreviation-context-single" in_context abbreviation_single
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

section\<open> Application definition argument names \<close>

text\<open>
Application definitions state source-spelled arguments without legacy name-binding warnings. A
parameter that is not an Isabelle identifier is desymbolized, and one that shadows a locale or
context fix is renamed away from it.
\<close>

ML\<open>
local
  open Chunk_Test
  val prefix = "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 2]]\n"
  val item = "  fn PrintedApplication(_unused: u32, shadowing: u32) -> u32 { shadowing }"
  val chunk = "urust " ^ command_source ("  " ^ annotation "application_def" ^ "\n" ^ item)
  val single = "urust_fn [application_def] " ^ command_source item
  fun in_locale body =
    "locale application_loc =\n  fixes shadowing :: nat\nbegin\n" ^ body ^ "\nend\n"
  fun in_context body = "context\n  fixes shadowing :: nat\nbegin\n" ^ body ^ "\nend\n"
  (* Definition theorems state their arguments schematically. *)
  fun expected argument =
    "definition printed_application_def:\nprinted_application ?x_unused ?" ^ argument ^
      " \<equiv> FunctionBody (ascribeu32 ?" ^ argument ^ ")"
  fun scenario label wrap argument body =
    let
      val {result, output, warnings, ...} = capture true label \<^theory> (prefix ^ wrap body)
      val _ = result_context result
      val printed = filter (String.isPrefix "definition ") (authored_output output)
      val _ =
        require (label ^ " emitted warnings:\n" ^ cat_lines warnings) (null warnings)
      val _ =
        require (label ^ " printed application definition changed:\n" ^ cat_lines printed)
          (printed = [expected argument])
    in () end
in
  val _ = scenario "application-theory-chunk" I "shadowing" chunk
  val _ = scenario "application-theory-single" I "shadowing" single
  val _ = scenario "application-locale-chunk" in_locale "shadowinga" chunk
  val _ = scenario "application-locale-single" in_locale "shadowinga" single
  val _ = scenario "application-context-chunk" in_context "shadowinga" chunk
  val _ = scenario "application-context-single" in_context "shadowinga" single
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

chapter\<open> Rust use imports \<close>

section\<open> Scope foundation \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

text\<open>
Direct tests of \<^ML_structure>\<open>URust_Import_Scope\<close> and \<^ML_structure>\<open>URust_Imports\<close>.
They construct use trees without parsing and check namespace membership, collisions, cycles,
confinement and stable identities.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val type_ns = S.Type_Namespace
  val value_ns = S.Value_Namespace
  val _ = require "theory imports retain no aliases from a fixture chunk"
    (is_none (S.lookup ctxt value_ns "fixture_step") andalso S.frame_depth ctxt = 0)

  val choice =
    prepare ctxt
      [group ["UseChoice"]
        [self_member (SOME "Selection"), leaf ["Empty"] NONE,
         leaf ["Value"] (SOME "Present"), leaf ["Named"] (SOME "Pick")]]
  val _ = require "grouped self imports the enum type"
    (lookup_roles choice type_ns "Selection" = SOME [S.Generated_Enum, S.Mapped_Type])
  val _ = require "grouped self imports no value" (is_none (S.lookup choice value_ns "Selection"))
  val _ = require "unit variant constructor"
    (lookup_roles choice value_ns "Empty" = SOME [S.Generated_Constructor])
  val _ = require "unit variant declaration"
    (lookup_roles choice type_ns "Empty" = SOME [S.Enum_Variant])
  val _ = require "renamed tuple variant"
    (lookup_key choice value_ns "Present" = SOME "UseChoice::Value")
  val _ = require "named variant has only its declaration identity"
    (is_none (S.lookup choice value_ns "Pick") andalso
      lookup_roles choice type_ns "Pick" = SOME [S.Enum_Variant])
  val _ = require "one identity per leaf"
    (#identity (the (S.lookup choice type_ns "Empty")) =
      #identity (the (S.lookup choice value_ns "Empty")))

  val shapes =
    prepare ctxt
      [leaf ["UsePacket"] NONE, leaf ["UseTuple"] NONE, leaf ["UseUnit"] NONE,
       leaf ["use_increment"] (SOME "inc"), leaf ["demo", "increment"] (SOME "call"),
       leaf ["demo", "WIDTH"] NONE, leaf ["demo", "ZERO"] NONE, leaf ["demo", "Width"] NONE,
       leaf ["demo", "Short"] NONE, leaf ["demo", "Cell"] NONE, leaf ["UseWrapper"] NONE]
  val _ = require "named struct has no value identity"
    (lookup_roles shapes type_ns "UsePacket" = SOME [S.Generated_Struct, S.Mapped_Type] andalso
      is_none (S.lookup shapes value_ns "UsePacket"))
  val _ = require "tuple and unit structs import both namespaces"
    (lookup_roles shapes value_ns "UseTuple" = SOME [S.Generated_Constructor] andalso
      lookup_roles shapes value_ns "UseUnit" = SOME [S.Generated_Constructor] andalso
      lookup_roles shapes type_ns "UseUnit" = SOME [S.Generated_Struct, S.Mapped_Type])
  val _ = require "generated function"
    (lookup_roles shapes value_ns "inc" = SOME [S.Generated_Function] andalso
      is_none (S.lookup shapes type_ns "inc"))
  val _ = require "exact notation roles"
    (lookup_roles shapes value_ns "call" = SOME [S.Call_Notation] andalso
      lookup_roles shapes value_ns "WIDTH" = SOME [S.Literal_Notation] andalso
      lookup_roles shapes value_ns "ZERO" = SOME [S.Literal_Notation])
  val _ = require "type mappings and aliases"
    (lookup_roles shapes type_ns "Width" = SOME [S.Mapped_Type] andalso
      lookup_roles shapes type_ns "Short" = SOME [S.Mapped_Type] andalso
      lookup_key shapes type_ns "Cell" = SOME "demo::Cell")

  val shared = prepare ctxt [leaf ["UsePacket"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")]
  val _ = require "distinct type and value bindings may share a spelling"
    (lookup_key shared type_ns "Pick" = SOME "UsePacket" andalso
      lookup_key shared value_ns "Pick" = SOME "demo::value")

  val _ = rejects "value imports with different notation roles" "duplicate value import"
    (fn () => prepare ctxt [leaf ["demo", "WIDTH"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "identical duplicate import" "duplicate import \"increment\""
    (fn () => prepare ctxt [leaf ["demo", "increment"] NONE, leaf ["demo", "increment"] NONE])
  val _ = rejects "tuple struct and function value collision" "duplicate value import"
    (fn () => prepare ctxt [leaf ["UseTuple"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "unit variant and function value collision" "duplicate value import"
    (fn () =>
      prepare ctxt [leaf ["UseChoice", "Empty"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "import cycle" "cyclic imports"
    (fn () => prepare ctxt [leaf ["Left"] (SOME "Right"), leaf ["Right"] (SOME "Left")])
  val _ = rejects "unused missing target" "unknown import target \"MissingTarget\""
    (fn () => prepare ctxt [leaf ["MissingTarget"] (SOME "Unused")])
  val _ = rejects "grouped self on a struct" "grouped `self` requires a generated enum"
    (fn () => prepare ctxt [group ["UsePacket"] [self_member (SOME "Selection")]])
  val _ = rejects "type aliases own no variants" "is not a generated enum"
    (fn () => prepare ctxt [leaf ["demo", "Short"] (SOME "Alias"), leaf ["Alias", "Empty"] NONE])
  val _ = rejects "unknown variant of an imported enum" "is not a variant of enum \"UseChoice\""
    (fn () => prepare ctxt [leaf ["UseChoice"] (SOME "C"), leaf ["C", "Missing"] NONE])
  val _ = rejects "field-only lens aliases" "field notation \"sample\" is outside the import surface"
    (fn () => prepare ctxt [leaf ["sample"] NONE])
  val _ = rejects "associated items" "unknown import target \"UsePacket::new\""
    (fn () => prepare ctxt [leaf ["UsePacket", "new"] NONE])
  val _ = rejects "variants own no nested items" "enum variants have no nested importable items"
    (fn () => prepare ctxt [leaf ["UseChoice"] (SOME "C"), leaf ["C", "Value", "inner"] NONE])

  val reverse =
    prepare ctxt
      [leaf ["Selection", "Value"] (SOME "Present"), leaf ["UseChoice"] (SOME "Selection")]
  val _ = require "same-batch dependency in reverse source order"
    (lookup_key reverse value_ns "Present" = SOME "UseChoice::Value")
  val existing = prepare ctxt [leaf ["use_increment"] NONE, leaf ["use_increment"] (SOME "again")]
  val _ = require "an import never resolves through itself"
    (lookup_key existing value_ns "again" = SOME "use_increment")

  val fixed_ctxt = #2 (Variable.add_fixes ["fixed_name"] ctxt)
  val _ = rejects "imports never capture fixed variables" "unknown import target \"fixed_name\""
    (fn () => prepare fixed_ctxt [leaf ["fixed_name"] (SOME "Captured")])

  val outer = prepare ctxt [leaf ["UseChoice"] (SOME "Selection"), leaf ["Selection", "Value"] (SOME "Present")]
  val inner = prepare outer [leaf ["UseOtherChoice"] (SOME "Selection")]
  val _ = require "frames are confined to derived contexts"
    (S.frame_depth ctxt = 0 andalso S.frame_depth outer = 1 andalso S.frame_depth inner = 2 andalso
      is_none (S.lookup ctxt type_ns "Selection"))
  val _ = require "an inner frame shadows its enclosing frame"
    (lookup_key inner type_ns "Selection" = SOME "UseOtherChoice" andalso
      lookup_key outer type_ns "Selection" = SOME "UseChoice")
  val _ = require "captured identities survive later shadowing"
    (lookup_key inner value_ns "Present" = SOME "UseChoice::Value")
  val per_namespace = prepare outer [leaf ["demo", "value"] (SOME "Selection")]
  val _ = require "shadowing is per namespace"
    (lookup_key per_namespace type_ns "Selection" = SOME "UseChoice" andalso
      lookup_key per_namespace value_ns "Selection" = SOME "demo::value")
in
  val _ = ()
end
\<close>

section\<open> Syntax and printing \<close>

text\<open>
Parser-only tests of the shared use-tree grammar for complete items and body statements, their
positioned rejections, exact symbol-counted ranges, recovery and printer roundtrips.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  open URust_AST
  val ctxt = \<^context>
  fun parse text =
    (case URust_Parser.parse_use_source ctxt (Parser_Lex_Util.text_source text) of
       SOME item => item
     | NONE => error ("empty use item " ^ quote text))
  fun body text =
    (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source text) of
       SOME expression => expression
     | NONE => error ("empty body " ^ quote text))
  fun leaves text =
    URust_Imports.flatten (parse text)
    |> map (fn leaf => (URust_Imports.leaf_path leaf, #1 (URust_Imports.leaf_alias leaf)))

  val _ = require "plain import" (leaves "use demo::increment;" = [(["demo", "increment"], "increment")])
  val _ = require "renamed import" (leaves "use demo::increment as inc;" = [(["demo", "increment"], "inc")])
  val _ = require "group import"
    (leaves "use demo::{increment as inc, Width};" =
      [(["demo", "increment"], "inc"), (["demo", "Width"], "Width")])
  val _ = require "enum self and renamed variants"
    (leaves "use UseChoice::{self as Selection, Empty, Value as Present};" =
      [(["UseChoice"], "Selection"), (["UseChoice", "Empty"], "Empty"),
       (["UseChoice", "Value"], "Present")])
  val _ = require "nested root group with trailing commas"
    (leaves "use {demo::{WIDTH, value,}, UseChoice::{self, Value as Present,},};" =
      [(["demo", "WIDTH"], "WIDTH"), (["demo", "value"], "value"),
       (["UseChoice"], "UseChoice"), (["UseChoice", "Value"], "Present")])
  val _ =
    (case use_item_tree (parse "use UseChoice::{self};") of
       Use_Group ([("UseChoice", _)], [Use_Self (_, NONE, _)], _) => ()
     | _ => error "grouped self is not represented explicitly")
  val _ =
    (case use_item_tree (parse "use demo::{ // comment\n increment /* block */ as inc };") of
       Use_Group (_, [Use_Path ([("increment", _)], SOME ("inc", _), _)], _) => ()
     | _ => error "comments inside a use tree changed its AST")

  fun reject_use (expected, text) =
    rejects ("use syntax " ^ quote text) expected (fn () => parse text)
  val _ =
    List.app reject_use
      [("glob imports (`*`) are not supported", "use demo::*;"),
       ("glob imports (`*`) are not supported", "use *;"),
       ("glob imports (`*`) are not supported", "use demo::{value, *};"),
       ("empty use groups are not supported", "use demo::{};"),
       ("empty use groups are not supported", "use {};"),
       ("rooted at `::`", "use ::demo::value;"),
       ("rooted at `crate`", "use crate::demo;"),
       ("rooted at `super`", "use super::demo;"),
       ("rooted at `self`", "use self::demo;"),
       ("rooted at `Self`", "use Self::Value;"),
       ("supported only as a grouped `{self}` import", "use demo::self;"),
       ("supported only as a grouped `{self}` import", "use self;"),
       ("supported only as a grouped `{self}` import", "use demo::{Choice::self};"),
       ("grouped `self` requires a group prefix", "use {self};"),
       ("underscore imports (`as _`) are not supported", "use demo::value as _;"),
       ("`_` is not a use path segment", "use demo::_;"),
       ("cannot be an import alias", "use demo::value as self;"),
       ("cannot be an import alias", "use demo::value as crate;"),
       ("cannot be a use path segment", "use demo::impl;"),
       ("generic arguments are not allowed in use paths", "use demo::Cell::<u8>;"),
       ("generic arguments are not allowed in use paths", "use demo::<u8>::Cell;"),
       ("visibility qualifiers (`pub use`) are not supported", "pub use demo::value;"),
       ("visibility qualifiers (`pub use`) are not supported", "pub(crate) use demo::value;"),
       ("unexpected `extern` before a use item", "extern use demo::value;"),
       ("syntax error", "use demo::value"),
       ("syntax error", "use demo::value as fn;"),
       ("syntax error", "use demo::{value as};"),
       ("syntax error", "use u8::MAX;"),
       ("syntax error", "use demo::shout!;"),
       ("syntax error", "use demo::{value,,};"),
       ("syntax error", "use demo::value; use demo::WIDTH;"),
       ("expected one complete use item", "type Width = u16;"),
       ("expected one complete use item", "fn probe() {}")]
  val _ =
    rejects "use item as a function" "urust_fn: expected a complete function item"
      (fn () => URust_Parser.parse_function_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ =
    rejects "use item as a datatype" "urust_datatype: expected a struct or enum item"
      (fn () => URust_Parser.parse_datatype_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ =
    rejects "use item as a type alias" "urust_type_alias: expected a complete type alias item"
      (fn () => URust_Parser.parse_type_alias_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ = require "recovery after a failed use item" (leaves "use demo::value;" = [(["demo", "value"], "value")])

  val _ =
    (case body "use demo::value; value()" of
       UE_Use (_, UE_Call _, _) => ()
     | _ => error "leading body import")
  val _ =
    (case body "{ use demo::value; }" of
       UE_Block (UE_Use (_, UE_Unit unit_layout, _), _) =>
         require "terminal import has a token-free unit continuation"
           (null (source_tokens unit_layout))
     | _ => error "import-only block")
  val _ =
    (case body "let x = 1; use demo::value; x" of
       UE_Let (_, _, UE_Use (_, UE_Path _, _), _) => ()
     | _ => error "import after a let")
  val _ =
    (case body "x; use demo::value; use demo::WIDTH;" of
       UE_Seq (_, UE_Use (_, UE_Use (_, UE_Unit _, _), _), _) => ()
     | _ => error "terminal imports after a statement")
  val _ =
    (case body "if c { use demo::value; value() } else { 0 }" of
       UE_If (_, UE_Block (UE_Use _, _), _, _) => ()
     | _ => error "branch block import")
  val _ = rejects "import as an operand" "syntax error" (fn () => body "1 + use demo::value;")
  val _ = rejects "import as a let initializer" "syntax error" (fn () => body "let x = use demo::value; x")
  val _ = rejects "body visibility" "visibility qualifiers (`pub use`) are not supported"
    (fn () => body "pub use demo::value; value()")
  val _ =
    (case body "x + 1" of
       UE_Bin _ => ()
     | _ => error "expression recovery after a failed body import")

  val positioned =
    Parser_Lex_Util.positioned_content_source
      "/* \<alpha>\<beta> */ use demo::{value as picked, UseChoice::{self}};"
      (Position.make0 1 7000 0 "" "" "use-syntax-positions")
  val text = Input.string_of positioned
  fun offset_of_text needle =
    let
      val (prefix, rest) = Substring.position needle (Substring.full text)
      val _ = if Substring.isEmpty rest then error ("missing " ^ needle) else ()
    in 7000 + length (Symbol.explode (Substring.string prefix)) end
  fun range_of needle =
    let val start = offset_of_text needle
    in (SOME start, SOME (start + length (Symbol.explode needle))) end
  fun offsets pos = (Position.offset_of pos, Position.end_offset_of pos)
  val positioned_item = the (URust_Parser.parse_use_source ctxt positioned)
  val positioned_leaves = URust_Imports.flatten positioned_item
  val _ = require "alias range after escaped symbols"
    (offsets (#2 (URust_Imports.leaf_alias (hd positioned_leaves))) = range_of "picked")
  val _ = require "grouped self alias range"
    (offsets (#2 (URust_Imports.leaf_alias (nth positioned_leaves 1))) = range_of "self")
  val _ = require "complete use item span"
    (offsets (use_item_position positioned_item) =
      (SOME (offset_of_text "use"), SOME (offset_of_text ";" + 1)))
  val _ =
    (case use_item_tree positioned_item of
       Use_Group ([("demo", demo_pos)], [Use_Path ([("value", value_pos)], _, path_layout), _], layout) =>
         (require "prefix segment range" (offsets demo_pos = range_of "demo");
          require "member segment range" (offsets value_pos = range_of "value");
          require "as keyword range"
            (map offsets (source_token_positions path_layout (Keyword_Token "as")) = [range_of "as"]);
          require "group delimiters"
            (length (source_token_positions layout (Delimiter_Token "{")) = 1 andalso
              length (source_token_positions layout (Delimiter_Token ",")) = 1))
     | _ => error "positioned use tree shape")

  fun roundtrip options text =
    let
      val original = parse text
      val rendered = URust_Printer.string_of_use_item options original
      val reparsed = parse rendered
    in
      require ("use item tokens changed for " ^ quote text ^ " rendered as " ^ quote rendered)
        (URust_Printer.tokens_of_use_item options original =
          URust_Printer.tokens_of_use_item options reparsed)
    end
  val roundtrip_items =
    ["use demo::increment;", "use demo::increment as inc;",
     "use demo::{increment as inc, Width};",
     "use UseChoice::{self as Selection, Empty, Value as Present};",
     "use {demo::{WIDTH, value,}, UseChoice::{self,},};"]
  val _ = List.app (roundtrip URust_Printer.serialized_options) roundtrip_items
  val _ = List.app (roundtrip URust_Printer.human_options) roundtrip_items
  val _ =
    require "canonical rendering"
      (URust_Printer.string_of_use_item URust_Printer.serialized_options
         (parse "use {demo::{WIDTH, value,}, UseChoice::{self as S,},};") =
        "use {demo::{WIDTH, value}, UseChoice::{self as S}};")
  fun body_roundtrip options text =
    let
      val original = body text
      val rendered = URust_Printer.string_of_expr options original
      val reparsed = body rendered
    in
      require ("body tokens changed for " ^ quote text ^ " rendered as " ^ quote rendered)
        (URust_Printer.tokens_of_expr options original =
          URust_Printer.tokens_of_expr options reparsed)
    end
  val roundtrip_bodies =
    ["use demo::value; value()", "{ use demo::value; }", "let x = 1; use demo::value; x",
     "x; use demo::value; use demo::WIDTH;",
     "match c { Present(n) => { use demo::value; n } _ => 0 }",
     "(use demo::value; 1)", "|x| { use demo::value as v; v() }"]
  val _ = List.app (body_roundtrip URust_Printer.serialized_options) roundtrip_bodies
  val _ = List.app (body_roundtrip URust_Printer.human_options) roundtrip_bodies
  val _ =
    URust_Printer_Output.pretty_human_use_item_with_reparse
      (fn input => ignore (URust_Parser.parse_use_source ctxt input))
      (parse "use UseChoice::{self as Selection, Value as Present};")
    |> ignore
in
  val _ = ()
end
\<close>

section\<open> Scoped imports \<close>

subsection\<open> Types \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun selector_type name = fastype_of (Syntax.read_term ctxt name) |> range_type
  val _ = require "imported datatype field types"
    (map selector_type
       ["use_imported_fields_width", "use_imported_fields_short", "use_imported_fields_cell"] =
     map selector_type
       ["use_qualified_fields_width", "use_qualified_fields_short", "use_qualified_fields_cell"])
in
  val _ = ()
end
\<close>

subsection\<open> Rejections without fallback \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
in
  val _ = command_rejects thy "variant as a parameter type" "names the enum variant \"UseChoice::Named\""
    ("urust " ^ cartouche " use UseChoice::Named as NamedVariant; fn bad(x: NamedVariant) {} ")
  val _ = command_rejects thy "generic arity through an import" "has generic arities [0, 2]"
    ("urust " ^ cartouche " use demo::Cell as Cell; fn bad(x: Cell<u8, u8>) {} ")
  val _ = command_rejects thy "unknown target" "unknown import target \"demo::Missing\""
    ("urust " ^ cartouche " use demo::{value as atomic_value, Missing}; ")
  val _ = command_rejects thy "use parse failure" "glob imports"
    ("urust " ^ cartouche " use demo::*; ")
  val _ = require "the persistent command keyword has been removed"
    (not (Keyword.is_command (Thy_Header.get_keywords thy) "urust_use"))
  val _ = rejects "the removed command cannot install imports" "Outer syntax error"
    (fn () => run_from (initial thy) "removed command"
      ("urust_use " ^ cartouche " use demo::value as removed_value; "))
  val recovered = run_from (initial thy) "recovered use"
    ("urust " ^ cartouche
      " use demo::value as recovered_value; fn UseRecovered() -> u32 { recovered_value() } ")
  val _ = require "recovery after a failed use declaration"
    (is_some (URust_Item_Scope.lookup_function (Toplevel.context_of recovered) "UseRecovered"))
  val _ = require "successful and failed declarations retain no aliases"
    (forall (is_none o S.lookup (Toplevel.context_of recovered) S.Value_Namespace)
      ["atomic_value", "recovered_value", "removed_value"] andalso
      S.frame_depth (Toplevel.context_of recovered) = 0)
end
\<close>

subsection\<open> Locales, experiments and interpretation \<close>

ML_val\<open>
  Parser_Use_Test.require "locale import is confined"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "LocaleWidth"))
\<close>

ML_val\<open>
  Parser_Use_Test.require "experiment import is confined"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "experiment_fetch"))
\<close>

ML_val\<open>
  Parser_Use_Test.require "interpretation retains no import aliases"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "LocaleWidth"))
\<close>

section\<open> Block imports \<close>

subsection\<open> Block rejections \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
  val ctxt = \<^context>
in
  val _ = command_rejects thy "body imports do not type the signature" "unknown Rust type \"LocalShortSig\""
    ("urust_fn _ " ^ cartouche " fn bad(x: LocalShortSig) { use demo::Short as LocalShortSig; } ")
  val escaped =
    Parser_Test_Elaboration.expression ctxt
      (Parser_Lex_Util.text_source "{ { use demo::value as inner_only; } inner_only() }")
  val _ = require "inner imports do not escape their block"
    (exists_subterm (fn Free ("inner_only", _) => true | _ => false) escaped andalso
      not (exists_Const (fn (name, _) => name = \<^const_name>\<open>use_demo_value_impl\<close>) escaped))
  val _ = rejects "declaration arguments are not import targets" "unknown import target \"argument\""
    (fn () => Parser_Test_Elaboration.expression_with_arguments ctxt [("argument", Position.none)]
      (Parser_Lex_Util.text_source "{ use argument as captured; 1 }"))
  val _ = require "block imports leave no binding in the enclosing context"
    (is_none (S.lookup ctxt S.Value_Namespace "local_inc") andalso
      is_none (S.lookup ctxt S.Value_Namespace "body_inc"))
end
\<close>

section\<open> Editor integration and replay \<close>

text\<open>
An import declaration reports keyword and delimiter markup, a definition and tooltip for each
alias, and references to its exact target registrations without selecting an overload. Each later
alias occurrence keeps its backend and type navigation and makes the import declaration its final
navigation target. Failed declarations replay no semantic reports, and replaying pretty output
or importing changes no registry inventory.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>

  fun markup_reports text =
    let
      val (result, chunks) =
        Parser_Test_Reports.chunks (fn () =>
          Exn.result (fn () => run_from (initial thy) "use-editor" text) ())
      (* The capture prepends each output chunk; restore emission order. *)
      val markups =
        maps YXML.parse_body (rev chunks)
        |> map_filter (fn XML.Elem (markup, _) => SOME markup | XML.Text _ => NONE)
    in (result, markups) end

  fun property name ((_, props): Markup.T) = AList.lookup (op =) props name
  fun occurrence text needle index =
    let
      fun find start remaining =
        let
          val (prefix, rest) = Substring.position needle (Substring.extract (text, start, NONE))
          val _ = if Substring.isEmpty rest then error ("missing " ^ needle) else ()
          val position = start + size (Substring.string prefix)
        in if remaining = 0 then position else find (position + size needle) (remaining - 1) end
    in 1 + length (Symbol.explode (String.substring (text, 0, find 0 index))) end
  fun at offset markup = property "offset" markup = SOME (Value.print_int offset)
  fun entity_kind (markup as (name, _): Markup.T) =
    if name = Markup.entityN then property Markup.kindN markup else NONE
  fun entities markups offset = filter (fn markup => at offset markup andalso is_some (entity_kind markup)) markups
  fun kinds markups offset = map (the o entity_kind) (entities markups offset)
  fun last_kind markups offset = try List.last (kinds markups offset)
  fun has markups offset name = exists (fn markup as (markup_name, _) => markup_name = name andalso at offset markup) markups
  fun definition markups offset =
    exists (fn markup => entity_kind markup = SOME "urust_import" andalso is_some (property "def" markup))
      (entities markups offset)
  fun import_reference_target markups offset =
    entities markups offset
    |> filter (fn markup => entity_kind markup = SOME "urust_import" andalso is_some (property "ref" markup))
    |> map (property "def_offset")

  val call_text =
    "urust_expr nav_call " ^ cartouche " use demo::increment as nav_inc; nav_inc(3) "
  val (call_result, call_markups) = markup_reports call_text
  val _ = require "navigation fixture succeeded" (is_some (Exn.get_res call_result))
  val alias = occurrence call_text "nav_inc" 0
  val use_site = occurrence call_text "nav_inc" 1
  val _ = require "alias definition" (definition call_markups alias)
  val _ = require "alias tooltip" (has call_markups alias Markup.typingN)
  val _ = require "use and as keywords"
    (has call_markups (occurrence call_text "use demo" 0) Markup.keyword1N andalso
      has call_markups (occurrence call_text "as nav_inc" 0) Markup.keyword1N)
  val _ = require "path and item delimiters"
    (has call_markups (occurrence call_text "::" 0) Markup.delimiterN andalso
      has call_markups (occurrence call_text ";" 0) Markup.delimiterN)
  val _ = require "target registration reference"
    (member (op =) (kinds call_markups (occurrence call_text "increment" 0)) Micro_Rust_Names.notationN)
  val _ = require "use site retains backend navigation"
    (member (op =) (kinds call_markups use_site) Micro_Rust_Names.notationN)
  val _ = require ("import declaration is the final use-site target: " ^
      commas (kinds call_markups use_site))
    (last_kind call_markups use_site = SOME "urust_import" andalso
      import_reference_target call_markups use_site = [SOME (Value.print_int alias)])

  val block_text = "urust_expr nav_block " ^ cartouche " { use demo::increment as blk; blk(1) } "
  val (_, block_markups) = markup_reports block_text
  val _ = require "block alias definition" (definition block_markups (occurrence block_text "blk" 0))
  val _ = require "block alias final target"
    (last_kind block_markups (occurrence block_text "blk" 1) = SOME "urust_import")
  val shadow_text =
    "urust_expr nav_shadow " ^
      cartouche " { let nav_pick = |x| x; { use demo::increment as nav_pick; nav_pick(1) } } "
  val (_, shadow_markups) = markup_reports shadow_text
  val shadow_site = occurrence shadow_text "nav_pick" 2
  val _ = require "a shadowing block import is the final target of its occurrence"
    (last_kind shadow_markups shadow_site = SOME "urust_import" andalso
      not (member (op =) (kinds shadow_markups shadow_site) "urust_var"))
  (* Exactly one of the import and the local is reported at each occurrence. *)
  fun winner label text needle index expect_import =
    let
      val (result, markups) = markup_reports text
      val _ = require (label ^ " succeeded") (is_some (Exn.get_res result))
      val site_kinds = kinds markups (occurrence text needle index)
      val has_import = member (op =) site_kinds "urust_import"
      val has_local = member (op =) site_kinds "urust_var"
    in
      require (label ^ " reports " ^ commas site_kinds)
        (if expect_import then has_import andalso not has_local else has_local andalso not has_import)
    end
  val _ = winner "inner local"
    ("urust_expr nav_inner_local " ^ cartouche " { use demo::increment as nav_q; let nav_q = |x| x; nav_q(1u32) } ")
    "nav_q" 2 false
  val _ = winner "range endpoint import"
    ("urust_expr nav_endpoint (x) " ^
      cartouche " { let nav_w = 0u32; { use demo::WIDTH as nav_w; match x { 0..=nav_w => 1u32, _ => 0 } } } ")
    "nav_w" 2 true
  val _ = winner "endpoint local inside the block"
    ("urust_expr nav_local_endpoint (x) " ^
      cartouche " { use demo::WIDTH as nav_e; let nav_e = 3u32; match x { 0..=nav_e => 1u32, _ => 0 } } ")
    "nav_e" 2 false
  val _ = winner "repeat length import"
    ("urust_expr nav_length " ^ cartouche " { let nav_n = 1u64; { use demo::COUNT as nav_n; [0u8; nav_n] } } ")
    "nav_n" 2 true
  val _ = winner "call import over an argument"
    ("urust_expr nav_argument (nav_s) " ^ cartouche " use demo::increment as nav_s; nav_s(1) ")
    "nav_s" 2 true
  val _ = winner "argument over a chunk alias"
    ("urust " ^ cartouche " use demo::WIDTH as nav_p; fn nav_alias_argument(nav_p: u32) -> u32 { nav_p } ")
    "nav_p" 2 false

  val type_text =
    "urust " ^ cartouche " use demo::Width as NavWord; fn nav_sig(x: NavWord) {} "
  val (_, type_markups) = markup_reports type_text
  val type_site = occurrence type_text "NavWord" 1
  val _ = require "type alias occurrence keeps its mapping and ends at the import"
    (member (op =) (kinds type_markups type_site) "micro_rust_type_mapping" andalso
      last_kind type_markups type_site = SOME "urust_import")

  val self_text = "urust " ^ cartouche " use UseChoice::{self as NavSelection}; "
  val (_, self_markups) = markup_reports self_text
  val self_pos = occurrence self_text "self" 0
  val _ = require "grouped self keyword and enum reference"
    (has self_markups self_pos Markup.keyword1N andalso
      member (op =) (kinds self_markups self_pos) "urust_item")

  val overload_text =
    "urust_expr nav_zero " ^ cartouche " use demo::ZERO as NavZero; NavZero + 1u64 "
  val (overload_result, overload_markups) = markup_reports overload_text
  val overload_ctxt = Toplevel.context_of (Exn.release overload_result)
  val wide_serial =
    Micro_Rust_Names.lookups overload_ctxt Micro_Rust_Names.NLiteral "demo::ZERO"
    |> filter (fn {hol_term, ...} : Micro_Rust_Names.entry =>
         Term.aconv_untyped (hol_term, \<^term>\<open>use_demo_zero_wide\<close>))
    |> map #serial
  val target = occurrence overload_text "ZERO" 0
  val _ = require "import declaration reports every candidate registration"
    (length (filter (fn kind => kind = Micro_Rust_Names.notationN) (kinds overload_markups target)) = 2)
  val overload_site = occurrence overload_text "NavZero" 1
  val selected =
    entities overload_markups overload_site
    |> filter (fn markup => entity_kind markup = SOME Micro_Rust_Names.notationN)
    |> map (property "ref")
  val _ = require "typed dispatch still selects the overload before the import target"
    (try List.last selected = SOME (Option.map Value.print_int (try hd wide_serial)) andalso
      last_kind overload_markups overload_site = SOME "urust_import")

  val rejected_text = "urust " ^ cartouche " use demo::{value as nav_rejected, Missing}; "
  val (rejected_result, rejected_markups) = markup_reports rejected_text
  val _ = require "rejected declaration fails" (is_none (Exn.get_res rejected_result))
  val _ = require "rejected declaration replays no semantic reports"
    (not (exists (is_some o entity_kind) rejected_markups))
  val rejected_block_text =
    "urust_expr nav_rejected_block " ^
      cartouche " { use demo::value as nav_dup; use demo::WIDTH as nav_dup; 1 } "
  val (rejected_block_result, rejected_block_markups) = markup_reports rejected_block_text
  val _ = require "rejected block import replays no import reports"
    (is_none (Exn.get_res rejected_block_result) andalso
      not (exists (fn markup => entity_kind markup = SOME "urust_import") rejected_block_markups))
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
  fun inventory ctxt =
    (length (URust_Item_Scope.dump_types ctxt), length (URust_Item_Scope.dump_constructors ctxt),
     length (URust_Item_Scope.dump_functions ctxt), length (URust_Type_Mappings.dump ctxt),
     length (Micro_Rust_Names.dump ctxt))
  fun output_of action =
    let
      val captured = Synchronized.var "use_pretty_output" ([]: string list)
      fun capture chunks = Synchronized.change captured (append chunks)
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Unsynchronized.setmp Private_Output.writeln_fn capture
            (Unsynchronized.setmp Private_Output.writeln_urgent_fn capture action) ())
    in (result, Synchronized.value captured |> map (XML.content_of o YXML.parse_body) |> cat_lines) end
  val start_state = initial thy
  val imported = run_from start_state "use-inventory" ("urust " ^ cartouche " use demo::value as inventory_value; ")
  val _ = require "imports leave item, type and notation registries unchanged"
    (inventory (Toplevel.context_of start_state) = inventory (Toplevel.context_of imported) andalso
      S.frame_depth (Toplevel.context_of imported) = 0 andalso
      is_none (S.lookup (Toplevel.context_of imported) S.Value_Namespace "inventory_value"))
  val (replayed, output) =
    output_of (fn () =>
      run_from imported "use-pretty"
        ("urust_fn [pretty, verbosity = 2] _ " ^
          cartouche " fn pretty_imports(x: u32) -> u32 { use demo::{increment as step, value as inventory_value}; step(inventory_value()) } "))
  val _ = require "pretty replay prints the body import"
    (String.isSubstring "increment as step" output)
  val _ = require "pretty replay leaves every inventory unchanged"
    (inventory (Toplevel.context_of replayed) = inventory (Toplevel.context_of imported) andalso
      S.frame_depth (Toplevel.context_of replayed) = 0)
in
  val _ = ()
end
\<close>

section\<open> Review regressions \<close>

subsection\<open> Import reports join the declaration transaction \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>\<open>Parser_Chunk_Use_Examples\<close>
  fun markup_reports text =
    let
      val (result, chunks) =
        Parser_Test_Reports.chunks (fn () =>
          Exn.result (fn () => run_from (initial thy) "use-review-reports" text) ())
      val markups =
        maps YXML.parse_body (rev chunks)
        |> map_filter (fn XML.Elem (markup, _) => SOME markup | XML.Text _ => NONE)
    in (result, markups) end
  fun property name ((_, props): Markup.T) = AList.lookup (op =) props name
  fun occurrence text needle index =
    let
      fun find start remaining =
        let
          val (prefix, rest) = Substring.position needle (Substring.extract (text, start, NONE))
          val _ = if Substring.isEmpty rest then error ("missing " ^ needle) else ()
          val position = start + size (Substring.string prefix)
        in if remaining = 0 then position else find (position + size needle) (remaining - 1) end
    in 1 + length (Symbol.explode (String.substring (text, 0, find 0 index))) end
  fun entity_kind (markup as (name, _): Markup.T) =
    if name = Markup.entityN then property Markup.kindN markup else NONE
  fun kinds markups offset =
    markups
    |> filter (fn markup => property "offset" markup = SOME (Value.print_int offset))
    |> map_filter entity_kind
  fun final_import label text needle index =
    let
      val (result, markups) = markup_reports text
      val found = kinds markups (occurrence text needle index)
    in
      require (label ^ " succeeded") (is_some (Exn.get_res result));
      require (label ^ " ends at the import: " ^ commas found)
        (length found >= 2 andalso try List.last found = SOME "urust_import")
    end
  fun no_import_reports label text =
    let val (result, markups) = markup_reports text in
      require (label ^ " fails") (is_none (Exn.get_res result));
      require (label ^ " replays no import reports")
        (not (exists (fn markup => entity_kind markup = SOME "urust_import") markups))
    end
in
  val _ = final_import "function body with chunk aliases"
    ("urust " ^ cartouche " use demo::{increment as inc, value as fetch}; fn nav_fn_chunk() -> u32 { inc(fetch()) } ")
    "inc" 2
  val _ = final_import "function body with a block alias"
    ("urust_fn nav_fn_block " ^
      cartouche " fn nav_fn_block() -> u32 { use demo::increment as fn_step; fn_step(1) } ")
    "fn_step" 1
  val _ = final_import "function body with a generated-function alias"
    ("urust_fn nav_fn_generated " ^
      cartouche " fn nav_fn_generated() -> u32 { use use_increment as fn_bump; fn_bump(1) } ")
    "fn_bump" 1
  val _ = no_import_reports "function failing at its HOL definition"
    ("urust_fn use_signature " ^
      cartouche " fn LateFunctionFailure() -> u32 { use demo::increment as late_step; late_step(1) } ")
  val _ = no_import_reports "expression failing at its HOL definition"
    ("urust_expr use_call " ^ cartouche " { use demo::increment as late_expr; late_expr(1) } ")
  val _ = no_import_reports "expression failing with a scoped alias"
    ("urust_expr use_literal " ^ cartouche " use demo::increment as inc; inc(1) ")
end
\<close>

subsection\<open> Two-phase batch preparation \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val type_ns = S.Type_Namespace
  val value_ns = S.Value_Namespace
  val allow = URust_Imports.Allow_Unavailable_Targets
  val require_targets = URust_Imports.Require_Targets
  fun elaborate context text = Parser_Test_Elaboration.expression context (Parser_Lex_Util.text_source text)

  val _ = rejects "validation rejects cycles without a context" "cyclic imports"
    (fn () => batch [leaf ["Left"] (SOME "Right"), leaf ["Right"] (SOME "Left")])
  val _ = rejects "validation rejects certain duplicates without a context" "duplicate import \"value\""
    (fn () => batch [leaf ["demo", "value"] NONE, leaf ["demo", "value"] NONE])
  val _ = require "validation keeps target-dependent spellings"
    (length (URust_Imports.batch_leaves
      (batch [leaf ["UsePacket"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])) = 2)

  val trees =
    [leaf ["demo", "value"] (SOME "ready"), leaf ["LaterItem"] (SOME "later"),
     leaf ["later"] (SOME "dependent"), leaf ["LaterItem", "Variant"] (SOME "later_variant")]
  val partial = prepare_with allow ctxt trees
  fun available alias namespace = Option.map #available (S.lookup partial namespace alias)
  val _ = require "available leaves resolve under the permissive policy"
    (lookup_key partial value_ns "ready" = SOME "demo::value" andalso available "ready" value_ns = SOME true)
  val _ = require "missing and dependent leaves are unavailable in both namespaces"
    (forall (fn alias => available alias type_ns = SOME false andalso available alias value_ns = SOME false)
      ["later", "dependent", "later_variant"])
  val _ = require "available uses are unaffected" (can (elaborate partial) "ready()")
  val _ = rejects "an unavailable call rejects without fallback"
    "import target \"LaterItem\" of \"later\" is not yet available" (fn () => elaborate partial "later()")
  val _ = rejects "an unavailable type rejects without fallback"
    "import target \"LaterItem\" of \"later\" is not yet available" (fn () => elaborate partial "1u8 as later")
  val _ = rejects "an unavailable pattern rejects without fallback" "is not yet available"
    (fn () => elaborate partial "match 1u32 { later => 1, _ => 0 }")
  val _ = rejects "an unavailable enum head rejects without fallback" "is not yet available"
    (fn () => elaborate partial "later::Value(1)")
  val _ = rejects "nested blocks require their outer targets" "is not yet available"
    (fn () => prepare partial [leaf ["later"] (SOME "inner")])
  val _ = rejects "the strict policy requires every target" "unknown import target \"LaterItem\""
    (fn () => prepare_with require_targets ctxt trees)
  val _ = rejects "existing unusable targets still reject" "field notation \"sample\""
    (fn () => prepare_with allow ctxt [leaf ["sample"] NONE])
  val _ = rejects "existing non-enum heads still reject" "is not a generated enum"
    (fn () => prepare_with allow ctxt [leaf ["demo", "Short"] (SOME "A"), leaf ["A", "X"] NONE])
  val _ = rejects "available duplicates still reject" "duplicate value import"
    (fn () => prepare_with allow ctxt [leaf ["UseTuple"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])

  val declared =
    URust_Item_Scope.register_function
      {rust_name = "LaterItem", rust_pos = Position.none, function = \<^term>\<open>use_increment\<close>}
      (Named_Target.theory_init \<^theory>)
  val completed = prepare_with require_targets declared (take 3 trees)
  val _ = require "re-preparing the validated batch after the target appears"
    (lookup_roles completed value_ns "later" = SOME [S.Generated_Function] andalso
      lookup_key completed value_ns "dependent" = SOME "LaterItem")
in
  val _ = ()
end
\<close>

subsection\<open> Body visibility and reserved keywords \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun parse text = URust_Parser.parse_use_source ctxt (Parser_Lex_Util.text_source text)
  val positioned =
    Parser_Lex_Util.positioned_content_source "{ pub(self) use demo::value; 1 }"
      (Position.make0 1 9000 0 "" "" "use-review-visibility")
  val message =
    the_default "" (failure (fn () => URust_Parser.parse_source ctxt positioned))
in
  val _ = rejects "item visibility with a path" "visibility qualifiers (`pub use`) are not supported"
    (fn () => parse "pub(in demo) use demo::value;")
  val _ = require ("body visibility is positioned at pub: " ^ message)
    (String.isSubstring "visibility qualifiers" message andalso
      String.isSubstring (Value.print_int 9002) message)
  val _ =
    List.app
      (fn keyword =>
        (rejects ("reserved alias " ^ keyword) "cannot be an import alias"
           (fn () => parse ("use demo::value as " ^ keyword ^ ";"));
         rejects ("reserved segment " ^ keyword) "cannot be a use path segment"
           (fn () => parse ("use demo::" ^ keyword ^ ";"))))
      ["abstract", "become", "box", "do", "final", "gen", "macro", "override", "priv", "try",
       "typeof", "unsized", "virtual", "yield"]
end
\<close>

subsection\<open> Scopes outside the continuation spine \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun elaborate text =
    Parser_Test_Elaboration.expression_with_arguments ctxt [("choice", Position.none)]
      (Parser_Lex_Util.text_source text)
  fun confined label alias text =
    let val term = elaborate text in
      require (label ^ " keeps its import confined")
        (exists_subterm (fn Free (name, _) => name = alias | _ => false) term)
    end
in
  val _ = confined "let-else fallback" "fallback_only"
    "{ let UseChoice::Value(n) = choice else { use demo::value as fallback_only; return fallback_only(); }; fallback_only() }"
  val _ = confined "loop body" "loop_only"
    "{ for i in 0u32..3 { use demo::increment as loop_only; loop_only(i); } loop_only(1) }"
  val _ = confined "match arm" "arm_only"
    "{ let m = match choice { UseChoice::Empty => { use demo::value as arm_only; arm_only() }, _ => 0 }; arm_only() }"
  val _ = confined "closure body" "closure_only"
    "{ let f = || { use demo::value as closure_only; closure_only() }; closure_only() }"
end
\<close>

subsection\<open> Source conventions \<close>

ML_val\<open>
local
  val master = Resources.master_directory \<^theory>
  fun ascii_only relative =
    let val text = File.read (master + Path.explode relative) in
      Parser_Use_Test.require ("raw non-ASCII text in " ^ relative)
        (forall (fn character => Char.ord character < 128) (String.explode text))
    end
in
  val _ =
    List.app ascii_only
      (map (fn name => "../Micro_Rust_Parser_Impl/" ^ name ^ ".thy")
        ["Parser_Impl_AST", "Parser_Impl_Import_Scope", "Parser_Impl_Imports",
         "Parser_Impl_Item_Scope", "Parser_Impl_Type_Mappings", "Parser_Impl_Grammar",
         "Parser_Impl_Resolution", "Parser_Impl_Case_Compiler", "Parser_Impl_Patterns",
         "Parser_Impl_Translate", "Parser_Impl_Command", "Parser_Impl_Printer",
         "Parser_Impl_Printer_Output"] @
       map (fn name => name ^ ".thy")
        ["Parser_Chunk_Use_Examples", "Parser_Chunk_Use_ML_Tests"])
end
\<close>

chapter\<open> Imports in source-ordered chunks \<close>

section\<open> Signatures, fields, calls, construction and patterns \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun selector_type name = fastype_of (Syntax.read_term ctxt name) |> range_type
in
  val _ = require "chunk alias field types"
    (map selector_type
       ["chunk_import_holder_choice", "chunk_import_holder_word", "chunk_import_holder_tuple"] =
     map selector_type
       ["chunk_import_holder_control_choice", "chunk_import_holder_control_word",
        "chunk_import_holder_control_tuple"])
end
\<close>

section\<open> Alias absence after the command \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val aliases =
    ["step", "fetch", "Width_Value", "helper", "ChunkImportPair", "Choice", "Present",
     "Absent", "Tuple1", "Word", "local_step", "only_value", "increment", "chunk_import_pick"]
in
  val _ = require "no block frame survives a chunk" (S.frame_depth ctxt = 0)
  val _ = require "no chunk alias survives its chunk"
    (forall (fn alias =>
        is_none (S.lookup ctxt S.Type_Namespace alias) andalso
        is_none (S.lookup ctxt S.Value_Namespace alias)) aliases)
  (* A later command reads the former alias as an unresolved HOL name. *)
  val later =
    Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source "step(fetch())")
  val _ = require "a later command does not resolve a chunk alias"
    (forall (fn alias => exists_subterm (fn Free (name, _) => name = alias | _ => false) later)
      ["step", "fetch"])
end
\<close>

section\<open> Audits \<close>

text\<open>
Command-level audits run synthetic theory text in a private toplevel state with the support of
\<^ML_structure>\<open>Chunk_Test\<close>; their positions carry symbol offsets and the current command ID.
\<close>

micro_rust_notation (call) use_demo_value_impl ("chunk_import_fallback")

ML\<open>
structure Chunk_Use_Audit =
struct
  open Chunk_Test
  val quiet = quiet_prefix ""
  val loud = "declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]\n"
  fun chunk body = "urust " ^ command_source body

  (* A rejected chunk run in the given theory: the diagnostic and the captured command effects.
     Callers pass the theory of their own position, so later fixtures are visible. *)
  fun rejected thy label expected text =
    let
      val {result, output, warnings, reports} = capture true label thy text
      val message = failure_message label expected result
    in {message = message, output = output, warnings = warnings, reports = reports} end

  fun rejects thy label expected body = #message (rejected thy label expected (quiet ^ chunk body))

  (* The diagnostic is positioned at the nth occurrence of needle in the command text. *)
  fun rejects_at thy label expected body needle occurrence =
    let
      val text = quiet ^ chunk body
      val message = #message (rejected thy label expected text)
    in
      require (label ^ " positioned at " ^ quote needle ^ ": " ^ plain message)
        (message_range message = range_of text needle occurrence)
    end

  fun import_entities reports =
    report_events reports
    |> filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_import")

  fun run_success thy label text =
    let val {result, output, warnings, reports} = capture true label thy text
    in {ctxt = result_context result, output = output, warnings = warnings, reports = reports} end
end
\<close>

subsection\<open> Targets declared later or never \<close>

urust_type "ChunkShadowSplit" = \<open> nat \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
in
  (* The alias is unavailable before its target is declared and does not fall back to the
     call registration of the same name. *)
  val _ = rejects_at \<^theory> "later target"
    ["import target \"ChunkImportSecond\" of \"chunk_import_fallback\" is not yet available"]
    ("  fn ChunkImportFirst() -> u32 { chunk_import_fallback() }\n" ^
     "  use ChunkImportSecond as chunk_import_fallback;\n" ^
     "  fn ChunkImportSecond() -> u32 { 2 }\n")
    "chunk_import_fallback" 0
  val _ = rejects_at \<^theory> "member declared after its user"
    ["import target \"ChunkImportHelperTwo\" of \"helper_two\" is not yet available"]
    ("  fn ChunkImportTooEarly(x: u32) -> u32 { helper_two(x) }\n" ^
     "  fn ChunkImportHelperTwo(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportHelperTwo as helper_two;\n")
    "helper_two" 0
  val _ = rejects_at \<^theory> "member importing itself"
    ["import target \"ChunkImportItself\" of \"itself\" is not yet available"]
    ("  fn ChunkImportItself(x: u32) -> u32 { itself(x) }\n" ^
     "  use ChunkImportItself as itself;\n")
    "itself" 0
  val _ = rejects_at \<^theory> "later datatype field type"
    ["import target \"ChunkImportLaterStruct\" of \"LaterType\" is not yet available"]
    ("  struct ChunkImportEarlyField { field: LaterType }\n" ^
     "  use ChunkImportLaterStruct as LaterType;\n" ^
     "  struct ChunkImportLaterStruct { value: u32 }\n")
    "LaterType" 0
  val _ = rejects_at \<^theory> "later signature type"
    ["import target \"ChunkImportLaterSignature\" of \"LaterSignature\" is not yet available"]
    ("  fn ChunkImportEarlySignature(value: LaterSignature) -> u32 { 1 }\n" ^
     "  use ChunkImportLaterSignature as LaterSignature;\n" ^
     "  struct ChunkImportLaterSignature { value: u32 }\n")
    "LaterSignature" 0
  (* A body import of a chunk alias whose value is declared later shadows a same-named parameter in
     the value namespace and rejects without falling back to the parameter. *)
  val _ = rejects_at \<^theory> "body import shadowing a parameter"
    ["is not yet available"]
    ("  use ChunkShadowSplit as chunk_shadow_split;\n" ^
     "  fn ChunkShadowSplitUser(chunk_split_param: u32) -> u32 {\n" ^
     "    use chunk_shadow_split as chunk_split_param;\n" ^
     "    chunk_split_param(1)\n" ^
     "  }\n" ^
     "  fn ChunkShadowSplit(value: u32) -> u32 { value }\n")
    "chunk_split_param" 2
  val _ = rejects_at \<^theory> "body import depending on a later target"
    ["import target \"ChunkImportLaterBody\" of \"later_body\" is not yet available"]
    ("  fn ChunkImportBodyEarly() -> u32 { use later_body as inner_body; inner_body() }\n" ^
     "  use ChunkImportLaterBody as later_body;\n" ^
     "  fn ChunkImportLaterBody() -> u32 { 3 }\n")
    "later_body" 0
  val _ = rejects_at \<^theory> "never-declared target"
    ["unknown import target \"ChunkImportNever\""]
    ("  fn ChunkImportOrphanUser() -> u32 { 1 }\n" ^
     "  use ChunkImportNever as never;\n")
    "ChunkImportNever" 0
end
\<close>

text\<open> Reordered, the chunk whose first member was rejected above succeeds. \<close>

urust \<open>
  fn ChunkImportSecond() -> u32 { 2 }

  use ChunkImportSecond as chunk_import_fallback;

  fn ChunkImportFirst() -> u32 { chunk_import_fallback() }
\<close>

urust_fn \<open> fn ChunkImportFirstControl() -> u32 { ChunkImportSecond() } \<close>

lemma \<open> chunk_import_first = chunk_import_first_control \<close>
  unfolding chunk_import_first_def chunk_import_first_control_def by (rule refl)

subsection\<open> Validation before the first declaration \<close>

text\<open>
Each chunk below starts with a member whose body fails typing. The import diagnostic is reported
instead, because the batch is validated, and prepared for the first member, before that member is
declared.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  val _ = rejects_at \<^theory> "duplicate import" ["duplicate import \"value\""]
    (broken ^ "  use demo::value;\n  use demo::value;\n") "value" 1
  val _ = rejects \<^theory> "cyclic imports" ["cyclic imports"]
    (broken ^ "  use chunk_left as chunk_right;\n  use chunk_right as chunk_left;\n")
  val _ = rejects_at \<^theory> "duplicate value import" ["duplicate value import \"dup\""]
    (broken ^ "  use demo::value as dup;\n  use UseTuple as dup;\n") "dup" 1
  val _ = rejects \<^theory> "unusable target" ["field notation \"sample\""]
    (broken ^ "  use sample;\n")
  val _ = rejects_at \<^theory> "glob import" ["glob imports (`*`) are not supported"]
    (broken ^ "  use demo::*;\n") "*" 0
  val _ = rejects_at \<^theory> "visibility" ["visibility qualifiers (`pub use`) are not supported"]
    (broken ^ "  pub use demo::value;\n") "pub" 0
  val _ = rejects_at \<^theory> "rooted path" ["`crate`"]
    (broken ^ "  use crate::value;\n") "crate" 0
  val _ =
    let
      val body = broken ^ "  " ^ annotation "pretty" ^ "\n  use demo::value;\n"
      val text = quiet ^ chunk body
      val message =
        #message (rejected \<^theory> "annotated use" ["an \<omega> annotation cannot precede a use item"] text)
      val (start, _) = range_of text omega 0
      val (_, stop) = range_of text (Symbol.close ^ "\n  use") 0
    in
      require ("annotated use positioned at the annotation: " ^ plain message)
        (message_range message = (start, stop - 6))
    end
end
\<close>

subsection\<open> Namespace-precise forward targets \<close>

text\<open>
Each declaration's preparation knows the registry entities that it and the later members will
declare, as their declaration backends report them from the decisions they declare with:
datatype types and mappings, constructors and enum variants, the conversion call notations of the
native \<open>simple_word_enum\<close> backend under its plugin filter, and the call keys of registered
functions. An entity among them is unavailable in its own namespace only; an entity that already
exists keeps resolving, and a target that neither exists nor is declared with a Rust registration
is unknown at its path before the first declaration.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val lthy = Named_Target.theory_init \<^theory>
  (* Members with every backend and plugin choice that changes registrations. *)
  val members =
    [("ChunkPredReprEight", "verbosity = 0",
       "#[repr(u8)]\n  enum ChunkPredReprEight { Low = 1, High = 4 }"),
     ("ChunkPredReprSixteen", "verbosity = 0",
       "#[repr(u16)]\n  enum ChunkPredReprSixteen { Low, High }"),
     ("ChunkPredWord", "backend = \"simple_word_enum\", word_width = 16",
       "enum ChunkPredWord { Low = 1, High = 2 }"),
     ("ChunkPredWordOnly",
       "backend = \"simple_word_enum\", word_width = 16, plugins = (plugins only: word_conversion)",
       "enum ChunkPredWordOnly { Low = 1, High = 2 }"),
     ("ChunkPredReprDel", "plugins = (plugins del: urust_conversion)",
       "#[repr(u8)]\n  enum ChunkPredReprDel { Low = 1, High = 2 }"),
     ("ChunkPredReprEnum", "backend = \"enum\"",
       "#[repr(u8)]\n  enum ChunkPredReprEnum { Low = 1, High = 2 }"),
     ("ChunkPredReprHidden", "register_notation = false",
       "#[repr(u8)]\n  enum ChunkPredReprHidden { Low = 1, High = 2 }"),
     ("ChunkPredHol", "backend = hol",
       "enum ChunkPredHol { Empty, Value(u32), Named { sample: u32 } }"),
     ("ChunkPredChoice", "verbosity = 0",
       "enum ChunkPredChoice { Empty, Value(u32), Named { sample: u32 } }"),
     ("ChunkPredPacket", "verbosity = 0", "struct ChunkPredPacket { sample: u32 }"),
     ("ChunkPredTuple", "verbosity = 0", "struct ChunkPredTuple(u32);"),
     ("ChunkPredUnit", "verbosity = 0", "struct ChunkPredUnit;"),
     ("ChunkPredWrapper", "verbosity = 0", "struct ChunkPredWrapper<T> { inner: T }"),
     ("ChunkPredEmpty", "verbosity = 0", "struct ChunkPredEmpty {}"),
     ("ChunkPredFn", "verbosity = 0", "fn ChunkPredFn(x: u32) -> u32 { x + 1 }"),
     ("ChunkPredHiddenFn", "register_notation = false",
       "fn ChunkPredHiddenFn(x: u32) -> u32 { x }"),
     ("ChunkPredAnonFn", "name = _", "fn ChunkPredAnonFn(x: u32) -> u32 { x }")]
  fun member_text (_, payload, item) = annotation payload ^ "\n  " ^ item ^ "\n"
  val declared =
    #ctxt (run_success \<^theory> "chunk-prediction"
      (quiet ^ chunk (implode (map (fn member => "  " ^ member_text member) members))))
  (* The prediction a chunk makes before declaring the member, in the enclosing context. *)
  fun prediction member =
    let
      val envelope =
        hd (URust_AST.chunk_items (the_chunk lthy "chunk-prediction-member" (member_text member)))
      val annotation = the (URust_AST.annotated_item_annotation envelope)
      val source = URust_AST.annotated_item_source envelope
      fun read schema = URust_Command.read_annotation_options lthy schema annotation
      val registrations =
        (case URust_AST.annotated_item_item envelope of
           URust_AST.Function_Item_Node function =>
             URust_Command.prepared_function_registrations
               (URust_Command.prepare_function_item lthy
                 {interactive = false, roundtrip = false,
                  options = read URust_Command.Function_Annotation,
                  source = source, function = function})
         | URust_AST.Datatype_Item item =>
             URust_Command.prepared_datatype_registrations lthy
               (URust_Command.prepare_datatype_item lthy
                 {interactive = false, roundtrip = false,
                  options = read URust_Command.Datatype_Annotation, source = source, item = item})
         | _ => error "chunk prediction audit: unexpected member")
    in URust_Imports.registration_entities registrations end
  (* Every registry entry that declaring the member added under its Rust name. *)
  fun observed name =
    let
      val {notations, types, constructors, functions, mappings} = registry_snapshot declared
      fun own key = key = name orelse String.isPrefix (name ^ "::") key
      val keys =
        distinct (op =)
          (filter own (map #2 notations @ types @ constructors @ functions @ mappings))
    in
      maps (URust_Imports.registration_entities o URust_Imports.installed_registrations declared)
        keys
    end
  fun triple ({key, namespace, roles}: URust_Imports.entity) = (key, namespace, roles)
  fun render entities =
    commas (map (fn (key, namespace, roles) =>
      key ^ "/" ^ URust_Import_Scope.namespace_name namespace ^ "/" ^
        space_implode "+" (map URust_Import_Scope.role_name roles)) entities)
  fun check (member as (name, _, _)) =
    let
      val predicted = map triple (prediction member)
      val actual = map triple (observed name)
    in
      require ("predicted registrations of " ^ name ^ ": " ^ render predicted ^
          "\nactual registrations: " ^ render actual)
        (eq_set (op =) (predicted, actual))
    end
  val _ = List.app check members
  fun predicts member key = exists (fn entity => #key entity = key) (prediction member)
  val _ = require "repr enums predict their conversion calls"
    (predicts (nth members 0) "ChunkPredReprEight::to_u8" andalso
      predicts (nth members 0) "ChunkPredReprEight::try_from" andalso
      predicts (nth members 1) "ChunkPredReprSixteen::to_u16" andalso
      predicts (nth members 2) "ChunkPredWord::to_u16" andalso
      predicts (nth members 6) "ChunkPredReprHidden::to_u8")
  val _ = require "plugin filters and other backends predict no conversion call"
    (not (predicts (nth members 3) "ChunkPredWordOnly::to_u16") andalso
      not (predicts (nth members 4) "ChunkPredReprDel::to_u8") andalso
      not (predicts (nth members 5) "ChunkPredReprEnum::to_u8"))
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val type_ns = S.Type_Namespace
  val value_ns = S.Value_Namespace
  val later =
    URust_Imports.Declared_Later
      [{key = "LaterItem", namespace = value_ns, roles = [S.Generated_Function]},
       {key = "UseChoice", namespace = value_ns, roles = [S.Generated_Function]},
       {key = "LaterEnum", namespace = type_ns, roles = [S.Generated_Enum, S.Mapped_Type]},
       {key = "LaterEnum::Ready", namespace = type_ns, roles = [S.Enum_Variant]},
       {key = "LaterEnum::Ready", namespace = value_ns, roles = [S.Generated_Constructor]}]
  val partial =
    prepare_with later ctxt
      [leaf ["LaterItem"] (SOME "later"), leaf ["UseChoice"] (SOME "both"),
       leaf ["later"] (SOME "dependent"), leaf ["LaterEnum"] (SOME "Enum"),
       leaf ["Enum", "Ready"] (SOME "ready"), group ["LaterEnum"] [self_member (SOME "Grouped")]]
  fun availability alias namespace = Option.map #available (S.lookup partial namespace alias)
  val _ = require "a later value entity is unavailable in the value namespace only"
    (availability "later" value_ns = SOME false andalso availability "later" type_ns = NONE andalso
      availability "dependent" value_ns = SOME false andalso
      availability "dependent" type_ns = NONE)
  val _ = require "an existing entity keeps resolving beside a later one"
    (lookup_roles partial type_ns "both" = SOME [S.Generated_Enum, S.Mapped_Type] andalso
      availability "both" value_ns = SOME false)
  val _ = require "a later enum qualifies exactly its declared variants"
    (availability "Enum" type_ns = SOME false andalso
      availability "Grouped" type_ns = SOME false andalso
      availability "ready" type_ns = SOME false andalso availability "ready" value_ns = SOME false)
  val _ = rejects "a variant the later enum does not declare" "\"Missing\" is not a variant of enum"
    (fn () => prepare_with later ctxt
      [leaf ["LaterEnum"] (SOME "Enum"), leaf ["Enum", "Missing"] (SOME "missing")])
  val _ = rejects "a target neither existing nor declared" "unknown import target \"NeverItem\""
    (fn () => prepare_with later ctxt [leaf ["NeverItem"] (SOME "never")])
in
  val _ = ()
end
\<close>

urust_datatype \<open> enum ChunkImportFE { A } \<close>

micro_rust_notation (call) use_demo_value_impl ("ChunkImportFBoth")

urust_type "ChunkImportFT" = \<open> nat \<close>

micro_rust_notation (call) use_demo_value_impl ("ChunkImportFT2")

urust_datatype \<open> enum ChunkImportFG { A } \<close>

urust_fn \<open> fn ChunkImportFG2() -> u32 { 3 } \<close>

urust_datatype \<open> enum ChunkImportFN { A } \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  fun later_value label target alias =
    rejects_at \<^theory> label
      ["import target " ^ quote target ^ " of " ^ quote alias ^ " is not yet available"]
      ("  fn " ^ target ^ "Early() -> u32 { " ^ alias ^ "() }\n" ^
       "  use " ^ target ^ " as " ^ alias ^ ";\n" ^
       "  fn " ^ target ^ "() -> u32 { 7 }\n" ^
       "  fn " ^ target ^ "Late() -> u32 { " ^ alias ^ "() }\n")
      alias 0
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  (* The target's type entity exists; its value entity is declared later. The earlier value use
     neither falls back to a call registration or an outer item of the alias spelling nor reads an
     unresolved name. *)
  val _ = later_value "enum with a later function, call-registration fallback"
    "ChunkImportFE" "ChunkImportFBoth"
  val _ = later_value "type mapping with a later function, call-registration fallback"
    "ChunkImportFT" "ChunkImportFT2"
  val _ = later_value "enum with a later function, outer item fallback"
    "ChunkImportFG" "ChunkImportFG2"
  val _ = later_value "enum with a later function, no fallback" "ChunkImportFN" "ChunkImportFNAlias"
  (* Targets without a Rust registration are unknown at their path, before the first declaration. *)
  val _ = rejects_at \<^theory> "unregistered function target" ["unknown import target \"ChunkImportHidden\""]
    (broken ^ "  " ^ annotation "register_notation = false" ^ "\n" ^
     "  fn ChunkImportHidden(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportHidden as hidden;\n" ^
     "  fn ChunkImportHiddenUser() -> u32 { hidden(1) }\n")
    "ChunkImportHidden" 1
  val _ = rejects_at \<^theory> "anonymous function target" ["unknown import target \"ChunkImportAnonymous\""]
    (broken ^ "  " ^ annotation "name = _" ^ "\n" ^
     "  fn ChunkImportAnonymous(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportAnonymous as anonymous;\n" ^
     "  fn ChunkImportAnonymousUser() -> u32 { anonymous(1) }\n")
    "ChunkImportAnonymous" 1
  val _ = rejects_at \<^theory> "never-declared target used by an earlier member"
    ["unknown import target \"ChunkImportNeverDeclared\""]
    (broken ^ "  fn ChunkImportNeverUser() -> u32 { never_declared(1) }\n" ^
     "  use ChunkImportNeverDeclared as never_declared;\n")
    "ChunkImportNeverDeclared" 0
  val _ = rejects_at \<^theory> "missing variant of a later enum"
    ["unknown import target \"ChunkImportLaterEnum::Missing\""]
    (broken ^ "  use ChunkImportLaterEnum::Missing as missing_variant;\n" ^
     "  enum ChunkImportLaterEnum { Ready }\n")
    "ChunkImportLaterEnum::Missing" 0
  val _ = rejects_at \<^theory> "missing variant through an imported later enum"
    ["\"Missing\" is not a variant of enum \"ChunkImportLaterEnum\""]
    (broken ^ "  use ChunkImportLaterEnum as LaterEnumAlias;\n" ^
     "  use LaterEnumAlias::Missing as missing_variant;\n" ^
     "  enum ChunkImportLaterEnum { Ready }\n")
    "Missing" 0
  val _ = rejects_at \<^theory> "later enum variant"
    ["import target \"ChunkImportLaterChoice::Ready\" of \"later_ready\" is not yet available"]
    ("  fn ChunkImportLaterUse(x: u32) -> u32 { match x { later_ready => 1 } }\n" ^
     "  use ChunkImportLaterChoice::{self as LaterChoice, Ready as later_ready};\n" ^
     "  enum ChunkImportLaterChoice { Ready }\n")
    "later_ready" 0
end
\<close>

text\<open>
Entities that exist before the chunk keep resolving through an alias whose other namespace a later
member declares, and a later value-only target leaves the type namespace of its spelling to the
existing type mapping.
\<close>

urust_datatype \<open> enum ChunkImportBoth { Only } \<close>

urust_type "ChunkImportSpell" = \<open> 32 word \<close>

urust \<open>
  fn ChunkImportBothType(choice: ChunkImportBothAlias) -> u32 {
    match choice { ChunkImportBothAlias::Only => 1 }
  }

  fn ChunkImportSpellUser(width: ChunkImportSpell) -> ChunkImportSpell { width }

  use ChunkImportBoth as ChunkImportBothAlias;
  use ChunkImportSpellLater as ChunkImportSpell;

  fn ChunkImportBoth() -> u32 { 2 }

  fn ChunkImportSpellLater() -> u32 { 1 }

  fn ChunkImportBothValue() -> u32 { ChunkImportBothAlias() + ChunkImportSpell() }
\<close>

urust_fn \<open>
  fn ChunkImportBothTypeControl(choice: ChunkImportBoth) -> u32 {
    match choice { ChunkImportBoth::Only => 1 }
  }
\<close>

urust_fn \<open> fn ChunkImportSpellUserControl(width: demo::Width) -> demo::Width { width } \<close>

urust_fn \<open> fn ChunkImportBothValueControl() -> u32 { ChunkImportBoth() + ChunkImportSpellLater() } \<close>

lemma \<open> chunk_import_both_type = chunk_import_both_type_control \<close>
  unfolding chunk_import_both_type_def chunk_import_both_type_control_def by (rule refl)

lemma \<open> chunk_import_spell_user = chunk_import_spell_user_control \<close>
  unfolding chunk_import_spell_user_def chunk_import_spell_user_control_def by (rule refl)

lemma \<open> chunk_import_both_value = chunk_import_both_value_control \<close>
  unfolding chunk_import_both_value_def chunk_import_both_value_control_def by (rule refl)

text\<open>
The conversion calls of a native \<open>simple_word_enum\<close> enum that the chunk declares are importable
by the members after it, exactly as in a single-item sequence.
\<close>

urust \<open>
  #[repr(u8)]
  enum ChunkImportConv { Low = 1, High = 4 }

  \<omega>\<open>backend = "simple_word_enum", word_width = 16\<close>
  enum ChunkImportConvWide { Low = 1, High = 2 }

  use ChunkImportConv::{to_u8 as conv_to_byte, try_from as conv_from};
  use ChunkImportConvWide::to_u16 as wide_to_word;

  fn ChunkImportConvUse(level: ChunkImportConv) -> u8 { conv_to_byte(level) }

  fn ChunkImportConvWideUse(level: ChunkImportConvWide) -> u16 { wide_to_word(level) }
\<close>

urust_fn \<open>
  fn ChunkImportConvUseControl(level: ChunkImportConv) -> u8 { ChunkImportConv::to_u8(level) }
\<close>

urust_fn \<open>
  fn ChunkImportConvWideUseControl(level: ChunkImportConvWide) -> u16 {
    ChunkImportConvWide::to_u16(level)
  }
\<close>

lemma \<open> chunk_import_conv_use = chunk_import_conv_use_control \<close>
  unfolding chunk_import_conv_use_def chunk_import_conv_use_control_def by (rule refl)

lemma \<open> chunk_import_conv_wide_use = chunk_import_conv_wide_use_control \<close>
  unfolding chunk_import_conv_wide_use_def chunk_import_conv_wide_use_control_def by (rule refl)

text\<open>
A body import of a chunk alias whose type exists and whose value a later member declares is
available in the type namespace and unavailable in the value namespace.
\<close>

urust_datatype \<open> enum ChunkImportBodyType { Only } \<close>

urust_datatype \<open> enum ChunkImportBodyValue { Only } \<close>

urust \<open>
  fn ChunkImportBodyTypeUse(choice: ChunkImportBodyType) -> u32 {
    use BodyTypeAlias as BodyInner;
    match choice { BodyInner::Only => 1 }
  }

  use ChunkImportBodyType as BodyTypeAlias;

  fn ChunkImportBodyType() -> u32 { 2 }
\<close>

urust_fn \<open>
  fn ChunkImportBodyTypeUseControl(choice: ChunkImportBodyType) -> u32 {
    match choice { ChunkImportBodyType::Only => 1 }
  }
\<close>

lemma \<open> chunk_import_body_type_use = chunk_import_body_type_use_control \<close>
  unfolding chunk_import_body_type_use_def chunk_import_body_type_use_control_def by (rule refl)

text\<open>
A call through an alias of an existing literal whose function a later member declares names the
unavailable call; value uses keep the literal, and calls after the function resolve to it.
\<close>

definition chunk_import_lit_value :: \<open> 32 word \<close> where
  \<open> chunk_import_lit_value = 5 \<close>

micro_rust_notation (literal) chunk_import_lit_value ("ChunkImportLit")

urust_fn \<open> fn ChunkImportLitEarlyControl() -> u32 { ChunkImportLit } \<close>

urust \<open>
  fn ChunkImportLitEarly() -> u32 { lit_value }

  use ChunkImportLit as lit_value;

  fn ChunkImportLit() -> u32 { 6 }

  fn ChunkImportLitLate() -> u32 { lit_value() }
\<close>

urust_fn \<open> fn ChunkImportLitLateControl() -> u32 { ChunkImportLit() } \<close>

lemma \<open> chunk_import_lit_early = chunk_import_lit_early_control \<close>
  unfolding chunk_import_lit_early_def chunk_import_lit_early_control_def by (rule refl)

lemma \<open> chunk_import_lit_late = chunk_import_lit_late_control \<close>
  unfolding chunk_import_lit_late_def chunk_import_lit_late_control_def by (rule refl)

definition chunk_import_lit_two_value :: \<open> 32 word \<close> where
  \<open> chunk_import_lit_two_value = 7 \<close>

micro_rust_notation (literal) chunk_import_lit_two_value ("ChunkImportLitTwo")

ML_val\<open>
local
  open Chunk_Use_Audit
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  val _ = rejects_at \<^theory> "conversion call before its enum"
    ["import target \"ChunkImportConvLater::to_u8\" of \"later_to_byte\" is not yet available"]
    ("  fn ChunkImportConvEarly(x: u8) -> u8 { later_to_byte(x) }\n" ^
     "  use ChunkImportConvLater::to_u8 as later_to_byte;\n" ^
     "  #[repr(u8)]\n  enum ChunkImportConvLater { Low = 1 }\n")
    "later_to_byte" 0
  val _ = rejects_at \<^theory> "conversion call filtered out" ["unknown import target \"ChunkImportConvNone::to_u8\""]
    (broken ^ "  " ^ annotation "plugins = (plugins only: word_conversion)" ^ "\n" ^
     "  #[repr(u8)]\n  enum ChunkImportConvNone { Low = 1 }\n" ^
     "  use ChunkImportConvNone::to_u8 as none_to_byte;\n")
    "ChunkImportConvNone::to_u8" 0
  val _ = rejects_at \<^theory> "value use through a partially available body import"
    ["import target \"ChunkImportBodyValue\" of \"body_inner\" is not yet available"]
    ("  fn ChunkImportBodyValueUse() -> u32 { use BodyValueAlias as body_inner; body_inner() }\n" ^
     "  use ChunkImportBodyValue as BodyValueAlias;\n" ^
     "  fn ChunkImportBodyValue() -> u32 { 3 }\n")
    "body_inner" 1
  val _ = rejects_at \<^theory> "predicted duplicate before the first declaration"
    ["duplicate value import \"dup_predicted\""]
    (broken ^ "  use ChunkImportDupLater as dup_predicted;\n  use demo::value as dup_predicted;\n" ^
     "  fn ChunkImportDupLater() -> u32 { 1 }\n")
    "dup_predicted" 1
  val _ = rejects_at \<^theory> "call through a literal whose function is declared later"
    ["import target \"ChunkImportLitTwo\" of \"lit_two\" is not yet available as a call"]
    ("  fn ChunkImportLitTwoEarly() -> u32 { lit_two() }\n" ^
     "  use ChunkImportLitTwo as lit_two;\n" ^
     "  fn ChunkImportLitTwo() -> u32 { 8 }\n")
    "lit_two" 0
end
\<close>

subsection\<open> Imports and items of one chunk \<close>

text\<open>
An import and an item that the same chunk declares cannot share a name in one namespace, in
either order, as in a Rust module. Distinct namespaces may share a spelling, and an item declared
before the chunk may be shadowed inside it.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val value_clash =
    ["value import \"ChunkImportClash\" collides with the same-scope generated Rust function"]
in
  val _ = rejects_at \<^theory> "import before item" value_clash
    ("  use demo::value as ChunkImportClash;\n  fn ChunkImportClash() -> u32 { 1 }\n")
    "ChunkImportClash" 0
  val _ = rejects_at \<^theory> "import after item" value_clash
    ("  fn ChunkImportClash() -> u32 { 1 }\n  use demo::value as ChunkImportClash;\n")
    "ChunkImportClash" 1
  val _ = rejects_at \<^theory> "type import and struct"
    ["type import \"ChunkImportClashType\" collides with the same-scope generated Rust item"]
    ("  use UsePacket as ChunkImportClashType;\n  struct ChunkImportClashType { value: u32 }\n")
    "ChunkImportClashType" 0
  val _ = rejects_at \<^theory> "value import and unit struct"
    ["value import \"ChunkImportClashUnit\" collides with the same-scope generated Rust constructor"]
    ("  struct ChunkImportClashUnit;\n  use demo::value as ChunkImportClashUnit;\n")
    "ChunkImportClashUnit" 1
end
\<close>

urust \<open>
  use demo::value as ChunkImportNamed;

  struct ChunkImportNamed { sample: u32 }

  fn ChunkImportNamedUse(packet: ChunkImportNamed) -> u32 { ChunkImportNamed() + packet.sample }
\<close>

urust \<open>
  use demo::value as ChunkImportHelper;

  fn ChunkImportOuterShadow() -> u32 { ChunkImportHelper() }
\<close>

urust_fn \<open>
  fn ChunkImportNamedUseControl(packet: ChunkImportNamed) -> u32 { demo::value() + packet.sample }
\<close>

urust_fn \<open> fn ChunkImportOuterShadowControl() -> u32 { demo::value() } \<close>

lemma \<open> chunk_import_named_use = chunk_import_named_use_control \<close>
  unfolding chunk_import_named_use_def chunk_import_named_use_control_def by (rule refl)

lemma \<open> chunk_import_outer_shadow = chunk_import_outer_shadow_control \<close>
  unfolding chunk_import_outer_shadow_def chunk_import_outer_shadow_control_def by (rule refl)

subsection\<open> Whole-command atomicity \<close>

text\<open>
A failure anywhere in a chunk with imports, including the final target check, leaves no
declaration, registry entry, import binding, semantic report, warning or successful output, in
theory, locale and nested context targets. The same names are then available to a successful
chunk.
\<close>

ML\<open>
structure Chunk_Use_Atomicity =
struct
  open Chunk_Use_Audit
  val earlier =
    "  use demo::{increment as atomic_step, value as atomic_fetch};\n" ^
    "  use UseChoice::{self as AtomicChoiceAlias, Value as AtomicPresent};\n" ^
    "  struct ChunkImportAtomicRecord { value: u32, choice: AtomicChoiceAlias }\n" ^
    "  fn ChunkImportAtomicFirst(record: ChunkImportAtomicRecord) -> u32 {\n" ^
    "    match record.choice { AtomicPresent(n) => atomic_step(n), _ => atomic_fetch() }\n" ^
    "  }\n" ^
    "  use ChunkImportAtomicFirst as atomic_first;\n" ^
    "  fn ChunkImportAtomicSecond(record: ChunkImportAtomicRecord) -> u32 {\n" ^
    "    atomic_first(record) + record.value\n" ^
    "  }\n"
  val failures =
    [("typing", "  fn ChunkImportAtomicBroken() -> bool { atomic_step(1) }\n",
       ["no backend matches the use-site type"]),
     ("unavailable",
       "  fn ChunkImportAtomicEarly() -> u32 { atomic_later() }\n" ^
       "  use ChunkImportAtomicLater as atomic_later;\n" ^
       "  fn ChunkImportAtomicLater() -> u32 { 1 }\n",
       ["is not yet available"]),
     ("never-declared", "  use ChunkImportAtomicNever as atomic_never;\n",
       ["unknown import target \"ChunkImportAtomicNever\""]),
     ("collision",
       "  use demo::value as ChunkImportAtomicClash;\n" ^
       "  fn ChunkImportAtomicClash() -> u32 { 1 }\n",
       ["collides with the same-scope generated Rust function"]),
     ("body-import",
       "  fn ChunkImportAtomicBody() -> u32 { use ChunkImportAtomicMissing as missing; missing() }\n",
       ["unknown import target \"ChunkImportAtomicMissing\""]),
     ("datatype-field",
       "  struct ChunkImportAtomicField { field: AtomicLaterType }\n" ^
       "  use ChunkImportAtomicLaterStruct as AtomicLaterType;\n" ^
       "  struct ChunkImportAtomicLaterStruct { value: u32 }\n",
       ["is not yet available"])]

  fun failing_case target wrap (label, failing, expected) =
    let
      val label = "chunk-import-atomic-" ^ target ^ "-" ^ label
      val text = loud ^ wrap (chunk (earlier ^ failing))
      val {output, warnings, reports, ...} = rejected \<^theory> label expected text
      val chunk_output =
        filter_out (String.isPrefix "locale chunk_import_atomic_loc") (authored_output output)
      val _ =
        require ("failed " ^ label ^ " chunk printed successful output:\n" ^ cat_lines chunk_output)
          (null chunk_output)
      val command_start = #1 (range_of text "urust " 0)
      fun after_start events = filter (fn event => #1 (report_range event) >= command_start) events
      val _ =
        require ("failed " ^ label ^ " chunk replayed semantic reports")
          (null (after_start (semantic_entities reports)) andalso
            null (after_start (import_entities reports)))
      val _ =
        require ("failed " ^ label ^ " chunk emitted warnings:\n" ^ cat_lines warnings)
          (null warnings)
      val failing_start = #1 (range_of text failing 0)
      fun key_start key =
        (case space_explode "|" key of
           _ :: _ :: start :: _ => the_default 0 (Int.fromString start)
         | _ => 0)
      val leaked =
        non_lexical_reports label \<^theory> text command_start reports
        |> filter (fn key => key_start key < failing_start)
      val _ =
        require ("failed " ^ label ^ " chunk left non-lexical reports of earlier members:\n" ^
            cat_lines leaked)
          (null leaked)
    in () end

  fun in_locale body =
    "locale chunk_import_atomic_loc =\n  fixes atomic_param :: nat\nbegin\n" ^ body ^ "\nend\n"
  fun in_context body =
    "context\n  fixes atomic_fixed :: nat\nbegin\n" ^ body ^ "\nend\n"

  val functions = ["ChunkImportAtomicFirst", "ChunkImportAtomicSecond"]
  fun declared ctxt =
    {functions = filter (is_some o URust_Item_Scope.lookup_function ctxt) functions,
     types =
       filter (is_some o URust_Item_Scope.lookup_type ctxt)
         ["ChunkImportAtomicRecord", "ChunkImportAtomicLater", "ChunkImportAtomicLaterStruct"],
     constants = filter (const_declared ctxt) ["chunk_import_atomic_first"],
     registries = registry_snapshot ctxt,
     frames = URust_Import_Scope.frame_depth ctxt}
end
\<close>

ML\<open>
local
  open Chunk_Use_Atomicity
  val _ = List.app (failing_case "theory" I) failures
  val base = declared (Proof_Context.init_global \<^theory>)
  val _ = require "atomicity fixtures already exist"
    (null (#functions base) andalso null (#types base) andalso null (#constants base))
  (* Each failing chunk in one document sequence leaves the state unchanged; the corrected chunk
     then declares the same names. *)
  val sequence =
    loud ^
    implode (map (fn (_, failing, _) => chunk (earlier ^ failing) ^ "\n") failures) ^
    chunk earlier
  val transitions =
    Outer_Syntax.parse_text \<^theory> (K \<^theory>) (start_position "chunk-import-sequence") sequence
  fun step transition (state, failed) =
    (case Exn.result (Toplevel.command_exception true transition) state of
       Exn.Res state' => (state', failed)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else (state, failed @ [declared (Toplevel.context_of state)]))
  val (final_state, failed) =
    Parser_Test_Report_Lock.run (fn () =>
      Unsynchronized.setmp Private_Output.writeln_fn (K ()) (fn () =>
        Unsynchronized.setmp Private_Output.warning_fn (K ()) (fn () =>
          Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
            fold step transitions (Toplevel.make_state (SOME \<^theory>), [])) ()) ()) ())
  val after_declare = declared (Proof_Context.init_global \<^theory>)
  val _ = require "every failing chunk was rejected" (length failed = length failures)
  val _ = require "a failed chunk changed declarations, registries or import bindings"
    (forall (fn state => state = after_declare) failed)
  val final = declared (Toplevel.context_of final_state)
  val _ = require "the corrected chunk did not reuse the names of the failed chunks"
    (#functions final = functions andalso
      #types final = ["ChunkImportAtomicRecord"] andalso
      #constants final = ["chunk_import_atomic_first"] andalso
      #frames final = 0)
in
  val _ = writeln "failing chunks with imports leave no declarations, bindings, reports or output"
end
\<close>

ML\<open>
  List.app (Chunk_Use_Atomicity.failing_case "locale" Chunk_Use_Atomicity.in_locale)
    Chunk_Use_Atomicity.failures
\<close>

ML\<open>
  List.app (Chunk_Use_Atomicity.failing_case "context" Chunk_Use_Atomicity.in_context)
    Chunk_Use_Atomicity.failures
\<close>

subsection\<open> Navigation \<close>

text\<open>
Each alias of a chunk is reported once, at its use item, with its tooltip and target references.
Every occurrence in any member keeps its backend navigation and ends at that import declaration,
exactly as an occurrence of a block alias in a single-item declaration does.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val text =
    quiet ^
    chunk
      ("  fn ChunkImportNavEarly(x: u32) -> u32 { nav_step(x) }\n" ^
       "  use demo::increment as nav_step;\n" ^
       "  fn ChunkImportNavLate(x: u32) -> u32 { nav_step(nav_step(x)) }\n") ^
    "\nurust_fn " ^ cartouche " fn ChunkImportNavControl(x: u32) -> u32 { use demo::increment as nav_control; nav_control(x) } "
  val {reports, warnings, ...} = run_success \<^theory> "chunk-import-navigation" text
  val events = report_events reports
  fun at range = filter (fn event => report_range event = range) events
  fun import_at range =
    filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_import")
      (at range)
  val alias = range_of text "nav_step" 1
  val definitions =
    filter (fn (_, properties) => is_some (Properties.get properties Markup.defN)) (import_at alias)
  val _ = require "one import definition at the chunk alias" (length definitions = 1)
  val identity = the (Properties.get (#2 (hd definitions)) Markup.defN)
  val _ = require "one alias tooltip"
    (length (filter (fn (name, _) => name = Markup.typingN) (at alias)) = 1)
  val _ = require "one target reference at the use path"
    (length (filter (fn (name, _) => name = Markup.entityN)
      (at (range_of text "increment" 0))) = 1)
  fun ends_at_import occurrence =
    let
      val range = range_of text "nav_step" occurrence
      val kinds = entity_kinds_at range reports
      val references =
        map (fn (_, properties) => Properties.get properties Markup.refN) (import_at range)
    in
      require ("occurrence " ^ string_of_int occurrence ^ " ends at the import: " ^ commas kinds)
        (try List.last kinds = SOME "urust_import" andalso references = [SOME identity] andalso
          kinds = entity_kinds_at (range_of text "nav_control" 1) reports)
    end
  val _ = List.app ends_at_import [0, 2, 3]
  val _ = require "navigation emitted warnings" (null warnings)
in
  val _ = ()
end
\<close>

subsection\<open> Printing, roundtrips and read-only pretty replay \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val ctxt = \<^context>
  val text =
    "fn ChunkImportPrintEarly(x: u32) -> u32 { print_step(x) }\n" ^
    "use demo::{increment as print_step, value};\n" ^
    "struct ChunkImportPrintPacket { sample: u32 }\n" ^
    "use {UsePacket as PrintPacket};\n" ^
    "fn ChunkImportPrintLate(packet: PrintPacket) -> u32 { print_step(packet.sample) }\n"
  val parsed = the_chunk ctxt "chunk-import-print" text
  fun kind (URust_AST.Use_Item_Node _) = "use"
    | kind (URust_AST.Function_Item_Node _) = "fn"
    | kind _ = "datatype"
  val kinds = map (kind o URust_AST.annotated_item_item) (URust_AST.chunk_items parsed)
  val _ = require "use members keep their source order" (kinds = ["fn", "use", "datatype", "use", "fn"])
  val printed = URust_Printer.string_of_chunk URust_Printer.serialized_options parsed
  val reparsed = the_chunk ctxt "chunk-import-reprint" printed
  val _ = require "serialized chunk roundtrip with use members"
    (URust_Printer.tokens_of_chunk URust_Printer.serialized_options parsed =
      URust_Printer.tokens_of_chunk URust_Printer.serialized_options reparsed)
  fun index needle = raw_index printed needle 0
  val _ = require "printed members in source order"
    (index "ChunkImportPrintEarly" < index "use demo" andalso
      index "use demo" < index "ChunkImportPrintPacket" andalso
      index "ChunkImportPrintPacket" < index "PrintPacket}" andalso
      index "PrintPacket}" < index "ChunkImportPrintLate")

  (* Pretty replay of members that use chunk aliases resolves them as their declarations did
     and is read-only. *)
  val body =
    "  use demo::increment as pretty_step;\n" ^
    "  struct ChunkImportPrettyHolder { choice: PrettyChoice }\n" ^
    "  use UseChoice as PrettyChoice;\n" ^
    "  fn ChunkImportPretty(x: u32) -> u32 { pretty_step(x) }\n"
  val pretty = run_success \<^theory> "chunk-import-pretty" ("urust [pretty, verbosity = 2, pp_test] " ^
    command_source body)
  val plain_run = run_success \<^theory> "chunk-import-plain" ("urust [verbosity = 2] " ^ command_source body)
  val _ = require ("pretty output shows the aliases:\n" ^ cat_lines (authored_output (#output pretty)))
    (exists (String.isSubstring "pretty_step(x)") (authored_output (#output pretty)) andalso
      exists (String.isSubstring "choice: PrettyChoice") (authored_output (#output pretty)))
  val _ = require "pretty replay is read-only"
    (registry_snapshot (#ctxt pretty) = registry_snapshot (#ctxt plain_run) andalso
      URust_Import_Scope.frame_depth (#ctxt pretty) = 0 andalso
      URust_Import_Scope.frame_depth (#ctxt plain_run) = 0)
in
  val _ = ()
end
\<close>

subsection\<open> Complete input \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val ctxt = \<^context>
  fun parse_rejects label expected text =
    ignore (expect_failure label expected (fn () => parse ctxt label text))
in
  val _ = parse_rejects "missing semicolon" ["syntax error"] "use demo::value"
  val _ = parse_rejects "trailing input after a use member" ["syntax error"]
    "use demo::value; 1"
  val _ = parse_rejects "dangling use keyword" ["syntax error"] "fn A() -> u32 { 1 }\nuse"
  val _ = parse_rejects "path prefix before use" ["unexpected `value` before a use item"]
    "fn A() -> u32 { 1 }\nvalue use demo::value;"
  val _ = require "an import-only chunk parses"
    (length (URust_AST.chunk_items (the_chunk ctxt "import-only" "use demo::value;")) = 1)
end
\<close>

end
