theory Parser_Impl_Diagnostics
  imports Parser_Impl_Grammar
begin

section\<open> Source diagnostics \<close>

text\<open>
C2-I4/C1-I8 keep parser diagnostics at the terminal boundary. The generated parser data is
re-exported with only \<open>EC.showTerminal\<close> changed, then rejoined with the same lexer, LR table,
semantic actions, parser mode, and recovery data. Consequently an unrelated substring that happens
to contain an ML-Yacc terminal name is never inspected or rewritten.
\<close>

ML\<open>
signature URUST_DIAGNOSTICS =
sig
  val parse_source:
    Proof.context -> Input.source -> URust_AST.ur_expr option
end

(*
  URust_Diagnostics owns the source-facing diagnostic adapter for the generated uRust parser.  It
  preserves URust's lexer, grammar, semantic actions, recovery policy, and unresolved-AST result, but
  replaces ML-Yacc terminal names in syntax errors with source spellings.  This is the boundary used
  by parser clients; identifier and pattern resolution, lowering, HOL checking, and command-level
  rejection of an empty expression remain the responsibility of later modules.

  The intended stable parser-module interface is:

    * parse_source ctxt source initializes the generated lexer for the position-carrying Input.source
      and parses it with ctxt.  It returns NONE for empty input and SOME unresolved
      URust_AST.ur_expr for a recognized expression, preserving the AST positions and lexer markup
      produced by URust.  Lexical and syntax failures raise positioned ERROR exceptions; syntax
      errors name the encountered terminal by its uRust source spelling (or a descriptive placeholder
      for value-bearing terminals), never by the generated ML-Yacc terminal name. The operation owns
      the shared parser lock for its complete lexer initialization and parser consumption, so callers
      cannot accidentally use the mutable generated runtime concurrently.

  URUST_DIAGNOSTICS seals that one-operation interface. The generated URustLrVals and URustLex
  instantiations, Original and LrTable aliases,
  terminal_specs, terminal_count, terminal_id, terminal_spec, generated_terminal_name,
  source_terminal_name, assert_distinct, and value_bearing_terminal_ids implement and load-time-check
  the exhaustive terminal mapping; ParserData changes only EC.showTerminal; and Source_Parser is the
  resulting Join instantiation.  Refactors may replace or reorganize all of that machinery provided
  parse_source retains the behavior above and grammar/token drift still fails while this theory is
  loaded.  In particular, callers must not depend on terminal numeric identities, table layout,
  generated names, PARSER_DATA components, or Source_Parser operations.
*)
structure URust_Diagnostics :> URUST_DIAGNOSTICS =
struct
  structure URustLrVals =
    URustLrValsFun(structure Token = LrParser.Token)

  structure URustLex =
    URustLexFun(structure Tokens = URustLrVals.Tokens)

  structure Original = URustLrVals.ParserData
  structure LrTable = Original.LrTable

  (* This is intentionally exhaustive over generated terminal identity. The middle column is not
     used to render diagnostics: it makes grammar/token drift fail while this theory is loaded. *)
  val terminal_specs =
    [(0, "NUM", "<integer>"),
     (1, "NUMSFX", "<integer>"),
     (2, "STRING", "<string>"),
     (3, "IDENT", "<identifier>"),
     (4, "LPAR", "("),
     (5, "RPAR", ")"),
     (6, "VALAQ", "<value antiquotation>"),
     (7, "EXPRAQ", "<expression antiquotation>"),
     (8, "TURBO", "<turbofish>"),
     (9, "TTRUE", "true"),
     (10, "TFALSE", "false"),
     (11, "TLET", "let"),
     (12, "TCONST", "const"),
     (13, "TRETURN", "return"),
     (14, "TEQ", "="),
     (15, "TSEMI", ";"),
     (16, "EOF", "end of input"),
     (17, "TIF", "if"),
     (18, "TELSE", "else"),
     (19, "TLBRACE", "{"),
     (20, "TRBRACE", "}"),
     (21, "TLBRACK", "["),
     (22, "TRBRACK", "]"),
     (23, "COMMA", ","),
     (24, "TDOT", "."),
     (25, "TCOLON", ":"),
     (26, "TCOLONCOLON", "::"),
     (27, "TAT", "@"),
     (28, "TPLUS", "+"),
     (29, "TMINUS", "-"),
     (30, "TSTAR", "*"),
     (31, "TSLASH", "/"),
     (32, "TPERCENT", "%"),
     (33, "TSHL", "<<"),
     (34, "TSHR", ">>"),
     (35, "TAMP", "&"),
     (36, "TBAR", "|"),
     (37, "TCARET", "^"),
     (38, "TPLUSEQ", "+="),
     (39, "TMINUSEQ", "-="),
     (40, "TSTAREQ", "*="),
     (41, "TPERCENTEQ", "%="),
     (42, "TAMPEQ", "&="),
     (43, "TBAREQ", "|="),
     (44, "TCARETEQ", "^="),
     (45, "TSHLEQ", "<<="),
     (46, "TSHREQ", ">>="),
     (47, "TEQEQ", "=="),
     (48, "TNE", "!="),
     (49, "TLT", "<"),
     (50, "TLE", "<="),
     (51, "TGT", ">"),
     (52, "TGE", ">="),
     (53, "TAMPAMP", "&&"),
     (54, "TBARBAR", "||"),
     (55, "TBANG", "!"),
     (56, "TQUESTION", "?"),
     (57, "TUNSAFE", "unsafe"),
     (58, "TFUEL", "fuel"),
     (59, "TWHILE", "while"),
     (60, "TLOOP", "loop"),
     (61, "TFOR", "for"),
     (62, "TIN", "in"),
     (63, "THASH", "#"),
     (64, "TMATCH", "match"),
     (65, "TMATCHSWITCH", "match_switch"),
     (66, "TMATCHCASE", "match_case"),
     (67, "TARROW", "=>"),
     (68, "TDOTDOT", ".."),
     (69, "TDOTDOTEQ", "..="),
     (70, "TMUT", "mut"),
     (71, "TPATCONTEXT", "<pattern context>"),
     (72, "TMATCHESBANG", "matches!")]

  val terminal_count = length terminal_specs

  fun terminal_id (LrTable.T id) = id

  fun terminal_spec id =
    if 0 <= id andalso id < terminal_count
    then nth terminal_specs id
    else error ("uRust diagnostics: unknown parser terminal identity " ^ string_of_int id)

  fun generated_terminal_name term =
    Original.EC.showTerminal term

  fun source_terminal_name term =
    #3 (terminal_spec (terminal_id term))

  fun assert_distinct what values =
    let
      fun check _ [] = ()
        | check seen (value :: rest) =
            if member (op =) seen value
            then error ("uRust diagnostics: duplicate " ^ what ^ " " ^ quote value)
            else check (value :: seen) rest
    in check [] values end

  val _ =
    if map #1 terminal_specs = (0 upto (terminal_count - 1)) then ()
    else error "uRust diagnostics: missing or duplicate terminal identity"

  val _ = assert_distinct "generated terminal name" (map #2 terminal_specs)

  val _ =
    List.app
      (fn (id, expected, _) =>
        let val actual = generated_terminal_name (LrTable.T id) in
          if actual = expected then ()
          else
            error
              ("uRust diagnostics: terminal " ^ string_of_int id ^
                " is " ^ quote actual ^ ", expected " ^ quote expected)
        end)
      terminal_specs

  val _ =
    if generated_terminal_name (LrTable.T terminal_count) = "bogus-term" then ()
    else error "uRust diagnostics: terminal table has an unmapped generated entry"

  val _ =
    List.app
      (fn term =>
        let val id = terminal_id term in
          if 0 <= id andalso id < terminal_count then ()
          else
            error
              ("uRust diagnostics: recovery terminal has unknown identity " ^
                string_of_int id)
        end)
      Original.EC.terms

  val value_bearing_terminal_ids = [0, 1, 2, 3, 6, 7, 8, 72]

  val _ =
    List.app
      (fn id =>
        if #1 (terminal_spec id) = id then ()
        else error "uRust diagnostics: missing value-bearing terminal")
      value_bearing_terminal_ids

  structure ParserData : PARSER_DATA =
  struct
    type pos = Original.pos
    type svalue = Original.svalue
    type arg = Original.arg
    type result = Original.result
    structure LrTable = Original.LrTable
    structure Token = Original.Token
    structure Actions = Original.Actions
    structure EC =
    struct
      val is_keyword = Original.EC.is_keyword
      val noShift = Original.EC.noShift
      val preferred_change = Original.EC.preferred_change
      val errtermvalue = Original.EC.errtermvalue
      val showTerminal = source_terminal_name
      val terms = Original.EC.terms
    end
    val table = Original.table
  end

  structure Source_Parser =
    Join(
      structure LrParser = LrParser
      structure ParserData = ParserData
      structure Lex = URustLex)

  fun parse_layout ctxt layout =
    let val _ = URustLex.UserDeclarations.set_layout layout ctxt in
      Parser_Lex_Util.parse_source_with_layout
          Source_Parser.parse Source_Parser.makeLexer
          Source_Parser.Stream.get Source_Parser.sameToken
          URustLrVals.Tokens.EOF layout
    end

  fun parse_source ctxt source =
    Parser_Utils.with_parser_lock (fn () =>
      parse_layout ctxt
        (Parser_Lex_Util.make_source_layout source))
end
\<close>

ML\<open>
local
  val surrounding = "/tmp/TEQEQ/RPAR"
  val source_pos = Position.line_file 41 surrounding
  val source =
    Parser_Lex_Util.positioned_content_source
      "1 == 2 == 3" source_pos
  val actual =
    (case
        Exn.result
          (fn () =>
            URust_Diagnostics.parse_source \<^context> source) () of
       Exn.Res _ =>
         error "uRust diagnostics: positioned malformed source unexpectedly parsed"
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else Runtime.exn_message exn)
  val actual_text = XML.content_of (YXML.parse_body actual)
  val expected =
    "Parse Error at line 41, column 8: syntax error found at == " ^
      "(line 41 of \"/tmp/TEQEQ/RPAR\")"
  val _ =
    if actual_text = expected then ()
    else
      error
        ("uRust diagnostics: exact positioned-message regression\n" ^
          "expected: " ^ quote expected ^ "\n" ^
          "actual:   " ^ quote actual_text)
  val _ =
    if String.isSubstring surrounding actual_text then ()
    else
      error
        ("uRust diagnostics: surrounding diagnostic text changed: " ^
          quote surrounding)
in end
\<close>

end
