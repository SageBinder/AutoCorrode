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
      for value-bearing terminals), never by the generated ML-Yacc terminal name.  The generated
      lexer and parser runtime are mutable, so callers must hold Parser_Utils.with_parser_lock for
      the complete call.

  The structure is intentionally unsealed for its generated-parser wiring, but no other exposed name
  is a supported parser-module interface.  Original and LrTable are aliases into generated data;
  terminal_specs, terminal_count, terminal_id, terminal_spec, generated_terminal_name,
  source_terminal_name, assert_distinct, and value_bearing_terminal_ids implement and load-time-check
  the exhaustive terminal mapping; ParserData changes only EC.showTerminal; and Source_Parser is the
  resulting Join instantiation.  Refactors may replace or reorganize all of that machinery provided
  parse_source retains the behavior above and grammar/token drift still fails while this theory is
  loaded.  In particular, callers must not depend on terminal numeric identities, table layout,
  generated names, PARSER_DATA components, or Source_Parser operations.
*)
structure URust_Diagnostics =
struct
  structure Original = URust.URustLrVals.ParserData
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
     (8, "TTRUE", "true"),
     (9, "TFALSE", "false"),
     (10, "TLET", "let"),
     (11, "TCONST", "const"),
     (12, "TRETURN", "return"),
     (13, "TEQ", "="),
     (14, "TSEMI", ";"),
     (15, "EOF", "end of input"),
     (16, "TIF", "if"),
     (17, "TELSE", "else"),
     (18, "TLBRACE", "{"),
     (19, "TRBRACE", "}"),
     (20, "TLBRACK", "["),
     (21, "TRBRACK", "]"),
     (22, "COMMA", ","),
     (23, "TDOT", "."),
     (24, "TCOLON", ":"),
     (25, "TAT", "@"),
     (26, "TPLUS", "+"),
     (27, "TMINUS", "-"),
     (28, "TSTAR", "*"),
     (29, "TSLASH", "/"),
     (30, "TPERCENT", "%"),
     (31, "TSHL", "<<"),
     (32, "TSHR", ">>"),
     (33, "TAMP", "&"),
     (34, "TBAR", "|"),
     (35, "TCARET", "^"),
     (36, "TPLUSEQ", "+="),
     (37, "TMINUSEQ", "-="),
     (38, "TSTAREQ", "*="),
     (39, "TPERCENTEQ", "%="),
     (40, "TAMPEQ", "&="),
     (41, "TBAREQ", "|="),
     (42, "TCARETEQ", "^="),
     (43, "TSHLEQ", "<<="),
     (44, "TSHREQ", ">>="),
     (45, "TEQEQ", "=="),
     (46, "TNE", "!="),
     (47, "TLT", "<"),
     (48, "TLE", "<="),
     (49, "TGT", ">"),
     (50, "TGE", ">="),
     (51, "TAMPAMP", "&&"),
     (52, "TBARBAR", "||"),
     (53, "TBANG", "!"),
     (54, "TQUESTION", "?"),
     (55, "TUNSAFE", "unsafe"),
     (56, "TFUEL", "fuel"),
     (57, "TWHILE", "while"),
     (58, "TLOOP", "loop"),
     (59, "TFOR", "for"),
     (60, "TIN", "in"),
     (61, "THASH", "#"),
     (62, "TMATCH", "match"),
     (63, "TMATCHSWITCH", "match_switch"),
     (64, "TMATCHCASE", "match_case"),
     (65, "TARROW", "=>"),
     (66, "TDOTDOT", ".."),
     (67, "TDOTDOTEQ", "..="),
     (68, "TMUT", "mut"),
     (69, "TPATCONTEXT", "<pattern context>")]

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

  val value_bearing_terminal_ids = [0, 1, 2, 3, 6, 7]

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
      structure Lex = URust.URustLex)

  fun parse_source ctxt source =
    let val _ = URust.URustLex.UserDeclarations.set source ctxt in
      Parser_Lex_Util.parse_source
        Source_Parser.parse Source_Parser.makeLexer
        Source_Parser.Stream.get Source_Parser.sameToken
        URust.URustLrVals.Tokens.EOF source
    end
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
            Parser_Utils.with_parser_lock
              (fn () => URust_Diagnostics.parse_source \<^context> source)) () of
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
