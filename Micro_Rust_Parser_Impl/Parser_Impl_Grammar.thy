theory Parser_Impl_Grammar
  imports
    Parser_Impl_AST
    Parser_Utils
    "Isabelle_Lex-Yacc.LexYacc"
begin

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> token reports \<close>
SML_import \<open> structure Symbol = struct open Symbol end \<close>     \<comment>\<open> partial lexeme reports \<close>

ML\<open>
signature URUST_GRAMMAR =
sig
  val lex_error: string -> Position.T -> 'a
  val string_error: Position.T -> 'a
  val antiquotation_error: string -> Position.T -> 'a
  val formal_comment_open_error: Position.T -> 'a
  val formal_comment_close_error: Position.T -> 'a
  val log_data_error: Position.T -> 'a
  val turbofish_error: Position.T -> 'a
  val function_literal_suffix_error: Position.T -> 'a
  val struct_head_generics_error: Position.T -> 'a
end

(*
  URust_Grammar owns the source-facing failures raised directly by generated lexer actions. This
  structure does not decide which input is malformed, recover from an error, report parser conflicts,
  or validate the AST; those responsibilities remain with the lexer rules, the joined parser, and
  later elaboration modules.

  The generated lexer may rely on these public, non-returning functions:

    * lex_error text pos raises an ERROR for an unrecognized source fragment.  The message retains the
      `urust_expr` command prefix, quotes text, and appends Position.here pos so the rejection is
      clickable.  In particular, the catch-all lexer rule must call this function rather than skip
      input.
    * string_error pos raises the positioned malformed-or-unterminated-string diagnostic at the
      opening quote.
    * antiquotation_error kind pos raises the positioned unterminated-antiquotation diagnostic at the
      opening delimiter.  Lexer callers supply the source-facing kind, currently "value" or
      "expression".
    * formal_comment_open_error pos raises when `\<comment>` is not followed by an opening cartouche.
    * formal_comment_close_error pos raises when a formal-comment cartouche is not closed. Both
      formal-comment failures report at the `\<comment>` opener.
    * log_data_error pos raises the unterminated-log-data diagnostic at the adjacent `l` opener.
    * turbofish_error pos raises the unterminated-group diagnostic at the generic opener.
    * function_literal_suffix_error pos rejects an arity suffix separated from its value
      antiquotation and reports at that suffix.
    * struct_head_generics_error pos rejects generic arguments on any struct-expression head
      segment and reports at that argument group.

  All nine functions have result type 'a because they always raise via error.  Their exact string
  assembly and use of quote are implementation details, subject to the message and position contracts
  above.  The SML_import below only makes this Isabelle/ML-owned interface available to generated lexer
  code; it does not create a second owner.
*)
structure URust_Grammar :> URUST_GRAMMAR =
struct
  fun lex_error text pos =
    error ("urust_expr: unexpected input " ^ quote text ^ Position.here pos)

  fun string_error pos =
    error ("urust_expr: malformed or unterminated string literal" ^ Position.here pos)

  fun antiquotation_error kind pos =
    error ("urust_expr: unterminated " ^ kind ^ " antiquotation" ^ Position.here pos)

  fun formal_comment_open_error pos =
    error
      ("urust_expr: opening cartouche expected after formal comment" ^
        Position.here pos)

  fun formal_comment_close_error pos =
    error ("urust_expr: unterminated formal comment" ^ Position.here pos)

  fun log_data_error pos =
    error ("urust_expr: unterminated log data" ^ Position.here pos)

  fun turbofish_error pos =
    error ("urust_expr: unterminated turbofish" ^ Position.here pos)

  fun function_literal_suffix_error pos =
    error
      ("urust_expr: function-literal arity suffix must immediately follow the value antiquotation" ^
        Position.here pos)

  fun struct_head_generics_error pos =
    error
      ("urust_expr: generic arguments are not supported in struct-expression heads" ^
        Position.here pos)
end
\<close>
SML_import \<open> structure URust_Grammar = URust_Grammar \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>  \<comment>\<open> shared lexer position math \<close>

section\<open> Lexer + grammar \<close>

text\<open>
Lexer start states capture value and expression antiquotation bodies without lexing their
HOL content. Structural grammar tiers encode assignment, range, cast, prefix, and postfix boundaries;
ML-Yacc precedence declarations encode the ordinary binary-operator table for both the unrestricted
and no-struct expression families. Only token shims remain lexer-local; positions use
\<open>Parser_Lex_Util\<close>.
\<close>
(*
  This declaration generates the private URust lexer/parser functors used by Parser_Impl.
  Together they own recognition of one uRust expression source and construction of the unresolved
  URust_AST. Their boundary includes tokenization, PIDE token
  reports, precedence and sequencing policy, and grammar-action construction of AST nodes.  It ends
  before identifier or constructor resolution, site-specific pattern validation, lowering to shallow
  terms, and HOL type checking.

  Parser_Impl relies on the standard expert-mode Lex/Yacc functor interface:

    * URustLexFun produces the lexer structure accepted by the ML-Yacc Join functor. Its
      UserDeclarations.set_layout layout ctxt operation initializes the Isabelle-Lex-Yacc runtime from
      the shared source layout and resets all antiquotation/generic state. The
      source-taking set wrapper remains for generated-driver compatibility.
    * URustLrValsFun supplies the generated semantic value/result types, actions, LR table, tokens, and
      recovery data. Parser_Impl instantiates it once and rejoins that exact data with the
      generated lexer while replacing only terminal rendering.
    * The generated Tokens.EOF constructs the dummy end token required by
      Parser_Lex_Util.parse_source_with_layout. Its Position.T * Position.T argument delimits the
      token. Other generated token constructors are lexer implementation details; terminal additions
      or reordering must still be reflected in Parser_Impl's exhaustive terminal identity
      table.
    * The start result is URust_AST.ur_expr option.  NONE represents empty input; SOME ast preserves
      source order and the token/span positions recorded by URust_AST.  Syntax rejection raises a
      positioned ERROR rather than returning NONE.

  Expert mode deliberately generates no unsealed URust structure or default parse_source operation.
  Parser clients use the sealed URust_Parser.parse_source boundary. Lexer refs, start states,
  buffers, position-map helpers, grammar nonterminals, LR states/tables, semantic-value encodings, and
  generated functor names remain implementation details shared only with Parser_Impl.
  Refactors may change them provided the AST result, source positions/markup, state-initialization rule,
  and diagnostic rejoin points above are preserved.
*)
ml_lex_yacc [verbose, expert] "URust" where
lex_user_declarations\<open>
structure Tokens = Tokens
open URust_AST
type pos = Position.T
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

datatype aq_kind = No_AQ | Value_AQ | Expr_AQ
val aq_kind = ref No_AQ
val aq_buf = ref ([] : string list)
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)
val aq_open = ref 0
val aq_depth = ref 0
val generic_open = ref (NONE : Position.T option)
val log_data_open = ref (NONE : Position.T option)

datatype comment_context =
    Initial_Comment
  | Generic_Comment
  | Log_Data_Comment
val comment_context = ref (NONE : comment_context option)
val comment_open = ref 0
val comment_depth = ref ~1

fun reset_aq () =
  (aq_kind := No_AQ; aq_buf := []; aq_start := 0; aq_open := 0; aq_depth := 0)
fun reset_generic () = generic_open := NONE
fun reset_log_data () = log_data_open := NONE
fun reset_comment () =
  (comment_context := NONE; comment_open := 0; comment_depth := ~1)
fun reset_state () =
  (reset_aq (); reset_generic (); reset_log_data (); reset_comment ())
fun start_aq kind open_pos body_pos =
  (aq_kind := kind; aq_buf := []; aq_start := body_pos; aq_open := open_pos; aq_depth := 0)
fun push_aq fragment = aq_buf := fragment :: !aq_buf
fun take_aq () =
  let val body = String.concat (rev (!aq_buf))
  in reset_aq (); body end
fun start_comment context open_pos =
  (comment_context := SOME context; comment_open := open_pos; comment_depth := ~1)
fun take_comment_context () =
  (case !comment_context of
     SOME context => (reset_comment (); context)
   | NONE => raise Fail "uRust lexer: missing formal-comment return context")

(* A suffixed integer literal is deliberately NOT interpreted here: the lexer captures the raw lexeme and
   the elaboration term layer reads it against the single suffix table, so an unknown suffix is a
   POSITIONED elaborator error rather than an unpositioned `raise Fail` in lexer code (D29). The
   base-specific unsuffixed rules precede the general digit-plus-identifier rule so equal-length literals
   are NUM, while longer suffixed or malformed candidates remain one NUMSFX token.

   Per-lexer source-layout ref + set-shadow; the position MATH is shared (Parser_Lex_Util). tok_ident
   emits NO colour -- ident_term does that once it knows the name's role, so the markup cannot split
   (D14). *)
val source_layout =
  ref
    (Parser_Lex_Util.make_source_layout
      (Parser_Lex_Util.text_source ""))
fun set_layout layout ctxt =
  (Isabelle_lex_yacc.set (Parser_Lex_Util.source_of layout) ctxt;
   source_layout := layout;
   reset_state ())
fun set source ctxt =
  set_layout (Parser_Lex_Util.make_source_layout source) ctxt

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!source_layout) yypos
fun tokF args       = Parser_Lex_Util.tokF (!source_layout) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!source_layout) args
fun report_text args = Parser_Lex_Util.report_text (!source_layout) args
fun tok_ident (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!source_layout) (yypos, yytext)
  in Tokens.IDENT (yytext, p, p) end

fun tok_generic_open (yypos, yytext) =
  let
    val open_offset = yypos + size yytext - 1
    val start = fixed_pos yypos
    val stop = fixed_pos (open_offset + 1)
    val _ = report_text (yypos, "::", Markup.delimiter, "TCOLONCOLON")
    val _ = report_text (open_offset, "<", Markup.delimiter, "TGOPEN")
    val _ = generic_open := SOME (fixed_pos open_offset)
  in Tokens.TGOPEN (start, stop) end

fun tok_generic_value markup typ cons (yypos, yytext) =
  let
    val (value, start, stop) =
      Parser_Lex_Util.ranged_value
        (!source_layout) true markup typ (yypos, yytext)
  in cons (value, start, stop) end

fun tok_generic_ident (yypos, yytext) =
  let
    (* Semantic fallback reparses the retained source and supplies role-aware identifier markup.
       Exact-key identifiers are opaque notation components, not HOL entities. *)
    val (value, start, stop) =
      Parser_Lex_Util.ranged_value
        (!source_layout) false Markup.empty "GIDENT" (yypos, yytext)
  in Tokens.GIDENT (value, start, stop) end

fun tok_generic_raw markup typ cons (yypos, yytext) =
  let
    val range as (start, stop) =
      Parser_Lex_Util.text_range (!source_layout) (yypos, yytext)
    val _ =
      Parser_Lex_Util.report_range
        (range, markup, typ)
  in cons (yypos, start, stop) end

fun tok_matches_bang (yypos, yytext) =
  let
    val range as (start, stop) =
      Parser_Lex_Util.text_range (!source_layout) (yypos, yytext)
    val bang_raw = yypos + size yytext - 1
    val bang_pos = fixed_pos bang_raw
    val _ = report_text (yypos, "matches", Markup.keyword1, "TMATCHESBANG")
    val _ = report_text (bang_raw, "!", Markup.operator, "TMATCHESBANG")
  in Tokens.TMATCHESBANG (bang_pos, start, stop) end

fun tok_log_data_open (yypos, yytext) =
  let
    val range as (start, stop) =
      Parser_Lex_Util.text_range (!source_layout) (yypos, yytext)
    val delimiter_raw = yypos + 1
    val _ = report_text (yypos, "l", Markup.keyword1, "TLOGDATAOPEN")
    val _ =
      report_text
        (delimiter_raw, String.extract (yytext, 1, NONE),
         Markup.delimiter, "TLOGDATAOPEN")
    val _ = log_data_open := SOME start
  in Tokens.TLOGDATAOPEN range end

fun tok_log_identifier (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!source_layout) (yypos, yytext)
  in Tokens.LOGIDENT (yytext, p, p) end

fun eof () =
  (case !comment_context of
     SOME _ =>
       if !comment_depth < 0
       then URust_Grammar.formal_comment_open_error (fixed_pos (!comment_open))
       else URust_Grammar.formal_comment_close_error (fixed_pos (!comment_open))
   | NONE =>
       (case !aq_kind of
          No_AQ =>
            (case !log_data_open of
               SOME pos => URust_Grammar.log_data_error pos
             | NONE =>
                 (case !generic_open of
                    NONE => Tokens.EOF (Position.none, Position.none)
                  | SOME pos =>
                      URust_Grammar.turbofish_error pos))
        | Value_AQ => URust_Grammar.antiquotation_error "value" (fixed_pos (!aq_open))
        | Expr_AQ => URust_Grammar.antiquotation_error "expression" (fixed_pos (!aq_open))))
\<close>
lex_definitions\<open>
%header (functor URustLexFun(structure Tokens: URust_TOKENS));
%s VAQ EAQ GENERIC LOGDATA COMMENT_OPEN COMMENT;
digit=[0-9];
hexdigit=[0-9a-fA-F];
idstart=[A-Za-z_];
idchar=[A-Za-z0-9_];
ws = [\ \t\r];
pathws = [\ \t\r\n];
\<close>
lex_rules\<open>
<INITIAL>\n       => (lex());
<INITIAL>{ws}+    => (lex());
<INITIAL>"//"[^\n]* =>
    (report_text (yypos, yytext, Markup.comment1, "line comment"); lex());
<INITIAL>\\"<comment>" =>
    (start_comment Initial_Comment yypos; YYBEGIN COMMENT_OPEN; lex());
<INITIAL>"0b"[0-1_]+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>"0o"[0-7_]+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>"0x"[0-9a-fA-F_]+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>{digit}[0-9_]* =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>{digit}{idchar}* =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", Tokens.NUMSFX, yytext));
<INITIAL>"true"   => (tokF (yypos, yytext, Markup.keyword1, "TTRUE", Tokens.TTRUE));
<INITIAL>"false"  => (tokF (yypos, yytext, Markup.keyword1, "TFALSE", Tokens.TFALSE));
<INITIAL>"as"     => (tokF (yypos, yytext, Markup.keyword1, "TAS", Tokens.TAS));
<INITIAL>"u8"     => (tok_valF (yypos, yytext, Markup.keyword1, "TUINT", Tokens.TUINT, UT_U8));
<INITIAL>"u16"    => (tok_valF (yypos, yytext, Markup.keyword1, "TUINT", Tokens.TUINT, UT_U16));
<INITIAL>"u32"    => (tok_valF (yypos, yytext, Markup.keyword1, "TUINT", Tokens.TUINT, UT_U32));
<INITIAL>"u64"    => (tok_valF (yypos, yytext, Markup.keyword1, "TUINT", Tokens.TUINT, UT_U64));
<INITIAL>"usize"  => (tok_valF (yypos, yytext, Markup.keyword1, "TUINT", Tokens.TUINT, UT_Usize));
<INITIAL>"i32"    => (tok_valF (yypos, yytext, Markup.keyword1, "TSINT", Tokens.TSINT, ST_I32));
<INITIAL>"i64"    => (tok_valF (yypos, yytext, Markup.keyword1, "TSINT", Tokens.TSINT, ST_I64));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", Tokens.TCONST));
<INITIAL>"return" => (tokF (yypos, yytext, Markup.keyword1, "TRETURN", Tokens.TRETURN));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", Tokens.TELSE));
<INITIAL>"fuel"   => (tokF (yypos, yytext, Markup.keyword1, "TFUEL", Tokens.TFUEL));
<INITIAL>"while"  => (tokF (yypos, yytext, Markup.keyword1, "TWHILE", Tokens.TWHILE));
<INITIAL>"loop"   => (tokF (yypos, yytext, Markup.keyword1, "TLOOP", Tokens.TLOOP));
<INITIAL>"for"    => (tokF (yypos, yytext, Markup.keyword1, "TFOR", Tokens.TFOR));
<INITIAL>"in"     => (tokF (yypos, yytext, Markup.keyword1, "TIN", Tokens.TIN));
<INITIAL>"unsafe" => (tokF (yypos, yytext, Markup.keyword1, "TUNSAFE", Tokens.TUNSAFE));
<INITIAL>\\"<y>"\\"<i>"\\"<e>"\\"<l>"\\"<d>" =>
    (tokF (yypos, yytext, Markup.keyword1, "TYIELD", Tokens.TYIELD));
<INITIAL>\\"<l>"\\"<o>"\\"<g>" =>
    (tokF (yypos, yytext, Markup.keyword1, "TLOG", Tokens.TLOG));
<INITIAL>"matches""!" => (tok_matches_bang (yypos, yytext));
<INITIAL>"match"        => (tokF (yypos, yytext, Markup.keyword1, "TMATCH", Tokens.TMATCH));
<INITIAL>"match_switch" => (tokF (yypos, yytext, Markup.keyword1, "TMATCHSWITCH", Tokens.TMATCHSWITCH));
<INITIAL>"match_case"   => (tokF (yypos, yytext, Markup.keyword1, "TMATCHCASE", Tokens.TMATCHCASE));
<INITIAL>"mut"    => (tokF (yypos, yytext, Markup.keyword1, "TMUT", Tokens.TMUT));
<INITIAL>"::"{pathws}*"<" =>
    (YYBEGIN GENERIC; tok_generic_open (yypos, yytext));
<INITIAL>"::"     => (tokF (yypos, yytext, Markup.delimiter, "TCOLONCOLON", Tokens.TCOLONCOLON));
<INITIAL>"<<="    => (tokF (yypos, yytext, Markup.operator, "TSHLEQ", Tokens.TSHLEQ));
<INITIAL>">>="    => (tokF (yypos, yytext, Markup.operator, "TSHREQ", Tokens.TSHREQ));
<INITIAL>"+="     => (tokF (yypos, yytext, Markup.operator, "TPLUSEQ", Tokens.TPLUSEQ));
<INITIAL>"-="     => (tokF (yypos, yytext, Markup.operator, "TMINUSEQ", Tokens.TMINUSEQ));
<INITIAL>"*="     => (tokF (yypos, yytext, Markup.operator, "TSTAREQ", Tokens.TSTAREQ));
<INITIAL>"%="     => (tokF (yypos, yytext, Markup.operator, "TPERCENTEQ", Tokens.TPERCENTEQ));
<INITIAL>"&="     => (tokF (yypos, yytext, Markup.operator, "TAMPEQ", Tokens.TAMPEQ));
<INITIAL>"|="     => (tokF (yypos, yytext, Markup.operator, "TBAREQ", Tokens.TBAREQ));
<INITIAL>"^="     => (tokF (yypos, yytext, Markup.operator, "TCARETEQ", Tokens.TCARETEQ));
<INITIAL>"=>"     => (tokF (yypos, yytext, Markup.delimiter, "TARROW", Tokens.TARROW));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.delimiter, "TEQ", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", Tokens.TSEMI));
<INITIAL>"..="    => (tokF (yypos, yytext, Markup.operator, "TDOTDOTEQ", Tokens.TDOTDOTEQ));
<INITIAL>".."     => (tokF (yypos, yytext, Markup.operator, "TDOTDOT", Tokens.TDOTDOT));
<INITIAL>"<<"     => (tokF (yypos, yytext, Markup.operator, "TSHL", Tokens.TSHL));
<INITIAL>">>"     => (tokF (yypos, yytext, Markup.operator, "TSHR", Tokens.TSHR));
<INITIAL>"<="     => (tokF (yypos, yytext, Markup.operator, "TLE", Tokens.TLE));
<INITIAL>">="     => (tokF (yypos, yytext, Markup.operator, "TGE", Tokens.TGE));
<INITIAL>"=="     => (tokF (yypos, yytext, Markup.operator, "TEQEQ", Tokens.TEQEQ));
<INITIAL>"!="     => (tokF (yypos, yytext, Markup.operator, "TNE", Tokens.TNE));
<INITIAL>"&&"     => (tokF (yypos, yytext, Markup.operator, "TAMPAMP", Tokens.TAMPAMP));
<INITIAL>"||"     => (tokF (yypos, yytext, Markup.operator, "TBARBAR", Tokens.TBARBAR));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.operator, "TPLUS", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.operator, "TMINUS", Tokens.TMINUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.operator, "TSTAR", Tokens.TSTAR));
<INITIAL>"/"      => (tokF (yypos, yytext, Markup.operator, "TSLASH", Tokens.TSLASH));
<INITIAL>"%"      => (tokF (yypos, yytext, Markup.operator, "TPERCENT", Tokens.TPERCENT));
<INITIAL>"<"      => (tokF (yypos, yytext, Markup.operator, "TLT", Tokens.TLT));
<INITIAL>">"      => (tokF (yypos, yytext, Markup.operator, "TGT", Tokens.TGT));
<INITIAL>"&"      => (tokF (yypos, yytext, Markup.operator, "TAMP", Tokens.TAMP));
<INITIAL>"|"      => (tokF (yypos, yytext, Markup.operator, "TBAR", Tokens.TBAR));
<INITIAL>"^"      => (tokF (yypos, yytext, Markup.operator, "TCARET", Tokens.TCARET));
<INITIAL>"!"      => (tokF (yypos, yytext, Markup.operator, "TBANG", Tokens.TBANG));
<INITIAL>"?"      => (tokF (yypos, yytext, Markup.operator, "TQUESTION", Tokens.TQUESTION));
<INITIAL>"\""([^\"\\\n]|\\.)*"\"" =>
    (tok_valF (yypos, yytext, Markup.inner_string, "STRING", Tokens.STRING, yytext));
<INITIAL>"\""     => (URust_Grammar.string_error (fixed_pos yypos));
<INITIAL>"l"\\"<llangle>" =>
    (YYBEGIN LOGDATA; tok_log_data_open (yypos, yytext));
<INITIAL>{idstart}{idchar}* => (tok_ident (yypos, yytext));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "LPAR", Tokens.LPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "RPAR", Tokens.RPAR));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "COMMA", Tokens.COMMA));
<INITIAL>"."      => (tokF (yypos, yytext, Markup.delimiter, "TDOT", Tokens.TDOT));
<INITIAL>":"      => (tokF (yypos, yytext, Markup.delimiter, "TCOLON", Tokens.TCOLON));
<INITIAL>"@"      => (tokF (yypos, yytext, Markup.operator, "TAT", Tokens.TAT));
<INITIAL>"#"      => (tokF (yypos, yytext, Markup.delimiter, "THASH", Tokens.THASH));
<INITIAL>"["      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACK", Tokens.TLBRACK));
<INITIAL>"]"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACK", Tokens.TRBRACK));
<INITIAL>"{"      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACE", Tokens.TLBRACE));
<INITIAL>"}"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACE", Tokens.TRBRACE));
<INITIAL>\\"<llangle>"          => (report_text (yypos, yytext, Markup.delimiter, "VALAQ"); start_aq Value_AQ yypos (yypos + size yytext); YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (report_text (yypos, hd (Symbol.explode yytext), Markup.literal, "EXPRAQ"); start_aq Expr_AQ yypos (yypos + size yytext); YYBEGIN EAQ; lex());
<INITIAL>\\"<Rightarrow>" => (tokF (yypos, yytext, Markup.delimiter, "TARROW", Tokens.TARROW));
<INITIAL>\\"<^sub>""1"\\"<^sub>""0" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 10));
<INITIAL>\\"<^sub>""1"\\"<^sub>""1" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 11));
<INITIAL>\\"<^sub>""1"\\"<^sub>""2" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 12));
<INITIAL>\\"<^sub>""1"\\"<^sub>""3" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 13));
<INITIAL>\\"<^sub>""1"\\"<^sub>""4" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 14));
<INITIAL>\\"<^sub>""1" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 1));
<INITIAL>\\"<^sub>""2" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 2));
<INITIAL>\\"<^sub>""3" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 3));
<INITIAL>\\"<^sub>""4" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 4));
<INITIAL>\\"<^sub>""5" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 5));
<INITIAL>\\"<^sub>""6" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 6));
<INITIAL>\\"<^sub>""7" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 7));
<INITIAL>\\"<^sub>""8" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 8));
<INITIAL>\\"<^sub>""9" => (tok_valF (yypos, yytext, Markup.delimiter, "FUNARITY", Tokens.FUNARITY, 9));
<INITIAL>.        => (URust_Grammar.lex_error yytext (fixed_pos yypos));
<VAQ>\\"<llangle>" => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<VAQ>\\"<rrangle>" =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_text (yypos, yytext, Markup.delimiter, "VALAQ");
       let
         val p = fixed_pos (!aq_start)
         val q = fixed_pos yypos
         val open_pos = fixed_pos (!aq_open)
         val token_stop = Position.symbol_explode yytext q
         val body = take_aq ()
       in
         Tokens.VALAQ
           (Input.source true body (Position.range (p, q)),
            open_pos, token_stop)
       end));
<VAQ>\n           => (push_aq "\n"; lex());
<VAQ>.            => (push_aq yytext; lex());
<EAQ>\\"<open>"    => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<EAQ>\\"<close>"   =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_text (yypos, yytext, Markup.delimiter, "EXPRAQ");
       let
         val p = fixed_pos (!aq_start)
         val q = fixed_pos yypos
         val open_pos = fixed_pos (!aq_open)
         val body = take_aq ()
       in Tokens.EXPRAQ ((Input.source true body (Position.range (p, q)), open_pos), p, q) end));
<EAQ>\n           => (push_aq "\n"; lex());
<EAQ>.            => (push_aq yytext; lex());
<GENERIC>\n       => (lex());
<GENERIC>{ws}+    => (lex());
<GENERIC>\\"<comment>" =>
    (start_comment Generic_Comment yypos; YYBEGIN COMMENT_OPEN; lex());
<GENERIC>"0x"{hexdigit}+ =>
    (tok_generic_value Markup.numeral "GNUM" Tokens.GNUM (yypos, yytext));
<GENERIC>{digit}+ =>
    (tok_generic_value Markup.numeral "GNUM" Tokens.GNUM (yypos, yytext));
<GENERIC>{idstart}{idchar}* => (tok_generic_ident (yypos, yytext));
<GENERIC>"::"     => (tokF (yypos, yytext, Markup.delimiter, "TCOLONCOLON", Tokens.TCOLONCOLON));
<GENERIC>"("      => (tok_generic_raw Markup.delimiter "GLPAR" Tokens.GLPAR (yypos, yytext));
<GENERIC>")"      => (tok_generic_raw Markup.delimiter "GRPAR" Tokens.GRPAR (yypos, yytext));
<GENERIC>","      => (tokF (yypos, yytext, Markup.delimiter, "COMMA", Tokens.COMMA));
<GENERIC>"+"      => (tokF (yypos, yytext, Markup.operator, "TPLUS", Tokens.TPLUS));
<GENERIC>">"      =>
    (generic_open := NONE; YYBEGIN INITIAL;
     tokF (yypos, yytext, Markup.delimiter, "TGT", Tokens.TGT));
<GENERIC>.        => (URust_Grammar.lex_error yytext (fixed_pos yypos));
<LOGDATA>\n       => (lex());
<LOGDATA>{ws}+    => (lex());
<LOGDATA>\\"<comment>" =>
    (start_comment Log_Data_Comment yypos; YYBEGIN COMMENT_OPEN; lex());
<LOGDATA>"\""([^\"\\\n]|\\.)*"\"" =>
    (tok_valF
      (yypos, yytext, Markup.inner_string, "LOGSTRING",
       Tokens.LOGSTRING, yytext));
<LOGDATA>"\""     => (URust_Grammar.string_error (fixed_pos yypos));
<LOGDATA>{idstart}{idchar}* =>
    (tok_log_identifier (yypos, yytext));
<LOGDATA>","      =>
    (tokF (yypos, yytext, Markup.delimiter, "COMMA", Tokens.COMMA));
<LOGDATA>\\"<rrangle>" =>
    (log_data_open := NONE; YYBEGIN INITIAL;
     tokF
       (yypos, yytext, Markup.delimiter, "TLOGDATACLOSE",
        Tokens.TLOGDATACLOSE));
<LOGDATA>.        => (URust_Grammar.lex_error yytext (fixed_pos yypos));
<COMMENT_OPEN>\n       => (lex());
<COMMENT_OPEN>{ws}+    => (lex());
<COMMENT_OPEN>\\"<open>" =>
    (comment_depth := 0; YYBEGIN COMMENT; lex());
<COMMENT_OPEN>. =>
    (URust_Grammar.formal_comment_open_error (fixed_pos (!comment_open)));
<COMMENT>\\"<open>" =>
    (comment_depth := !comment_depth + 1; lex());
<COMMENT>\\"<close>" =>
    (if !comment_depth > 0 then
       (comment_depth := !comment_depth - 1; lex())
     else
       ((case take_comment_context () of
           Initial_Comment => YYBEGIN INITIAL
         | Generic_Comment => YYBEGIN GENERIC
         | Log_Data_Comment => YYBEGIN LOGDATA);
        lex()));
<COMMENT>\n       => (lex());
<COMMENT>.        => (lex());
\<close>
and yacc_user_declarations\<open>
open URust_AST

datatype parsed_fragment =
  Parsed_Fragment of
    string *
    Parser_Lex_Util.source_layout * int * int

fun append_fragment separator
    (Parsed_Fragment (left, layout, start, _))
    (Parsed_Fragment (right, _, _, stop)) =
  Parsed_Fragment (left ^ separator ^ right, layout, start, stop)

fun generic_argument
    (Parsed_Fragment (canonical, layout, start, stop)) =
  Generic_Arg
    (canonical, Parser_Lex_Util.source_slice layout start stop)

datatype binding_head =
    BH_Let of ur_pat * ur_expr
  | BH_LetMut of ur_pat * ur_expr * Position.T
  | BH_Const of ur_pat * ur_expr
  | BH_LetElse of ur_pat * ur_expr * ur_expr * Position.T

fun finish_binding (BH_Let (pattern, value), body, _) =
      UE_Let (pattern, value, body)
  | finish_binding (BH_LetMut (pattern, value, pos), body, _) =
      UE_LetMut (pattern, value, body, pos)
  | finish_binding (BH_Const (pattern, value), body, _) =
      UE_Const (pattern, value, body)
  | finish_binding
      (BH_LetElse (pattern, value, fallback, pos), body, body_right) =
      mk_let_else
        (pattern, value, fallback, body, pos, body_right)

datatype if_head =
    IH_If of ur_expr * Position.T
  | IH_IfLet of
      ur_pat * ur_expr * Position.T

fun finish_conditional
      (IH_If (condition, pos), success, fallback, _) =
      UE_If (condition, success, fallback, pos)
  | finish_conditional
      (IH_IfLet (pattern, value, pos), success, fallback, stop) =
      UE_IfLet
        (pattern, value, success, fallback,
         Position.range_position (pos, stop))

datatype arm_head =
  AH_Arm of ur_pat * (ur_expr * Position.T) option

fun finish_arm (AH_Arm (pattern, guard), body) =
  UR_Arm (pattern, guard, body)

fun segment_position (Path_Segment (_, pos, NONE)) = pos
  | segment_position (Path_Segment (_, _, SOME (Generic_Args (_, pos)))) = pos

fun make_path segment =
  UR_Path ([segment], segment_position segment)

fun append_path (UR_Path (segments, pos), segment) =
  UR_Path
    (segments @ [segment],
     Position.range_position
       (pos, Parser_Lex_Util.exclusive_end (segment_position segment)))

fun reject_struct_head_generics path =
  let
    fun reject segment =
      (case segment_generic_args segment of
         NONE => ()
       | SOME (Generic_Args (_, pos)) =>
           URust_Grammar.struct_head_generics_error pos)
  in List.app reject (path_segments path) end

fun make_struct_expression (path, fields, right) =
  let
    val _ = reject_struct_head_generics path
  in
    UE_Struct
      (path, fields,
       Position.range_position (path_position path, right))
  end

fun same_offset left right =
  (case (Position.offset_of left, Position.offset_of right) of
     (SOME left_offset, SOME right_offset) =>
       left_offset = right_offset
   | _ => left = right)

fun make_function_literal
    (source, arity, value_right, suffix_left, suffix_right, arguments) =
  if same_offset value_right suffix_left then
    UC_FunLiteral
      (source, arity,
       Position.range_position (suffix_left, suffix_right),
       arguments)
  else
    URust_Grammar.function_literal_suffix_error suffix_left
\<close>
yacc_definitions\<open>
%name URust
%pos Position.T
%eop EOF
%noshift EOF

(* Binary operators use ML-Yacc's native precedence mechanism instead of one grammar nonterminal per
   tier. Assignment, ranges, casts, prefixes, and postfixes remain structural because their accepted
   operand languages differ, not merely their precedence or associativity. TRETURN and the
   with-block delimiters resolve the two low-precedence expression/statement boundaries. *)
%right TRETURN
%right TIF TELSE TLBRACE TLBRACK TUNSAFE TWHILE TLOOP TFOR
%left TBARBAR
%left TAMPAMP
%nonassoc TEQEQ TNE TLT TLE TGT TGE
%nonassoc TPATCONTEXT
%left TBAR
%left TCARET
%left TAMP
%left TSHL TSHR
%left TPLUS TMINUS
%left TSTAR TSLASH TPERCENT

%term NUM of string | NUMSFX of string | STRING of string | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source * Position.T
    | TGOPEN
    | GNUM of string * Parser_Lex_Util.source_layout * int * int
    | GIDENT of string * Parser_Lex_Util.source_layout * int * int
    | GLPAR of int | GRPAR of int
    | TTRUE | TFALSE | TLET | TCONST | TRETURN | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE | TLBRACK | TRBRACK | COMMA | TDOT
    | TCOLON | TCOLONCOLON | TAT
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TPLUSEQ | TMINUSEQ | TSTAREQ | TPERCENTEQ
    | TAMPEQ | TBAREQ | TCARETEQ | TSHLEQ | TSHREQ
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG | TQUESTION
    | TUNSAFE | TFUEL | TWHILE | TLOOP | TFOR | TIN | THASH
    | TMATCH | TMATCHSWITCH | TMATCHCASE | TARROW
    | TDOTDOT | TDOTDOTEQ | TMUT | TPATCONTEXT
    | TMATCHESBANG of Position.T
    | TAS | TUINT of URust_AST.unsigned_type | TSINT of URust_AST.signed_type
    | FUNARITY of int
    | TYIELD | TLOG | TLOGDATAOPEN | LOGSTRING of string | LOGIDENT of string
    | TLOGDATACLOSE
%nonterm ustart of URust_AST.ur_expr option
       | ubody of URust_AST.ur_expr
       | ubinding_head of binding_head
       | uexpr of URust_AST.ur_expr
       | uclosure of URust_AST.ur_expr
       | uclosure_formals of URust_AST.ur_pat list
       | uassign of URust_AST.ur_expr
       | uassignop of URust_AST.assignop * Position.T
       | urange of URust_AST.ur_expr
       | ubinary of URust_AST.ur_expr
       | ucast of URust_AST.ur_expr
       | uprefix of URust_AST.ur_expr
       | ucast_target of URust_AST.cast_target
       | upostfix of URust_AST.ur_expr
       | uprimary of URust_AST.ur_expr
       | uprimary_nonhead of URust_AST.ur_expr
       | uexpr_no_struct of URust_AST.ur_expr
       | uclosure_no_struct of URust_AST.ur_expr
       | uassign_no_struct of URust_AST.ur_expr
       | urange_no_struct of URust_AST.ur_expr
       | ubinary_no_struct of URust_AST.ur_expr
       | ucast_no_struct of URust_AST.ur_expr
       | uprefix_no_struct of URust_AST.ur_expr
       | upostfix_no_struct of URust_AST.ur_expr
       | uprimary_no_struct of URust_AST.ur_expr
       | upath_segment of URust_AST.path_segment
       | upath of URust_AST.ur_path
       | ugeneric_args of URust_AST.generic_args
       | ugeneric_arglist of URust_AST.generic_arg list
       | ugeneric_arg of URust_AST.generic_arg
       | ugeneric_additive of parsed_fragment
       | ugeneric_atom of parsed_fragment
       | ugeneric_path of parsed_fragment
       | arglist of URust_AST.ur_expr list
       | ucallargs of URust_AST.ur_expr list
       | umacroargs of URust_AST.ur_expr list
       | umacrocallargs of URust_AST.ur_expr list
       | ublock of URust_AST.ur_expr
       | uunsafe of URust_AST.ur_expr
       | uwith_block_expr of URust_AST.ur_expr
       | usemi_free_stmt of URust_AST.ur_expr
       | uconditional of URust_AST.ur_expr
       | uif_head of if_head
       | ufuel of Input.source * Position.T
       | uloop_expr of URust_AST.ur_expr
       | umatch_kind of URust_AST.match_flavour * Position.T
       | umatch of URust_AST.ur_expr
       | uguard of URust_AST.ur_expr
       | uarm_head of arm_head
       | uarm of URust_AST.ur_arm
       | uarm_with_block of URust_AST.ur_arm
       | uarms of URust_AST.ur_arm list
       | upat of URust_AST.ur_pat
       | upat_range of URust_AST.ur_pat
       | upat_alias of URust_AST.ur_pat
       | upat_prefix of URust_AST.ur_pat
       | upat_atom of URust_AST.ur_pat
       | upat_ident of string * Position.T
       | upats of URust_AST.ur_pat list
       | uslice_item of URust_AST.slice_item
       | uslice_items of URust_AST.slice_item list
       | ustruct_field of URust_AST.struct_field
       | ustruct_fields of URust_AST.struct_field list
       | ustruct_expr of URust_AST.ur_expr
       | ustruct_expr_field of URust_AST.struct_expr_field
       | ustruct_expr_fields of URust_AST.struct_expr_field list
       | ulog_data_entry of URust_AST.log_data_entry
       | ulog_data_entries of URust_AST.log_data_entry list
\<close>
yacc_rules\<open>
  ustart : ubody (SOME ubody)
         | (NONE)
  (* With-block classification controls only separator elision. Every with-block form also enters the
     primary-expression tier below, so operators can consume it without a second precedence ladder. *)
  ubody : uexpr                             (uexpr)
        | uexpr TSEMI ubody                 (UE_Seq (uexpr, ubody))
        | uexpr TSEMI                       (finish_statement (uexpr, TSEMIleft))
        | usemi_free_stmt                   (usemi_free_stmt)
        | ubinding_head TSEMI ubody
            (finish_binding (ubinding_head, ubody, ubodyright))
  ubinding_head : TLET upat TEQ uexpr
                    (BH_Let (upat, uexpr))
                | TLET TMUT upat TEQ uexpr
                    (BH_LetMut (upat, uexpr, TMUTleft))
                | TCONST upat TEQ uexpr
                    (BH_Const (upat, uexpr))
                | TLET upat TEQ uexpr TELSE ublock
                    (BH_LetElse (upat, uexpr, ublock, TLETleft))
  (* Return and closures are low-precedence expressions outside the operator ladder. Their operands
     and bodies are complete expressions, while assignment enters this layer only on its right. *)
  uexpr : uassign                           (uassign)
        | TRETURN                           (UE_Return (NONE, TRETURNleft))
        | TRETURN uexpr
            (UE_Return (SOME uexpr, TRETURNleft))
        | uclosure                          (uclosure)
  uclosure : TBARBAR uexpr
                (mk_closure
                  ([], uexpr,
                   TBARBARleft, uexprright))
           | TBAR uclosure_formals TBAR uexpr
                (mk_closure
                  (uclosure_formals, uexpr,
                   TBAR1left, uexprright))
  (* Closure formals share the pattern representation, but this grammar accepts identifier spellings
     only. mk_bare_ident_pat normalizes `_` to P_Wild so the closure-formal elaboration gate can issue
     the positioned semantic rejection. Repeated identifiers and arbitrarily long lists are retained. *)
  uclosure_formals : IDENT
                       ([mk_bare_path_pat
                           (make_single_path (IDENT, IDENTleft))])
                   | IDENT COMMA uclosure_formals
                       (mk_bare_path_pat
                          (make_single_path (IDENT, IDENTleft)) ::
                          uclosure_formals)
  (* Assignment is structurally right-associative and ranges are structurally non-associative.
     Binary precedence and associativity come from the declarations above. *)
  uassign : urange (urange)
          | urange uassignop uexpr (mk_assign uassignop urange uexpr)
  uassignop : TEQ        ((Assign, TEQleft))
            | TPLUSEQ    ((AssignAdd, TPLUSEQleft))
            | TMINUSEQ   ((AssignBin AssignSub, TMINUSEQleft))
            | TSTAREQ    ((AssignBin AssignMul, TSTAREQleft))
            | TPERCENTEQ ((AssignBin AssignMod, TPERCENTEQleft))
            | TAMPEQ     ((AssignBin AssignBAnd, TAMPEQleft))
            | TBAREQ     ((AssignBin AssignBOr, TBAREQleft))
            | TCARETEQ   ((AssignBin AssignBXor, TCARETEQleft))
            | TSHLEQ     ((AssignBin AssignShl, TSHLEQleft))
            | TSHREQ     ((AssignBin AssignShr, TSHREQleft))
  urange : ubinary (ubinary)
         | ubinary TDOTDOT ubinary
             (UE_Range (RK_Exclusive, ubinary1, ubinary2, TDOTDOTleft))
         | ubinary TDOTDOTEQ ubinary
             (UE_Range (RK_Inclusive, ubinary1, ubinary2, TDOTDOTEQleft))
  ubinary : ucast (ucast)
          | ubinary TBARBAR ubinary
              (UE_Bin (Or, ubinary1, ubinary2, TBARBARleft))
          | ubinary TAMPAMP ubinary
              (UE_Bin (And, ubinary1, ubinary2, TAMPAMPleft))
          | ubinary TEQEQ ubinary
              (UE_Bin (Eq, ubinary1, ubinary2, TEQEQleft))
          | ubinary TNE ubinary
              (UE_Bin (Ne, ubinary1, ubinary2, TNEleft))
          | ubinary TLT ubinary
              (UE_Bin (Lt, ubinary1, ubinary2, TLTleft))
          | ubinary TLE ubinary
              (UE_Bin (Le, ubinary1, ubinary2, TLEleft))
          | ubinary TGT ubinary
              (UE_Bin (Gt, ubinary1, ubinary2, TGTleft))
          | ubinary TGE ubinary
              (UE_Bin (Ge, ubinary1, ubinary2, TGEleft))
          | ubinary TBAR ubinary
              (UE_Bin (BOr, ubinary1, ubinary2, TBARleft))
          | ubinary TCARET ubinary
              (UE_Bin (BXor, ubinary1, ubinary2, TCARETleft))
          | ubinary TAMP ubinary
              (UE_Bin (BAnd, ubinary1, ubinary2, TAMPleft))
          | ubinary TSHL ubinary
              (UE_Bin (Shl, ubinary1, ubinary2, TSHLleft))
          | ubinary TSHR ubinary
              (UE_Bin (Shr, ubinary1, ubinary2, TSHRleft))
          | ubinary TPLUS ubinary
              (UE_Bin (Add, ubinary1, ubinary2, TPLUSleft))
          | ubinary TMINUS ubinary
              (UE_Bin (Sub, ubinary1, ubinary2, TMINUSleft))
          | ubinary TSTAR ubinary
              (UE_Bin (Mul, ubinary1, ubinary2, TSTARleft))
          | ubinary TSLASH ubinary
              (UE_Bin (Div, ubinary1, ubinary2, TSLASHleft))
          | ubinary TPERCENT ubinary
              (UE_Bin (Mod, ubinary1, ubinary2, TPERCENTleft))
  (* Casts consume a complete prefix expression. Thus dereference binds before `as`, while postfix
     operations remain tighter than every prefix and no general postfix invocation is introduced. *)
  ucast : uprefix (uprefix)
        | ucast TAS ucast_target
            (UE_Cast (ucast, ucast_target, TASleft))
  uprefix : upostfix (upostfix)
          | TBANG uprefix
              (UE_Unary (U_Not, uprefix, TBANGleft))
          | TAMP uprefix
              (UE_Unary (U_Borrow BM_Imm, uprefix, TAMPleft))
          | TAMP TMUT uprefix
              (UE_Unary (U_Borrow BM_Mut, uprefix, TAMPleft))
          | TSTAR uprefix
              (UE_Unary (U_Deref, uprefix, TSTARleft))
  (* Postfixes form a structural tier above primaries, so `?`, field access, tuple projections, and
     methods compose left-to-right and bind tighter than prefix/binary operators. Indexing shares this
     tier. A dotted identifier followed by parentheses is a method; without parentheses it is an
     NField lens access. A dotted numeric token is validated as a canonical projection index 0..15. *)
  upostfix : uprimary (uprimary)
           | upostfix TQUESTION
               (UE_Unary (U_Propagate, upostfix, TQUESTIONleft))
           | upostfix TDOT IDENT
               (UE_Field (upostfix, IDENT, IDENTleft))
           | upostfix TDOT NUM
               (mk_tuple_projection (upostfix, NUM, NUMleft))
           | upostfix TDOT NUMSFX
               (mk_tuple_projection (upostfix, NUMSFX, NUMSFXleft))
           | upostfix TDOT upath_segment LPAR ucallargs RPAR
               (mk_call
                  (UC_Method (upostfix, upath_segment),
                   ucallargs, upostfixleft, RPARright))
           | upostfix TLBRACK uexpr TRBRACK
               (UE_Index
                 (upostfix, uexpr,
                  Position.range_position (upostfixleft, TRBRACKright)))
  uprimary : upath           (UE_Path upath)
           | ustruct_expr    (ustruct_expr)
           | uprimary_nonhead (uprimary_nonhead)
  uprimary_nonhead : NUM     (UE_Literal (LP_Integer (NUM, NUMleft)))
        | NUMSFX     (UE_Literal (LP_Integer (NUMSFX, NUMSFXleft)))
        | TTRUE      (UE_Literal (LP_Bool (true, TTRUEleft)))
        | TFALSE     (UE_Literal (LP_Bool (false, TFALSEleft)))
        | STRING     (UE_Literal (LP_String (STRING, STRINGleft)))
        | TYIELD
            (UE_Yield
              (Position.range_position (TYIELDleft, TYIELDright)))
        | TLOG VALAQ VALAQ
            (UE_Log
              (VALAQ1, VALAQ2,
               Position.range_position (TLOGleft, VALAQ2right)))
        | TLOGDATAOPEN ulog_data_entries TLOGDATACLOSE
            (UE_LogData
              (ulog_data_entries,
               Position.range_position
                 (TLOGDATAOPENleft, TLOGDATACLOSEright)))
        | upath LPAR ucallargs RPAR
            (mk_call (UC_Path upath, ucallargs, upathleft, RPARright))
        | EXPRAQ LPAR ucallargs RPAR
            (mk_call
              (UC_Antiq (#1 EXPRAQ), ucallargs, #2 EXPRAQ, RPARright))
        | VALAQ FUNARITY LPAR ucallargs RPAR
            (mk_call
              (make_function_literal
                (VALAQ, FUNARITY, VALAQright,
                 FUNARITYleft, FUNARITYright, NONE),
               ucallargs, VALAQleft, RPARright))
        | VALAQ FUNARITY ugeneric_args LPAR ucallargs RPAR
            (mk_call
              (make_function_literal
                (VALAQ, FUNARITY, VALAQright,
                 FUNARITYleft, FUNARITYright,
                 SOME ugeneric_args),
               ucallargs, VALAQleft, RPARright))
        | upath TBANG LPAR umacrocallargs RPAR
            (UE_Macro
              (upath, TBANGleft,
               MP_Arguments umacrocallargs,
               Position.range_position (upathleft, RPARright)))
        | upath TBANG TLBRACK umacrocallargs TRBRACK
            (UE_Macro
              (upath, TBANGleft,
               MP_Arguments umacrocallargs,
               Position.range_position (upathleft, TRBRACKright)))
        | TMATCHESBANG LPAR uexpr COMMA upat RPAR
            (UE_Macro
              (make_single_path
                 ("matches",
                  Position.range_position (TMATCHESBANGleft, TMATCHESBANG)),
               TMATCHESBANG,
               MP_Matches (uexpr, upat),
               Position.range_position (TMATCHESBANGleft, RPARright)))
        | LPAR RPAR  (UE_Unit LPARleft)
        | LPAR uexpr COMMA arglist RPAR
            (UE_Tuple
              (uexpr :: arglist,
               Position.range_position (LPARleft, RPARright)))
        | LPAR ubody RPAR
            (UE_Group
              (ubody,
               Position.range_position (LPARleft, RPARright)))
        | TLBRACK TRBRACK
            (UE_Array ([], Position.range_position (TLBRACKleft, TRBRACKright)))
        | TLBRACK arglist TRBRACK
            (UE_Array (arglist, Position.range_position (TLBRACKleft, TRBRACKright)))
        | VALAQ      (UE_Literal (LP_ValAntiq VALAQ))
        | EXPRAQ     (UE_ExprAntiq (#1 EXPRAQ))
        | uwith_block_expr %prec TIF (uwith_block_expr)
  upath_segment : IDENT
                    (Path_Segment (IDENT, IDENTleft, NONE))
                | IDENT ugeneric_args
                    (Path_Segment (IDENT, IDENTleft, SOME ugeneric_args))
  upath : upath_segment
            (make_path upath_segment)
        | upath TCOLONCOLON upath_segment
            (append_path (upath, upath_segment))
  ugeneric_args : TGOPEN ugeneric_arglist TGT
                    (Generic_Args
                      (ugeneric_arglist,
                       Position.range_position (TGOPENleft, TGTright)))
  ugeneric_arglist : ugeneric_arg
                       ([ugeneric_arg])
                   | ugeneric_arg COMMA ugeneric_arglist
                       (ugeneric_arg :: ugeneric_arglist)
  ugeneric_arg : ugeneric_additive
                   (generic_argument ugeneric_additive)
  ugeneric_additive : ugeneric_atom
                        (ugeneric_atom)
                    | ugeneric_additive TPLUS ugeneric_atom
                        (append_fragment "+"
                          ugeneric_additive ugeneric_atom)
  ugeneric_atom : GNUM
                (case GNUM of
                       (lexeme, layout, start, stop) =>
                         Parsed_Fragment
                           (lexeme, layout, start, stop))
                | ugeneric_path
                    (ugeneric_path)
                | GLPAR ugeneric_additive GRPAR
                    (case ugeneric_additive of
                       Parsed_Fragment
                         (canonical, layout, _, _) =>
                           Parsed_Fragment
                             ("(" ^ canonical ^ ")",
                              layout, GLPAR, GRPAR + 1))
  ugeneric_path : GIDENT
                    (case GIDENT of
                       (name, layout, start, stop) =>
                         Parsed_Fragment
                           (name, layout, start, stop))
                | ugeneric_path TCOLONCOLON GIDENT
                    (case (ugeneric_path, GIDENT) of
                       (Parsed_Fragment
                          (canonical, layout, start, _),
                        (name, _, _, stop)) =>
                          Parsed_Fragment
                            (canonical ^ "::" ^ name,
                             layout, start, stop))
  ucast_target : TUINT
                   (CT_Unsigned TUINT)
               | TSINT
                   (CT_Signed TSINT)
               | TSTAR TCONST TUINT
                   (CT_RawPointer (RPM_Const, TUINT))
               | TSTAR TMUT TUINT
                   (CT_RawPointer (RPM_Mut, TUINT))
  (* The no-struct family mirrors the structural expression boundaries and binary operator rule.
     Only its primary excludes direct struct expressions; explicit delimiters in the shared non-head
     primary restore unrestricted parsing. A bare operandless return is intentionally absent here:
     the following mandatory control-body block is always parsed as its operand, so the old alternative
     was unreachable. Ordinary expression and guard contexts still support operandless return. *)
  uexpr_no_struct : uassign_no_struct       (uassign_no_struct)
                  | TRETURN uexpr_no_struct
                      (UE_Return (SOME uexpr_no_struct, TRETURNleft))
                  | uclosure_no_struct      (uclosure_no_struct)
  uclosure_no_struct : TBARBAR uexpr_no_struct
                         (mk_closure
                           ([], uexpr_no_struct,
                            TBARBARleft, uexpr_no_structright))
                     | TBAR uclosure_formals TBAR uexpr_no_struct
                         (mk_closure
                           (uclosure_formals, uexpr_no_struct,
                            TBAR1left, uexpr_no_structright))
  uassign_no_struct : urange_no_struct
                        (urange_no_struct)
                    | urange_no_struct uassignop uexpr_no_struct
                        (mk_assign
                          uassignop urange_no_struct uexpr_no_struct)
  urange_no_struct : ubinary_no_struct
                       (ubinary_no_struct)
                   | ubinary_no_struct TDOTDOT ubinary_no_struct
                       (UE_Range
                         (RK_Exclusive, ubinary_no_struct1,
                          ubinary_no_struct2, TDOTDOTleft))
                   | ubinary_no_struct TDOTDOTEQ ubinary_no_struct
                       (UE_Range
                         (RK_Inclusive, ubinary_no_struct1,
                          ubinary_no_struct2, TDOTDOTEQleft))
  ubinary_no_struct : ucast_no_struct
                        (ucast_no_struct)
                    | ubinary_no_struct TBARBAR ubinary_no_struct
                        (UE_Bin
                          (Or, ubinary_no_struct1,
                           ubinary_no_struct2, TBARBARleft))
                    | ubinary_no_struct TAMPAMP ubinary_no_struct
                        (UE_Bin
                          (And, ubinary_no_struct1,
                           ubinary_no_struct2, TAMPAMPleft))
                    | ubinary_no_struct TEQEQ ubinary_no_struct
                        (UE_Bin
                          (Eq, ubinary_no_struct1,
                           ubinary_no_struct2, TEQEQleft))
                    | ubinary_no_struct TNE ubinary_no_struct
                        (UE_Bin
                          (Ne, ubinary_no_struct1,
                           ubinary_no_struct2, TNEleft))
                    | ubinary_no_struct TLT ubinary_no_struct
                        (UE_Bin
                          (Lt, ubinary_no_struct1,
                           ubinary_no_struct2, TLTleft))
                    | ubinary_no_struct TLE ubinary_no_struct
                        (UE_Bin
                          (Le, ubinary_no_struct1,
                           ubinary_no_struct2, TLEleft))
                    | ubinary_no_struct TGT ubinary_no_struct
                        (UE_Bin
                          (Gt, ubinary_no_struct1,
                           ubinary_no_struct2, TGTleft))
                    | ubinary_no_struct TGE ubinary_no_struct
                        (UE_Bin
                          (Ge, ubinary_no_struct1,
                           ubinary_no_struct2, TGEleft))
                    | ubinary_no_struct TBAR ubinary_no_struct
                        (UE_Bin
                          (BOr, ubinary_no_struct1,
                           ubinary_no_struct2, TBARleft))
                    | ubinary_no_struct TCARET ubinary_no_struct
                        (UE_Bin
                          (BXor, ubinary_no_struct1,
                           ubinary_no_struct2, TCARETleft))
                    | ubinary_no_struct TAMP ubinary_no_struct
                        (UE_Bin
                          (BAnd, ubinary_no_struct1,
                           ubinary_no_struct2, TAMPleft))
                    | ubinary_no_struct TSHL ubinary_no_struct
                        (UE_Bin
                          (Shl, ubinary_no_struct1,
                           ubinary_no_struct2, TSHLleft))
                    | ubinary_no_struct TSHR ubinary_no_struct
                        (UE_Bin
                          (Shr, ubinary_no_struct1,
                           ubinary_no_struct2, TSHRleft))
                    | ubinary_no_struct TPLUS ubinary_no_struct
                        (UE_Bin
                          (Add, ubinary_no_struct1,
                           ubinary_no_struct2, TPLUSleft))
                    | ubinary_no_struct TMINUS ubinary_no_struct
                        (UE_Bin
                          (Sub, ubinary_no_struct1,
                           ubinary_no_struct2, TMINUSleft))
                    | ubinary_no_struct TSTAR ubinary_no_struct
                        (UE_Bin
                          (Mul, ubinary_no_struct1,
                           ubinary_no_struct2, TSTARleft))
                    | ubinary_no_struct TSLASH ubinary_no_struct
                        (UE_Bin
                          (Div, ubinary_no_struct1,
                           ubinary_no_struct2, TSLASHleft))
                    | ubinary_no_struct TPERCENT ubinary_no_struct
                        (UE_Bin
                          (Mod, ubinary_no_struct1,
                           ubinary_no_struct2, TPERCENTleft))
  ucast_no_struct : uprefix_no_struct
                      (uprefix_no_struct)
                  | ucast_no_struct TAS ucast_target
                      (UE_Cast
                        (ucast_no_struct, ucast_target, TASleft))
  uprefix_no_struct : upostfix_no_struct
                        (upostfix_no_struct)
                    | TBANG uprefix_no_struct
                        (UE_Unary
                          (U_Not, uprefix_no_struct, TBANGleft))
                    | TAMP uprefix_no_struct
                        (UE_Unary
                          (U_Borrow BM_Imm, uprefix_no_struct, TAMPleft))
                    | TAMP TMUT uprefix_no_struct
                        (UE_Unary
                          (U_Borrow BM_Mut, uprefix_no_struct, TAMPleft))
                    | TSTAR uprefix_no_struct
                        (UE_Unary
                          (U_Deref, uprefix_no_struct, TSTARleft))
  upostfix_no_struct : uprimary_no_struct
                         (uprimary_no_struct)
                     | upostfix_no_struct TQUESTION
                         (UE_Unary
                           (U_Propagate, upostfix_no_struct,
                            TQUESTIONleft))
                     | upostfix_no_struct TDOT IDENT
                         (UE_Field
                           (upostfix_no_struct, IDENT, IDENTleft))
                     | upostfix_no_struct TDOT NUM
                         (mk_tuple_projection
                           (upostfix_no_struct, NUM, NUMleft))
                     | upostfix_no_struct TDOT NUMSFX
                         (mk_tuple_projection
                           (upostfix_no_struct, NUMSFX, NUMSFXleft))
                     | upostfix_no_struct TDOT upath_segment
                         LPAR ucallargs RPAR
                         (mk_call
                           (UC_Method
                             (upostfix_no_struct, upath_segment),
                            ucallargs, upostfix_no_structleft,
                            RPARright))
                     | upostfix_no_struct TLBRACK
                         uexpr TRBRACK
                         (UE_Index
                           (upostfix_no_struct, uexpr,
                            Position.range_position
                              (upostfix_no_structleft,
                               TRBRACKright)))
  uprimary_no_struct : upath
                         (UE_Path upath)
                     | uprimary_nonhead
                         (uprimary_nonhead)
  (* Branches are brace-delimited, and right-associative TIF/TELSE precedence preserves nearest-else
     association through recursive mixed chains. Re-check the [verbose] grm.desc after grammar
     changes. Its only expected conflicts are the two reduce/reduce choices at a comma-free direct
     with-block match arm followed by an `&` or `[` pattern; those tokens can instead continue the
     current body as binary-and or indexing, so such following arms require an explicit comma. *)
  ublock : TLBRACE ubody TRBRACE            (UE_Block (ubody, TLBRACEleft))
         | TLBRACE TRBRACE                  (UE_Block (UE_Unit TLBRACEleft, TLBRACEleft))
  (* Unsafe is block-like in operand and statement positions, but deliberately remains distinct from
     `ublock`: branch delimiters still require ordinary braces. Its frontend semantics are block erasure. *)
  uunsafe : TUNSAFE ublock                  (ublock)
  (* This direct category is used both as a primary and, separately, to decide whether a statement or
     non-final match arm may omit its separator. Wrapping it in any operator leaves this category. *)
  uwith_block_expr : ublock                 (ublock)
                   | uunsafe                (uunsafe)
                   | uconditional           (uconditional)
                   | uloop_expr             (uloop_expr)
                   | umatch                 (umatch)
  usemi_free_stmt : uwith_block_expr ubody
                      (UE_Seq (uwith_block_expr, ubody))
  (* Conditional heads retain only the condition or pattern/scrutinee. The conditional consumes the
     success block once and preserves nearest-else association plus the existing AST/span shape. *)
  uif_head : TIF uexpr_no_struct
                (IH_If (uexpr_no_struct, TIFleft))
           | TIF TLET upat TEQ uexpr_no_struct
                (IH_IfLet (upat, uexpr_no_struct, TIFleft))
  uconditional : uif_head ublock %prec TIF
                    (finish_conditional
                      (uif_head, ublock, NONE, ublockright))
               | uif_head ublock TELSE ublock
                    (finish_conditional
                      (uif_head, ublock1, SOME ublock2,
                       ublock2right))
               | uif_head ublock TELSE uconditional
                    (finish_conditional
                      (uif_head, ublock, SOME uconditional,
                       uconditionalright))
  ufuel : THASH TLBRACK TFUEL LPAR EXPRAQ RPAR TRBRACK
              ((#1 EXPRAQ, THASHleft))
  uloop_expr : ufuel TWHILE LPAR uexpr RPAR ublock
              (UE_While (#1 ufuel, uexpr, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | ufuel TLOOP ublock
              (UE_Loop (#1 ufuel, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | TFOR upat TIN uexpr_no_struct ublock
              (UE_For
                (upat, uexpr_no_struct, ublock,
                 Position.range_position
                   (TFORleft, ublockright)))
             | ufuel TWHILE TLET upat TEQ uexpr_no_struct ublock
              (UE_WhileLet
                (#1 ufuel, upat, uexpr_no_struct, ublock,
                 Position.range_position
                   (#2 ufuel, ublockright)))
  (* Comma lists stay nonempty and right-nested (source order preserved). Each list has an explicit terminal
     comma production, so a trailing separator cannot create an empty element. Calls are dedicated
     atom/method productions, so LPAR is never in FOLLOW(uexpr) as a general postfix operator -- no
     precedence directive is needed here (D23/D77). *)
  arglist : uexpr
              ([uexpr])
          | uexpr COMMA
              ([uexpr])
          | uexpr COMMA arglist
              (uexpr :: arglist)
  ucallargs : ([])
            | arglist (arglist)
  (* Generic macro arguments are complete, nonempty bodies separated by commas. The list as a whole
     may be empty, but deliberately does not share call trailing-comma support. *)
  umacroargs : ubody
                 ([ubody])
             | ubody COMMA umacroargs
                 (ubody :: umacroargs)
  umacrocallargs : ([])
                 | umacroargs             (umacroargs)
  (* A tuple has one element before the comma and a nonempty `arglist` after it. Even when `arglist` has a
     terminal comma, this requires at least two elements and keeps `(x,)` outside the grammar. *)
  (* All match spellings share one production and differ only in the existing flavour tag. Guards reuse
     the complete body grammar, as in the old frontend. One arm production plus the ordinary nonempty
     trailing-comma list keeps guarded and unguarded termination identical. *)
  umatch_kind : TMATCH       ((MF_Auto, TMATCHleft))
              | TMATCHSWITCH ((MF_Switch, TMATCHSWITCHleft))
              | TMATCHCASE   ((MF_Case, TMATCHCASEleft))
  umatch : umatch_kind uexpr_no_struct TLBRACE uarms TRBRACE
              (UE_Match
                (#1 umatch_kind, uexpr_no_struct, uarms,
                 Position.range_position
                   (#2 umatch_kind, TRBRACEright)))
  uguard : ubody (ubody)
  uarm_head : upat TARROW
                (AH_Arm (upat, NONE))
            | upat TIF uguard TARROW
                (AH_Arm (upat, SOME (uguard, TIFleft)))
  uarm : uarm_head uexpr
           (finish_arm (uarm_head, uexpr))
  uarm_with_block : uarm_head uwith_block_expr
                      (finish_arm (uarm_head, uwith_block_expr))
  uarms : uarm                  ([uarm])
        | uarm COMMA            ([uarm])
        | uarm COMMA uarms      (uarm :: uarms)
        | uarm_with_block uarms  (uarm_with_block :: uarms)
  (* The single pattern grammar, shared by every binding site above (D28). Its own nonterminals, disjoint
     from `uexpr`, so the constructor pattern cannot clash with the call production nor or-`|` with bitwise
     or. It deliberately ACCEPTS more than any one site can lower (a numeral in `let`, a constructor under
     `match_switch`); each site's elaborator rejects the rest WITH A POSITION, which beats a bare "syntax
     error" and keeps one grammar for one language. *)
  (* Pattern precedence is explicit rather than yacc-directed. A chained range is retained long enough
     for a positioned non-associativity diagnostic; disjunctions flatten in source order. *)
  upat : upat_alias               (upat_alias)
        | upat_alias TBAR upat
            (mk_or_pat (upat_alias, upat, TBARleft))
  upat_alias : upat_range         (upat_range)
              | upat_ident TAT upat_alias
                  (mk_alias_pat (upat_ident, upat_alias, TATleft))
  upat_range : upat_prefix        (upat_prefix)
              | upat_range TDOTDOT upat_prefix
                  (P_Range (RK_Exclusive, upat_range, upat_prefix, TDOTDOTleft))
              | upat_range TDOTDOTEQ upat_prefix
                  (P_Range (RK_Inclusive, upat_range, upat_prefix, TDOTDOTEQleft))
  upat_prefix : upat_atom         (upat_atom)
               | TAMP upat_prefix
                   (P_Borrow (BM_Imm, upat_prefix, TAMPleft))
               | TAMP TMUT upat_prefix
                   (P_Borrow (BM_Mut, upat_prefix, TAMPleft))
  upat_atom : upath               (mk_bare_path_pat upath)
             | NUM                (P_Literal (LP_Integer (NUM, NUMleft)))
             | TTRUE              (P_Literal (LP_Bool (true, TTRUEleft)))
             | TFALSE             (P_Literal (LP_Bool (false, TFALSEleft)))
             | STRING             (P_Literal (LP_String (STRING, STRINGleft)))
             | VALAQ              (P_Literal (LP_ValAntiq VALAQ))
             | upath LPAR upats RPAR
                 (mk_ctor_pat (upath, upats))
             | LPAR upat RPAR
                 (P_Group upat)
             | LPAR upat COMMA upats RPAR
                 (P_Tuple (upat :: upats, Position.range_position (LPARleft, RPARright)))
             | TLBRACK TRBRACK
                 (P_Slice ([], Position.range_position (TLBRACKleft, TRBRACKright)))
             | TLBRACK uslice_items TRBRACK
                 (P_Slice (uslice_items, Position.range_position (TLBRACKleft, TRBRACKright)))
             | upath TLBRACE ustruct_fields TRBRACE
                 (mk_struct_pat (upath, ustruct_fields))
  upat_ident : IDENT              ((IDENT, IDENTleft))
  upats : upat %prec TPATCONTEXT ([upat])
        | upat COMMA              ([upat])
        | upat COMMA upats        (upat :: upats)
  uslice_item : upat %prec TPATCONTEXT
                                      (SI_Pat upat)
               | TDOTDOT          (SI_Rest TDOTDOTleft)
  uslice_items : uslice_item      ([uslice_item])
                | uslice_item COMMA
                    ([uslice_item])
                | uslice_item COMMA uslice_items
                    (uslice_item :: uslice_items)
  ustruct_field : IDENT TCOLON upat %prec TPATCONTEXT
                      (SF_Field (IDENT, IDENTleft, upat))
                | IDENT
                      (SF_Shorthand (IDENT, IDENTleft))
                | TDOTDOT
                      (SF_Rest TDOTDOTleft)
  ustruct_fields : ustruct_field  ([ustruct_field])
                 | ustruct_field COMMA
                      ([ustruct_field])
                 | ustruct_field COMMA ustruct_fields
                      (ustruct_field :: ustruct_fields)
  (* Expression labels remain syntax-only and source-ordered. Empty fields and one terminal comma are
     accepted without adding shorthand or rest syntax. *)
  ustruct_expr : upath TLBRACE TRBRACE
                   (make_struct_expression
                     (upath, [], TRBRACEright))
               | upath TLBRACE ustruct_expr_fields TRBRACE
                   (make_struct_expression
                     (upath, ustruct_expr_fields, TRBRACEright))
  ustruct_expr_field : IDENT TCOLON ubody
                         (SE_Field (IDENT, IDENTleft, ubody))
  ustruct_expr_fields : ustruct_expr_field
                          ([ustruct_expr_field])
                      | ustruct_expr_field COMMA
                          ([ustruct_expr_field])
                      | ustruct_expr_field COMMA ustruct_expr_fields
                          (ustruct_expr_field :: ustruct_expr_fields)
  ulog_data_entry : LOGSTRING
                      (LDE_String
                        (LOGSTRING,
                         Position.range_position
                           (LOGSTRINGleft, LOGSTRINGright)))
                  | LOGIDENT
                      (LDE_Identifier
                        (LOGIDENT, LOGIDENTleft))
  ulog_data_entries : ulog_data_entry
                        ([ulog_data_entry])
                    | ulog_data_entry COMMA ulog_data_entries
                        (ulog_data_entry :: ulog_data_entries)
\<close>

end
