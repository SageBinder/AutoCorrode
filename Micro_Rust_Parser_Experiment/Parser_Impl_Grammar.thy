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
    * turbofish_error pos raises the unterminated-group diagnostic at the generic opener.
    * function_literal_suffix_error pos rejects an arity suffix separated from its value
      antiquotation and reports at that suffix.
    * struct_head_generics_error pos rejects generic arguments on any struct-expression head
      segment and reports at that argument group.

  All six functions have result type 'a because they always raise via error.  Their exact string
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
HOL content. Yacc directives reproduce the frontend precedence
(\<open>Micro_Rust_Syntax.thy:559-639\<close>). Only token shims remain lexer-local; positions use
\<open>Parser_Lex_Util\<close>.
\<close>
(*
  This declaration generates the private URust lexer/parser functors used by Parser_Impl_Diagnostics.
  Together they own recognition of one uRust expression source and construction of the unresolved
  URust_AST. Their boundary includes tokenization, PIDE token
  reports, precedence and sequencing policy, and grammar-action construction of AST nodes.  It ends
  before identifier or constructor resolution, site-specific pattern validation, lowering to shallow
  terms, and HOL type checking.

  Parser_Impl_Diagnostics relies on the standard expert-mode Lex/Yacc functor interface:

    * URustLexFun produces the lexer structure accepted by the ML-Yacc Join functor. Its
      UserDeclarations.set_layout layout ctxt operation initializes the Isabelle-Lex-Yacc runtime from
      the shared source layout and resets all antiquotation/generic state. The
      source-taking set wrapper remains for generated-driver compatibility.
    * URustLrValsFun supplies the generated semantic value/result types, actions, LR table, tokens, and
      recovery data. Parser_Impl_Diagnostics instantiates it once and rejoins that exact data with the
      generated lexer while replacing only terminal rendering.
    * The generated Tokens.EOF constructs the dummy end token required by
      Parser_Lex_Util.parse_source_with_layout. Its Position.T * Position.T argument delimits the
      token. Other generated token constructors are lexer implementation details; terminal additions
      or reordering must still be reflected in Parser_Impl_Diagnostics' exhaustive terminal identity
      table.
    * The start result is URust_AST.ur_expr option.  NONE represents empty input; SOME ast preserves
      source order and the token/span positions recorded by URust_AST.  Syntax rejection raises a
      positioned ERROR rather than returning NONE.

  Expert mode deliberately generates no unsealed URust structure or default parse_source operation.
  Parser clients use the sealed URust_Diagnostics.parse_source boundary. Lexer refs, start states,
  buffers, position-map helpers, grammar nonterminals, LR states/tables, semantic-value encodings, and
  generated functor names remain implementation details shared only with Parser_Impl_Diagnostics.
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

fun reset_aq () =
  (aq_kind := No_AQ; aq_buf := []; aq_start := 0; aq_open := 0; aq_depth := 0)
fun reset_generic () = generic_open := NONE
fun reset_state () = (reset_aq (); reset_generic ())
fun start_aq kind open_pos body_pos =
  (aq_kind := kind; aq_buf := []; aq_start := body_pos; aq_open := open_pos; aq_depth := 0)
fun push_aq fragment = aq_buf := fragment :: !aq_buf
fun take_aq () =
  let val body = String.concat (rev (!aq_buf))
  in reset_aq (); body end

(* A suffixed integer literal is deliberately NOT interpreted here: the lexer captures the raw lexeme and
   the elaboration term layer reads it against the single suffix table, so an unknown suffix is a
   POSITIONED elaborator error rather than an unpositioned `raise Fail` in lexer code (D29). The bare-hex
   rule precedes the general digit-plus-identifier rule so equal-length `0xff` is NUM, while longer
   `0xffu8` and unsupported glued suffixes are each one NUMSFX token.

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

fun eof () =
  (case !aq_kind of
     No_AQ =>
       (case !generic_open of
          NONE => Tokens.EOF (Position.none, Position.none)
        | SOME pos =>
            URust_Grammar.turbofish_error pos)
   | Value_AQ => URust_Grammar.antiquotation_error "value" (fixed_pos (!aq_open))
   | Expr_AQ => URust_Grammar.antiquotation_error "expression" (fixed_pos (!aq_open)))
\<close>
lex_definitions\<open>
%header (functor URustLexFun(structure Tokens: URust_TOKENS));
%s VAQ EAQ GENERIC;
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
<INITIAL>"0x"{hexdigit}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>{digit}+{idstart}{idchar}* =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", Tokens.NUMSFX, yytext));
<INITIAL>{digit}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
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
    IH_If of ur_expr * ur_expr * Position.T * Position.T
  | IH_IfLet of
      ur_pat * ur_expr * ur_expr * Position.T * Position.T

fun if_head_stop (IH_If (_, _, _, stop)) = stop
  | if_head_stop (IH_IfLet (_, _, _, _, stop)) = stop

fun finish_conditional
      (IH_If (condition, success, pos, _), fallback, _) =
      UE_If (condition, success, fallback, pos)
  | finish_conditional
      (IH_IfLet (pattern, value, success, pos, _), fallback, stop) =
      UE_IfLet
        (pattern, value, success, fallback,
         Position.range_position (pos, stop))

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

datatype path_block_tail =
    PBT_Block of ur_expr option * Position.T
  | PBT_Struct of
      struct_expr_field list * Position.T * ur_expr * Position.T

fun finish_path_block (path, left, tail) =
  (case tail of
     PBT_Block (body, right) =>
       (UE_Path path,
        UE_Block
          ((case body of
              SOME expression => expression
            | NONE => UE_Unit left),
           left),
        right)
   | PBT_Struct (fields, struct_right, block, right) =>
       (make_struct_expression (path, fields, struct_right),
        block, right))

datatype path_arms_tail =
    PAT_Arms of ur_arm list * Position.T
  | PAT_Struct of
      struct_expr_field list * Position.T * ur_arm list * Position.T

fun finish_path_arms (path, tail) =
  (case tail of
     PAT_Arms (arms, right) =>
       (UE_Path path, arms, right)
   | PAT_Struct (fields, struct_right, arms, right) =>
       (make_struct_expression (path, fields, struct_right),
        arms, right))

fun map_followed_expression f (expression, follower, right) =
  (f expression, follower, right)

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

(* Operator precedence, loosest -> tightest (the frontend's infix priorities). Return is below
   with-block expressions, so `return { e }` takes the block as its operand instead of becoming an
   operandless return followed by a block statement. Comparisons are non-associative (Rust rejects
   `a == b == c`). Ranges and assignment use structural tiers below. Reference prefixes and `!` use
   structural tiers too; these directives keep the ambiguous `uexp OP uexp` productions
   conflict-free. *)
%right TRETURN
%right TIF TELSE TLBRACE TLBRACK TUNSAFE TWHILE TLOOP TFOR
%nonassoc TDOTDOT TDOTDOTEQ
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
%right TBANG

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
%nonterm ustart of URust_AST.ur_expr option
       | ubody of URust_AST.ur_expr
       | ubinding_head of binding_head
       | uval of URust_AST.ur_expr
       | uclosure_arg of URust_AST.ur_expr
       | uclosure of URust_AST.ur_expr
       | uclosure_formals of URust_AST.ur_pat list
       | uclosure_body of URust_AST.ur_expr
       | uclosure_if_head of if_head
       | uclosure_conditional of URust_AST.ur_expr
       | uassign of URust_AST.ur_expr
       | uassignop of URust_AST.assignop * Position.T
       | urange of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
       | urefprefix of URust_AST.ur_expr
       | unotprefix of URust_AST.ur_expr
       | ucast of URust_AST.ur_expr
       | ucast_target of URust_AST.cast_target
       | upostfix of URust_AST.ur_expr
       | uatom of URust_AST.ur_expr
       | uatom_nonhead of URust_AST.ur_expr
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
       | uwith_block_atom of URust_AST.ur_expr
       | ucontrol_expr of URust_AST.ur_expr
       | usemi_free_stmt of URust_AST.ur_expr
       | uconditional of URust_AST.ur_expr
       | uif_head of if_head
       | uval_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | uassign_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | urange_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | uexp_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | urefprefix_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | unotprefix_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | ucast_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | upostfix_before_block of
           URust_AST.ur_expr * URust_AST.ur_expr * Position.T
       | upath_block_tail of path_block_tail
       | ufuel of Input.source * Position.T
       | uloop_expr of URust_AST.ur_expr
       | umatch_kind of URust_AST.match_flavour * Position.T
       | umatch of URust_AST.ur_expr
       | umatch_scrutinee of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | uval_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | uassign_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | urange_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | uexp_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | urefprefix_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | unotprefix_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | ucast_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | upostfix_before_arms of
           URust_AST.ur_expr * URust_AST.ur_arm list * Position.T
       | upath_arms_tail of path_arms_tail
       | uguard of URust_AST.ur_expr
       | uarm of URust_AST.ur_arm
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
\<close>
yacc_rules\<open>
  ustart : ubody (SOME ubody)
         | (NONE)
  (* A body is a value, semicolon sequencing, a policy-approved semicolon-free statement followed by
     another body, or a binding head followed by its required semicolon and continuation. The same
     nonterminal is used for block contents and match guards, matching the old frontend's unrestricted
     `urust` guard slot without duplicating statement syntax. *)
  ubody : uval                              (uval)
        | uclosure                          (uclosure)
        | uval TSEMI ubody                  (UE_Seq (uval, ubody))
        | uval TSEMI                        (finish_statement (uval, TSEMIleft))
        | usemi_free_stmt                   (usemi_free_stmt)
        | ubinding_head TSEMI ubody
            (finish_binding (ubinding_head, ubody, ubodyright))
  (* Binding heads are grammar-private. The binder is the shared `upat`, so every site continues to use
     the existing pattern validation and lowering policies. *)
  ubinding_head : TLET upat TEQ uval
                    (BH_Let (upat, uval))
                | TLET TMUT upat TEQ uval
                    (BH_LetMut (upat, uval, TMUTleft))
                | TCONST upat TEQ uval
                    (BH_Const (upat, uval))
                | TLET upat TEQ uval TELSE ublock
                    (BH_LetElse (upat, uval, ublock, TLETleft))
  (* Value position: an operand OR a with-block control-flow expr. `uval` is where `if`/`match` (later
     loops) are admitted -- let-RHS, condition, call args, parens -- WITHOUT being a bare binary-operator
     operand (that stays `uexp`, closing divergence D-1 -- D25). *)
  uval : uassign (uassign)
       | TRETURN (UE_Return (NONE, TRETURNleft))
       | TRETURN uclosure_arg
           (UE_Return (SOME uclosure_arg, TRETURNleft))
       | ucontrol_expr %prec TIF (ucontrol_expr)
  (* Bare closures deliberately remain outside uval, uassign, and uexp. This delimiter-level category
     is used only by the grammar sites where a closure may appear without grouping. Parentheses turn
     the resulting closure node back into an ordinary atom. *)
  uclosure_arg : uval                       (uval)
               | uclosure                   (uclosure)
  uclosure : TBARBAR uclosure_body
                (mk_closure
                  ([], uclosure_body,
                   TBARBARleft, uclosure_bodyright))
           | TBAR uclosure_formals TBAR uclosure_body
                (mk_closure
                  (uclosure_formals, uclosure_body,
                   TBAR1left, uclosure_bodyright))
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
  (* This is the old frontend's priority-20 closure-body boundary: assignments and pure expressions,
     ordinary conditionals, matches, blocks/unsafe blocks through uassign, and legacy semicolon-bearing
     returns. Bindings, if-let, loops, sequencing, direct nested closures, and semicolon-free returns
     enter only through an explicit block or another admitted delimiter context. *)
  uclosure_body : uassign                   (uassign)
                | uclosure_conditional      (uclosure_conditional)
                | umatch                    (umatch)
                | TRETURN TSEMI
                    (UE_Return (NONE, TRETURNleft))
                | TRETURN uclosure_arg TSEMI
                    (UE_Return (SOME uclosure_arg, TRETURNleft))
  (* This head deliberately does not reuse uif_head: closure-body priority admits only ordinary if,
     and the recursive closure conditional must exclude if-let from every later else-if arm too. *)
  uclosure_if_head : TIF uval_before_block
                       (IH_If
                         (#1 uval_before_block,
                          #2 uval_before_block,
                          TIFleft,
                          #3 uval_before_block))
  uclosure_conditional : uclosure_if_head %prec TIF
                           (finish_conditional
                             (uclosure_if_head, NONE,
                              if_head_stop uclosure_if_head))
                       | uclosure_if_head TELSE ublock
                           (finish_conditional
                             (uclosure_if_head, SOME ublock,
                              ublockright))
                       | uclosure_if_head TELSE uclosure_conditional
                           (finish_conditional
                             (uclosure_if_head, SOME uclosure_conditional,
                              uclosure_conditionalright))
  (* Assignment is below ranges and every pure operator and recurses through its own tier on the right.
     Blocks remain ordinary expression atoms, while lower-priority `if`/`match` forms require
     parentheses on the RHS, matching the frontend's priority-40 boundary. The LHS crosses
     expr_to_place exactly once. *)
  uassign : urange (urange)
          | urange uassignop uassign (mk_assign uassignop urange uassign)
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
  (* Bounded ranges form one non-associative tier between logical OR and assignment. Their endpoints
     are complete pure expressions, so every tighter binary operator remains inside the endpoint. *)
  urange : uexp (uexp)
         | uexp TDOTDOT uexp
             (UE_Range (RK_Exclusive, uexp1, uexp2, TDOTDOTleft))
         | uexp TDOTDOTEQ uexp
             (UE_Range (RK_Inclusive, uexp1, uexp2, TDOTDOTEQleft))
  (* Postfixes form a structural tier above atoms, so `?`, field access, and methods compose
     left-to-right and bind tighter than prefix/binary operators. Indexing shares this tier. A dotted
     identifier followed by parentheses is a method; without parentheses it is an NField lens access. *)
  upostfix : uatom (uatom)
           | upostfix TQUESTION
               (UE_Unary (U_Propagate, upostfix, TQUESTIONleft))
           | upostfix TDOT IDENT
               (UE_Field (upostfix, IDENT, IDENTleft))
           | upostfix TDOT upath_segment LPAR ucallargs RPAR
               (mk_call
                  (UC_Method (upostfix, upath_segment),
                   ucallargs, upostfixleft, RPARright))
           | upostfix TLBRACK uclosure_arg TRBRACK
               (UE_Index
                 (upostfix, uclosure_arg,
                  Position.range_position (upostfixleft, TRBRACKright)))
  uatom : upath      (UE_Path upath)
        | ustruct_expr (ustruct_expr)
        | uatom_nonhead (uatom_nonhead)
  uatom_nonhead : NUM        (UE_Literal (LP_Integer (NUM, NUMleft)))
        | NUMSFX     (UE_Literal (LP_Integer (NUMSFX, NUMSFXleft)))
        | TTRUE      (UE_Literal (LP_Bool (true, TTRUEleft)))
        | TFALSE     (UE_Literal (LP_Bool (false, TFALSEleft)))
        | STRING     (UE_Literal (LP_String (STRING, STRINGleft)))
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
        | TMATCHESBANG LPAR uclosure_arg COMMA upat RPAR
            (UE_Macro
              (make_single_path
                 ("matches",
                  Position.range_position (TMATCHESBANGleft, TMATCHESBANG)),
               TMATCHESBANG,
               MP_Matches (uclosure_arg, upat),
               Position.range_position (TMATCHESBANGleft, RPARright)))
        | LPAR RPAR  (UE_Unit LPARleft)
        | LPAR uclosure_arg COMMA arglist RPAR
            (UE_Tuple
              (uclosure_arg :: arglist,
               Position.range_position (LPARleft, RPARright)))
        | LPAR uclosure_arg RPAR
            (UE_Group
              (uclosure_arg,
               Position.range_position (LPARleft, RPARright)))
        | TLBRACK TRBRACK
            (UE_Array ([], Position.range_position (TLBRACKleft, TRBRACKright)))
        | TLBRACK arglist TRBRACK
            (UE_Array (arglist, Position.range_position (TLBRACKleft, TRBRACKright)))
        | VALAQ      (UE_Literal (LP_ValAntiq VALAQ))
        | EXPRAQ     (UE_ExprAntiq (#1 EXPRAQ))
        | uwith_block_atom %prec TIF (uwith_block_atom)
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
  (* Casts form one left-recursive tier above every prefix and below postfix expressions. Repeated
     casts therefore associate left, while a field, method, index, or propagation after a cast
     requires grouping. The target grammar is closed to the legacy frontend's seven integral and ten
     raw-pointer targets. *)
  ucast : upostfix (upostfix)
        | ucast TAS ucast_target
            (UE_Cast (ucast, ucast_target, TASleft))
  ucast_target : TUINT
                   (CT_Unsigned TUINT)
               | TSINT
                   (CT_Signed TSINT)
               | TSTAR TCONST TUINT
                   (CT_RawPointer (RPM_Const, TUINT))
               | TSTAR TMUT TUINT
                   (CT_RawPointer (RPM_Mut, TUINT))
  (* Reference prefixes bind tighter than every binary operator and looser than `!`, matching the
     frontend priorities. Casts bind tighter than all prefixes, resolving the old frontend's
     type-dependent prefix/cast ambiguity deterministically. Recursing through the reference tier
     makes `**x` two ordinary dereference nodes while preserving the binary meanings of `*` and `&`;
     mixed and deeper recursion is a documented accepted-surface improvement over the frontend's
     fixed prefix productions. *)
  unotprefix : ucast (ucast)
             | TBANG unotprefix (UE_Unary (U_Not, unotprefix, TBANGleft))
  urefprefix : unotprefix (unotprefix)
             | TAMP urefprefix
                 (UE_Unary (U_Borrow BM_Imm, urefprefix, TAMPleft))
             | TAMP TMUT urefprefix
                 (UE_Unary (U_Borrow BM_Mut, urefprefix, TAMPleft))
             | TSTAR urefprefix
                 (UE_Unary (U_Deref, urefprefix, TSTARleft))
  uexp : urefprefix (urefprefix)
       (* `ucontrol_expr` is deliberately NOT a `uexp` alternative (closes D-1): it reaches value
          position via `uval` and operand position only when parenthesized. *)
       | uexp TPLUS uexp     (UE_Bin (Add,  uexp1, uexp2, TPLUSleft))
       | uexp TMINUS uexp    (UE_Bin (Sub,  uexp1, uexp2, TMINUSleft))
       | uexp TSTAR uexp     (UE_Bin (Mul,  uexp1, uexp2, TSTARleft))
       | uexp TSLASH uexp    (UE_Bin (Div,  uexp1, uexp2, TSLASHleft))
       | uexp TPERCENT uexp  (UE_Bin (Mod,  uexp1, uexp2, TPERCENTleft))
       | uexp TSHL uexp      (UE_Bin (Shl,  uexp1, uexp2, TSHLleft))
       | uexp TSHR uexp      (UE_Bin (Shr,  uexp1, uexp2, TSHRleft))
       | uexp TAMP uexp      (UE_Bin (BAnd, uexp1, uexp2, TAMPleft))
       | uexp TBAR uexp      (UE_Bin (BOr,  uexp1, uexp2, TBARleft))
       | uexp TCARET uexp    (UE_Bin (BXor, uexp1, uexp2, TCARETleft))
       | uexp TEQEQ uexp     (UE_Bin (Eq,   uexp1, uexp2, TEQEQleft))
       | uexp TNE uexp       (UE_Bin (Ne,   uexp1, uexp2, TNEleft))
       | uexp TLT uexp       (UE_Bin (Lt,   uexp1, uexp2, TLTleft))
       | uexp TLE uexp       (UE_Bin (Le,   uexp1, uexp2, TLEleft))
       | uexp TGT uexp       (UE_Bin (Gt,   uexp1, uexp2, TGTleft))
       | uexp TGE uexp       (UE_Bin (Ge,   uexp1, uexp2, TGEleft))
       | uexp TAMPAMP uexp   (UE_Bin (And,  uexp1, uexp2, TAMPAMPleft))
       | uexp TBARBAR uexp   (UE_Bin (Or,   uexp1, uexp2, TBARBARleft))
  (* These private right-edge grammars carry a known block or match-arm follower through the ordinary
     precedence tiers. A path at that edge consumes the opening brace before choosing between an
     ordinary follower and `label: initializer` struct fields. Keeping block and arm followers
     separate prevents their brace contents from competing and requires neither lexer lookahead nor
     precedence-based brace resolution. *)
  uval_before_block : uassign_before_block
                        (uassign_before_block)
                    | TRETURN uval_before_block
                        (map_followed_expression
                          (fn expression =>
                            UE_Return (SOME expression, TRETURNleft))
                          uval_before_block)
                    | ucontrol_expr ublock %prec TIF
                        ((ucontrol_expr, ublock, ublockright))
  uassign_before_block : urange_before_block
                           (urange_before_block)
                       | urange uassignop uassign_before_block
                           (map_followed_expression
                             (mk_assign uassignop urange)
                             uassign_before_block)
  urange_before_block : uexp_before_block
                          (uexp_before_block)
                      | uexp TDOTDOT uexp_before_block
                          (map_followed_expression
                            (fn upper =>
                              UE_Range
                                (RK_Exclusive, uexp, upper,
                                 TDOTDOTleft))
                            uexp_before_block)
                      | uexp TDOTDOTEQ uexp_before_block
                          (map_followed_expression
                            (fn upper =>
                              UE_Range
                                (RK_Inclusive, uexp, upper,
                                 TDOTDOTEQleft))
                            uexp_before_block)
  uexp_before_block : urefprefix_before_block
                        (urefprefix_before_block)
                    | uexp TPLUS uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Add, uexp, right, TPLUSleft))
                          uexp_before_block)
                    | uexp TMINUS uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Sub, uexp, right, TMINUSleft))
                          uexp_before_block)
                    | uexp TSTAR uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Mul, uexp, right, TSTARleft))
                          uexp_before_block)
                    | uexp TSLASH uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Div, uexp, right, TSLASHleft))
                          uexp_before_block)
                    | uexp TPERCENT uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Mod, uexp, right, TPERCENTleft))
                          uexp_before_block)
                    | uexp TSHL uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Shl, uexp, right, TSHLleft))
                          uexp_before_block)
                    | uexp TSHR uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Shr, uexp, right, TSHRleft))
                          uexp_before_block)
                    | uexp TAMP uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (BAnd, uexp, right, TAMPleft))
                          uexp_before_block)
                    | uexp TBAR uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (BOr, uexp, right, TBARleft))
                          uexp_before_block)
                    | uexp TCARET uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (BXor, uexp, right, TCARETleft))
                          uexp_before_block)
                    | uexp TEQEQ uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Eq, uexp, right, TEQEQleft))
                          uexp_before_block)
                    | uexp TNE uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Ne, uexp, right, TNEleft))
                          uexp_before_block)
                    | uexp TLT uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Lt, uexp, right, TLTleft))
                          uexp_before_block)
                    | uexp TLE uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Le, uexp, right, TLEleft))
                          uexp_before_block)
                    | uexp TGT uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Gt, uexp, right, TGTleft))
                          uexp_before_block)
                    | uexp TGE uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Ge, uexp, right, TGEleft))
                          uexp_before_block)
                    | uexp TAMPAMP uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (And, uexp, right, TAMPAMPleft))
                          uexp_before_block)
                    | uexp TBARBAR uexp_before_block
                        (map_followed_expression
                          (fn right =>
                            UE_Bin (Or, uexp, right, TBARBARleft))
                          uexp_before_block)
  urefprefix_before_block : unotprefix_before_block
                              (unotprefix_before_block)
                          | TAMP urefprefix_before_block
                              (map_followed_expression
                                (fn operand =>
                                  UE_Unary
                                    (U_Borrow BM_Imm, operand,
                                     TAMPleft))
                                urefprefix_before_block)
                          | TAMP TMUT urefprefix_before_block
                              (map_followed_expression
                                (fn operand =>
                                  UE_Unary
                                    (U_Borrow BM_Mut, operand,
                                     TAMPleft))
                                urefprefix_before_block)
                          | TSTAR urefprefix_before_block
                              (map_followed_expression
                                (fn operand =>
                                  UE_Unary
                                    (U_Deref, operand, TSTARleft))
                                urefprefix_before_block)
  unotprefix_before_block : ucast_before_block
                              (ucast_before_block)
                          | TBANG unotprefix_before_block
                              (map_followed_expression
                                (fn operand =>
                                  UE_Unary
                                    (U_Not, operand, TBANGleft))
                                unotprefix_before_block)
  ucast_before_block : upostfix_before_block
                         (upostfix_before_block)
                     | ucast TAS ucast_target ublock
                         ((UE_Cast
                             (ucast, ucast_target, TASleft),
                           ublock, ublockright))
  upostfix_before_block :
      uatom_nonhead ublock
        ((uatom_nonhead, ublock, ublockright))
    | upath TLBRACE upath_block_tail
        (finish_path_block
          (upath, TLBRACEleft, upath_block_tail))
    | upostfix TQUESTION ublock
        ((UE_Unary (U_Propagate, upostfix, TQUESTIONleft),
          ublock, ublockright))
    | upostfix TDOT IDENT ublock
        ((UE_Field (upostfix, IDENT, IDENTleft),
          ublock, ublockright))
    | upostfix TDOT upath_segment LPAR ucallargs RPAR ublock
        ((mk_call
            (UC_Method (upostfix, upath_segment),
             ucallargs, upostfixleft, RPARright),
          ublock, ublockright))
    | upostfix TLBRACK uclosure_arg TRBRACK ublock
        ((UE_Index
            (upostfix, uclosure_arg,
             Position.range_position
               (upostfixleft, TRBRACKright)),
          ublock, ublockright))
  upath_block_tail : ubody TRBRACE
                       (PBT_Block (SOME ubody, TRBRACEright))
                   | TRBRACE
                       (PBT_Block (NONE, TRBRACEright))
                   | ustruct_expr_fields TRBRACE ublock
                       (PBT_Struct
                         (ustruct_expr_fields, TRBRACEright,
                          ublock, ublockright))
  uval_before_arms : uassign_before_arms
                       (uassign_before_arms)
                   | TRETURN uval_before_arms
                       (map_followed_expression
                         (fn expression =>
                           UE_Return (SOME expression, TRETURNleft))
                         uval_before_arms)
                   | ucontrol_expr TLBRACE uarms TRBRACE %prec TIF
                       ((ucontrol_expr, uarms, TRBRACEright))
  uassign_before_arms : urange_before_arms
                          (urange_before_arms)
                      | urange uassignop uassign_before_arms
                          (map_followed_expression
                            (mk_assign uassignop urange)
                            uassign_before_arms)
  urange_before_arms : uexp_before_arms
                         (uexp_before_arms)
                     | uexp TDOTDOT uexp_before_arms
                         (map_followed_expression
                           (fn upper =>
                             UE_Range
                               (RK_Exclusive, uexp, upper,
                                TDOTDOTleft))
                           uexp_before_arms)
                     | uexp TDOTDOTEQ uexp_before_arms
                         (map_followed_expression
                           (fn upper =>
                             UE_Range
                               (RK_Inclusive, uexp, upper,
                                TDOTDOTEQleft))
                           uexp_before_arms)
  uexp_before_arms : urefprefix_before_arms
                       (urefprefix_before_arms)
                   | uexp TPLUS uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Add, uexp, right, TPLUSleft))
                         uexp_before_arms)
                   | uexp TMINUS uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Sub, uexp, right, TMINUSleft))
                         uexp_before_arms)
                   | uexp TSTAR uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Mul, uexp, right, TSTARleft))
                         uexp_before_arms)
                   | uexp TSLASH uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Div, uexp, right, TSLASHleft))
                         uexp_before_arms)
                   | uexp TPERCENT uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Mod, uexp, right, TPERCENTleft))
                         uexp_before_arms)
                   | uexp TSHL uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Shl, uexp, right, TSHLleft))
                         uexp_before_arms)
                   | uexp TSHR uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Shr, uexp, right, TSHRleft))
                         uexp_before_arms)
                   | uexp TAMP uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (BAnd, uexp, right, TAMPleft))
                         uexp_before_arms)
                   | uexp TBAR uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (BOr, uexp, right, TBARleft))
                         uexp_before_arms)
                   | uexp TCARET uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (BXor, uexp, right, TCARETleft))
                         uexp_before_arms)
                   | uexp TEQEQ uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Eq, uexp, right, TEQEQleft))
                         uexp_before_arms)
                   | uexp TNE uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Ne, uexp, right, TNEleft))
                         uexp_before_arms)
                   | uexp TLT uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Lt, uexp, right, TLTleft))
                         uexp_before_arms)
                   | uexp TLE uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Le, uexp, right, TLEleft))
                         uexp_before_arms)
                   | uexp TGT uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Gt, uexp, right, TGTleft))
                         uexp_before_arms)
                   | uexp TGE uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Ge, uexp, right, TGEleft))
                         uexp_before_arms)
                   | uexp TAMPAMP uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (And, uexp, right, TAMPAMPleft))
                         uexp_before_arms)
                   | uexp TBARBAR uexp_before_arms
                       (map_followed_expression
                         (fn right =>
                           UE_Bin (Or, uexp, right, TBARBARleft))
                         uexp_before_arms)
  urefprefix_before_arms : unotprefix_before_arms
                             (unotprefix_before_arms)
                         | TAMP urefprefix_before_arms
                             (map_followed_expression
                               (fn operand =>
                                 UE_Unary
                                   (U_Borrow BM_Imm, operand,
                                    TAMPleft))
                               urefprefix_before_arms)
                         | TAMP TMUT urefprefix_before_arms
                             (map_followed_expression
                               (fn operand =>
                                 UE_Unary
                                   (U_Borrow BM_Mut, operand,
                                    TAMPleft))
                               urefprefix_before_arms)
                         | TSTAR urefprefix_before_arms
                             (map_followed_expression
                               (fn operand =>
                                 UE_Unary
                                   (U_Deref, operand, TSTARleft))
                               urefprefix_before_arms)
  unotprefix_before_arms : ucast_before_arms
                             (ucast_before_arms)
                         | TBANG unotprefix_before_arms
                             (map_followed_expression
                               (fn operand =>
                                 UE_Unary
                                   (U_Not, operand, TBANGleft))
                               unotprefix_before_arms)
  ucast_before_arms : upostfix_before_arms
                        (upostfix_before_arms)
                    | ucast TAS ucast_target TLBRACE uarms TRBRACE
                        ((UE_Cast
                            (ucast, ucast_target, TASleft),
                          uarms, TRBRACEright))
  upostfix_before_arms :
      uatom_nonhead TLBRACE uarms TRBRACE
        ((uatom_nonhead, uarms, TRBRACEright))
    | upath TLBRACE upath_arms_tail
        (finish_path_arms (upath, upath_arms_tail))
    | upostfix TQUESTION TLBRACE uarms TRBRACE
        ((UE_Unary (U_Propagate, upostfix, TQUESTIONleft),
          uarms, TRBRACEright))
    | upostfix TDOT IDENT TLBRACE uarms TRBRACE
        ((UE_Field (upostfix, IDENT, IDENTleft),
          uarms, TRBRACEright))
    | upostfix TDOT upath_segment LPAR ucallargs RPAR
        TLBRACE uarms TRBRACE
        ((mk_call
            (UC_Method (upostfix, upath_segment),
             ucallargs, upostfixleft, RPARright),
          uarms, TRBRACEright))
    | upostfix TLBRACK uclosure_arg TRBRACK
        TLBRACE uarms TRBRACE
        ((UE_Index
            (upostfix, uclosure_arg,
             Position.range_position
               (upostfixleft, TRBRACKright)),
          uarms, TRBRACEright))
  upath_arms_tail : uarms TRBRACE
                      (PAT_Arms (uarms, TRBRACEright))
                  | ustruct_expr_fields TRBRACE TLBRACE uarms TRBRACE
                      (PAT_Struct
                        (ustruct_expr_fields, TRBRACE1right,
                         uarms, TRBRACE2right))
  (* Branches are brace-delimited, and right-associative TIF/TELSE precedence preserves nearest-else
     association through recursive mixed chains. The whole grammar is verified conflict-free via the
     [verbose] grm.desc export -- RE-CHECK IT after any grammar change. *)
  ublock : TLBRACE ubody TRBRACE            (UE_Block (ubody, TLBRACEleft))
         | TLBRACE TRBRACE                  (UE_Block (UE_Unit TLBRACEleft, TLBRACEleft))
  (* Unsafe is block-like in operand and statement positions, but deliberately remains distinct from
     `ublock`: branch delimiters still require ordinary braces. Its frontend semantics are block erasure. *)
  uunsafe : TUNSAFE ublock                  (ublock)
  (* Placement and semicolon policy are independent: with-block atoms are ordinary operands, control
     expressions are values, and either category may be sequenced without a semicolon when another
     body follows. *)
  uwith_block_atom : ublock                 (ublock)
                   | uunsafe                (uunsafe)
  usemi_free_stmt : uwith_block_atom ubody
                      (UE_Seq (uwith_block_atom, ubody))
                  | ucontrol_expr ubody
                      (UE_Seq (ucontrol_expr, ubody))
  ucontrol_expr : uconditional              (uconditional)
                | uloop_expr                (uloop_expr)
                | umatch                    (umatch)
  (* Conditional heads are grammar-private. One fallback grammar preserves nearest-else association,
     mixed `else if` / `else if let` chains, and the existing AST/span representation. *)
  uif_head : TIF uval_before_block
                (IH_If
                  (#1 uval_before_block,
                   #2 uval_before_block,
                   TIFleft,
                   #3 uval_before_block))
           | TIF TLET upat TEQ uval_before_block
                (IH_IfLet
                  (upat, #1 uval_before_block,
                   #2 uval_before_block, TIFleft,
                   #3 uval_before_block))
  uconditional : uif_head %prec TIF
                    (finish_conditional
                      (uif_head, NONE, if_head_stop uif_head))
               | uif_head TELSE ublock
                    (finish_conditional
                      (uif_head, SOME ublock, ublockright))
               | uif_head TELSE uconditional
                    (finish_conditional
                      (uif_head, SOME uconditional,
                       uconditionalright))
  ufuel : THASH TLBRACK TFUEL LPAR EXPRAQ RPAR TRBRACK
              ((#1 EXPRAQ, THASHleft))
  uloop_expr : ufuel TWHILE LPAR uval RPAR ublock
              (UE_While (#1 ufuel, uval, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | ufuel TLOOP ublock
              (UE_Loop (#1 ufuel, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | TFOR upat TIN uval_before_block
              (UE_For
                (upat, #1 uval_before_block,
                 #2 uval_before_block,
                 Position.range_position
                   (TFORleft, #3 uval_before_block)))
             | ufuel TWHILE TLET upat TEQ uval_before_block
              (UE_WhileLet
                (#1 ufuel, upat, #1 uval_before_block,
                 #2 uval_before_block,
                 Position.range_position
                   (#2 ufuel, #3 uval_before_block)))
  (* Comma lists stay nonempty and right-nested (source order preserved). Each list has an explicit terminal
     comma production, so a trailing separator cannot create an empty element. Calls are dedicated
     atom/method productions, so LPAR is never in FOLLOW(uexp) as a general postfix operator -- no
     precedence directive is needed here (D23/D77). *)
  arglist : uclosure_arg
              ([uclosure_arg])
          | uclosure_arg COMMA
              ([uclosure_arg])
          | uclosure_arg COMMA arglist
              (uclosure_arg :: arglist)
  ucallargs : ([])
            | arglist (arglist)
  (* Macro argument lists deliberately do not share call trailing-comma support. The legacy frontend
     accepts empty lists and comma-separated values, but rejects a terminal comma. *)
  umacroargs : uclosure_arg
                 ([uclosure_arg])
             | uclosure_arg COMMA umacroargs
                 (uclosure_arg :: umacroargs)
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
  umatch : umatch_kind umatch_scrutinee
              (UE_Match
                (#1 umatch_kind, #1 umatch_scrutinee,
                 #2 umatch_scrutinee,
                 Position.range_position
                   (#2 umatch_kind, #3 umatch_scrutinee)))
  umatch_scrutinee : uval_before_arms
                       (uval_before_arms)
  uguard : ubody (ubody)
  uarm : upat TARROW uval
            (UR_Arm (upat, NONE, uval))
       | upat TIF uguard TARROW uval
            (UR_Arm (upat, SOME (uguard, TIFleft), uval))
  uarms : uarm                  ([uarm])
        | uarm COMMA            ([uarm])
        | uarm COMMA uarms      (uarm :: uarms)
  (* The single pattern grammar, shared by every binding site above (D28). Its own nonterminals, disjoint
     from `uexp`, so the constructor pattern cannot clash with the call production nor or-`|` with bitwise
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
  (* Expression labels are retained only for markup and future metadata semantics. The active
     frontend erases them and calls the head with source-ordered initializers. Unlike pattern fields,
     this list is nonempty, colon-only, and has no trailing separator. *)
  ustruct_expr : upath TLBRACE ustruct_expr_fields TRBRACE
                   (make_struct_expression
                     (upath, ustruct_expr_fields, TRBRACEright))
  ustruct_expr_field : IDENT TCOLON ubody
                         (SE_Field (IDENT, IDENTleft, ubody))
  ustruct_expr_fields : ustruct_expr_field
                          ([ustruct_expr_field])
                      | ustruct_expr_field COMMA ustruct_expr_fields
                          (ustruct_expr_field :: ustruct_expr_fields)
\<close>

end
