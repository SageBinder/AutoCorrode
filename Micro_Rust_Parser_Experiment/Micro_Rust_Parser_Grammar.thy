theory Micro_Rust_Parser_Grammar
  imports
    Micro_Rust_Parser_AST
    Parser_Utils
    "Isabelle_Lex-Yacc.LexYacc"
begin

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> token reports \<close>

ML\<open>
(* Positioned lexer error for the catch-all rule: an unrecognized character must ABORT with a clickable
   position, not be silently skipped (D21). In Isabelle/ML because `error`/`quote`/`Position.here` are not
   in the lexer's SML environment; SML_imported below. *)
structure URust_Err =
struct
  fun lex_error text pos =
    error ("urust_expr: unexpected input " ^ quote text ^ Position.here pos)

  fun string_error pos =
    error ("urust_expr: malformed or unterminated string literal" ^ Position.here pos)

  fun antiquotation_error kind pos =
    error ("urust_expr: unterminated " ^ kind ^ " antiquotation" ^ Position.here pos)
end
\<close>
SML_import \<open> structure URust_Err = URust_Err \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>  \<comment>\<open> shared lexer position math \<close>

section\<open> Lexer + grammar \<close>

text\<open>
Lexer start states capture value and expression antiquotation bodies without lexing their
HOL content. Yacc directives reproduce the frontend precedence
(\<open>Micro_Rust_Syntax.thy:559-639\<close>). Only token shims remain lexer-local; positions use
\<open>Parser_Lex_Util\<close>.
\<close>
ml_lex_yacc [verbose] "URust" where
lex_user_declarations\<open>
datatype aq_kind = No_AQ | Value_AQ | Expr_AQ
val aq_kind = ref No_AQ
val aq_buf = ref ([] : string list)
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)
val aq_open = ref 0
val aq_depth = ref 0

fun reset_aq () =
  (aq_kind := No_AQ; aq_buf := []; aq_start := 0; aq_open := 0; aq_depth := 0)
fun start_aq kind open_pos body_pos =
  (aq_kind := kind; aq_buf := []; aq_start := body_pos; aq_open := open_pos; aq_depth := 0)
fun push_aq fragment = aq_buf := fragment :: !aq_buf
fun take_aq () =
  let val body = String.concat (rev (!aq_buf))
  in reset_aq (); body end

(* A suffixed integer literal is deliberately NOT interpreted here: the lexer captures the raw lexeme and
   the elaboration term layer reads it against the single suffix table, so an unknown suffix is a
   POSITIONED elaborator error rather than an unpositioned `raise Fail` in lexer code (D29).

   Per-lexer position-map ref + set-shadow; the position MATH is shared (Parser_Lex_Util). tok_ident emits NO
   colour -- ident_term does that once it knows the name's role, so the markup cannot split (D14). *)
val pos_map = ref (Parser_Lex_Util.make_position_map (Input.string ""))
fun set source ctxt =
  (Isabelle_lex_yacc.set source ctxt;
   pos_map := Parser_Lex_Util.make_position_map source;
   reset_aq ())

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!pos_map) yypos
fun tokF args       = Parser_Lex_Util.tokF (!pos_map) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!pos_map) args
fun report_fixed args = Parser_Lex_Util.report_fixed (!pos_map) args
fun tok_ident (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!pos_map) (yypos, yytext)
  in Tokens.IDENT (yytext, p, p) end

fun eof () =
  (case !aq_kind of
     No_AQ => Tokens.EOF (Position.none, Position.none)
   | Value_AQ => URust_Err.antiquotation_error "value" (fixed_pos (!aq_open))
   | Expr_AQ => URust_Err.antiquotation_error "expression" (fixed_pos (!aq_open)))
\<close>
lex_definitions\<open>
%s VAQ EAQ;
digit=[0-9];
hexdigit=[0-9a-fA-F];
idstart=[A-Za-z_];
idchar=[A-Za-z0-9_];
ws = [\ \t\r];
\<close>
lex_rules\<open>
<INITIAL>\n       => (lex());
<INITIAL>{ws}+    => (lex());
<INITIAL>"//"[^\n]* =>
    (report_fixed (yypos, size yytext, Markup.comment1, "line comment"); lex());
<INITIAL>({digit}+|"0x"{hexdigit}+)"_"{idchar}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", Tokens.NUMSFX, yytext));
<INITIAL>({digit}+|"0x"{hexdigit}+) =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>"true"   => (tokF (yypos, yytext, Markup.keyword1, "TTRUE", Tokens.TTRUE));
<INITIAL>"false"  => (tokF (yypos, yytext, Markup.keyword1, "TFALSE", Tokens.TFALSE));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", Tokens.TCONST));
<INITIAL>"return" => (tokF (yypos, yytext, Markup.keyword1, "TRETURN", Tokens.TRETURN));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", Tokens.TELSE));
<INITIAL>"unsafe" => (tokF (yypos, yytext, Markup.keyword1, "TUNSAFE", Tokens.TUNSAFE));
<INITIAL>"match"        => (tokF (yypos, yytext, Markup.keyword1, "TMATCH", Tokens.TMATCH));
<INITIAL>"match_switch" => (tokF (yypos, yytext, Markup.keyword1, "TMATCHSWITCH", Tokens.TMATCHSWITCH));
<INITIAL>"match_case"   => (tokF (yypos, yytext, Markup.keyword1, "TMATCHCASE", Tokens.TMATCHCASE));
<INITIAL>"mut"    => (tokF (yypos, yytext, Markup.keyword1, "TMUT", Tokens.TMUT));
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
<INITIAL>"\""     => (URust_Err.string_error (fixed_pos yypos));
<INITIAL>{idstart}{idchar}* => (tok_ident (yypos, yytext));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "LPAR", Tokens.LPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "RPAR", Tokens.RPAR));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "COMMA", Tokens.COMMA));
<INITIAL>"."      => (tokF (yypos, yytext, Markup.delimiter, "TDOT", Tokens.TDOT));
<INITIAL>":"      => (tokF (yypos, yytext, Markup.delimiter, "TCOLON", Tokens.TCOLON));
<INITIAL>"@"      => (tokF (yypos, yytext, Markup.operator, "TAT", Tokens.TAT));
<INITIAL>"["      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACK", Tokens.TLBRACK));
<INITIAL>"]"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACK", Tokens.TRBRACK));
<INITIAL>"{"      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACE", Tokens.TLBRACE));
<INITIAL>"}"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACE", Tokens.TRBRACE));
<INITIAL>\\"<llangle>"          => (report_fixed (yypos, 1, Markup.delimiter, "VALAQ"); start_aq Value_AQ yypos (yypos + size yytext); YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (report_fixed (yypos, 1, Markup.literal, "EXPRAQ"); start_aq Expr_AQ yypos (yypos + size yytext); YYBEGIN EAQ; lex());
<INITIAL>\\"<Rightarrow>" => (report_fixed (yypos, 1, Markup.delimiter, "TARROW");
    Tokens.TARROW (fixed_pos yypos, fixed_pos (yypos + size yytext)));
<INITIAL>.        => (URust_Err.lex_error yytext (fixed_pos yypos));
<VAQ>\\"<llangle>" => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<VAQ>\\"<rrangle>" =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_fixed (yypos, 1, Markup.delimiter, "VALAQ");
       let val p = fixed_pos (!aq_start) val q = fixed_pos yypos val body = take_aq ()
       in Tokens.VALAQ (Input.source true body (Position.range (p, q)), p, q) end));
<VAQ>\n           => (push_aq "\n"; lex());
<VAQ>.            => (push_aq yytext; lex());
<EAQ>\\"<open>"    => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<EAQ>\\"<close>"   =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_fixed (yypos, 1, Markup.delimiter, "EXPRAQ");
       let val p = fixed_pos (!aq_start) val q = fixed_pos yypos val body = take_aq ()
       in Tokens.EXPRAQ (Input.source true body (Position.range (p, q)), p, q) end));
<EAQ>\n           => (push_aq "\n"; lex());
<EAQ>.            => (push_aq yytext; lex());
\<close>
and yacc_user_declarations\<open>
open URust_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

(* Operator precedence, loosest -> tightest (the frontend's infix priorities). Return is below
   with-block expressions, so `return { e }` takes the block as its operand instead of becoming an
   operandless return followed by a block statement. Comparisons are non-associative (Rust rejects
   `a == b == c`). Reference prefixes and `!` use structural tiers below; these directives keep the
   ambiguous `uexp OP uexp` productions conflict-free. *)
%right TRETURN
%right TIF TLBRACE TUNSAFE
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
%nonassoc TDOTDOT TDOTDOTEQ

%term NUM of string | NUMSFX of string | STRING of string | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TTRUE | TFALSE | TLET | TCONST | TRETURN | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE | TLBRACK | TRBRACK | COMMA | TDOT | TCOLON | TAT
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TPLUSEQ | TMINUSEQ | TSTAREQ | TPERCENTEQ
    | TAMPEQ | TBAREQ | TCARETEQ | TSHLEQ | TSHREQ
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG | TQUESTION
    | TUNSAFE | TMATCH | TMATCHSWITCH | TMATCHCASE | TARROW
    | TDOTDOT | TDOTDOTEQ | TMUT | TPATCONTEXT
%nonterm ustart of URust_AST.ur_expr option
       | ustmt of URust_AST.ur_expr
       | uval of URust_AST.ur_expr
       | uassign of URust_AST.ur_expr
       | uassignop of URust_AST.assignop * Position.T
       | uexp of URust_AST.ur_expr
       | urefprefix of URust_AST.ur_expr
       | unotprefix of URust_AST.ur_expr
       | upostfix of URust_AST.ur_expr
       | uatom of URust_AST.ur_expr
       | arglist of URust_AST.ur_expr list
       | ucallargs of URust_AST.ur_expr list
       | ublock of URust_AST.ur_expr
       | uunsafe of URust_AST.ur_expr
       | uif of URust_AST.ur_expr
       | umatch of URust_AST.ur_expr
       | umatchsw of URust_AST.ur_expr
       | umatchcase of URust_AST.ur_expr
       | uguard of URust_AST.ur_expr
       | uarms of URust_AST.ur_arm list
       | upat of URust_AST.ur_pat
       | upat_range of URust_AST.ur_pat
       | upat_alias of URust_AST.ur_pat
       | upat_prefix of URust_AST.ur_pat
       | upat_atom of URust_AST.ur_pat
       | upat_ident of URust_AST.pat_ident
       | upats of URust_AST.ur_pat list
       | uslice_item of URust_AST.slice_item
       | uslice_items of URust_AST.slice_item list
       | ustruct_field of URust_AST.struct_field
       | ustruct_fields of URust_AST.struct_field list
\<close>
yacc_rules\<open>
  ustart : ustmt (SOME ustmt)
         | (NONE)
  (* Statements: a value expression `uval` sequenced with `;`, OR a block-like form in
     statement position with NO trailing `;` (Rust's optional semicolon after a block-like expr; closes
     divergence D-2 -- D25). Both desugar to the same `sequence`. The `ublock`-as-operand vs `ublock
     ustmt` decision resolves by lookahead (operator/`;`/`}`/EOF -> operand; statement-start -> sequence). *)
  ustmt : uval                              (uval)
        | uval TSEMI ustmt                  (UE_Seq (uval, ustmt))
        | uval TSEMI                        (finish_statement (uval, TSEMIleft))
        | ublock ustmt                      (UE_Seq (ublock, ustmt))
        | uunsafe ustmt                     (UE_Seq (uunsafe, ustmt))
        | uif ustmt                         (UE_Seq (uif, ustmt))
        | umatch ustmt                      (UE_Seq (umatch, ustmt))
        (* NO `umatchsw ustmt` / `umatchcase ustmt` forms: only the bare `match` keyword has the
           frontend's no-`;` sequencing production. The explicit forms still need a trailing `;`. *)
        (* The binder is the SHARED `upat`, not an inline IDENT, so `let (a, b) = ..` / `let mut x` become
           pattern-datatype extensions rather than new productions per site; bind_pat gates refutable
           patterns with a positioned error (D28). *)
        | TLET upat TEQ uval TSEMI ustmt   (UE_Let (upat, uval, ustmt))
        | TLET TMUT upat TEQ uval TSEMI ustmt
            (UE_LetMut (upat, uval, ustmt, TMUTleft))
        | TCONST upat TEQ uval TSEMI ustmt (UE_Const (upat, uval, ustmt))
  (* Value position: an operand OR a with-block control-flow expr. `uval` is where `if`/`match` (later
     loops) are admitted -- let-RHS, condition, call args, parens -- WITHOUT being a bare binary-operator
     operand (that stays `uexp`, closing divergence D-1 -- D25). *)
  uval : uassign (uassign)
       | TRETURN (UE_Return (NONE, TRETURNleft))
       | TRETURN uval (UE_Return (SOME uval, TRETURNleft))
       | uif %prec TIF (uif)
       | umatch %prec TIF (umatch)
       | umatchsw (umatchsw)
       | umatchcase (umatchcase)
  (* Assignment is below every pure operator and recurses through its own tier on the right. Blocks
     remain ordinary expression atoms, while lower-priority `if`/`match` forms require parentheses on
     the RHS, matching the frontend's priority-40 boundary. The LHS crosses expr_to_place exactly once. *)
  uassign : uexp (uexp)
          | uexp uassignop uassign (mk_assign uassignop uexp uassign)
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
  (* Postfixes form a structural tier above atoms, so `?`, field access, and methods compose
     left-to-right and bind tighter than prefix/binary operators. A dotted identifier followed by
     parentheses is a method; without parentheses it is an NField lens access. *)
  upostfix : uatom (uatom)
           | upostfix TQUESTION
               (UE_Unary (U_Propagate, upostfix, TQUESTIONleft))
           | upostfix TDOT IDENT
               (UE_Field (upostfix, IDENT, IDENTleft))
           | upostfix TDOT IDENT LPAR ucallargs RPAR
               (mk_method_call
                  (upostfix, IDENT, IDENTleft, ucallargs, upostfixleft, RPARright))
  uatom : NUM        (UE_Literal (LP_Integer (NUM, NUMleft)))
        | NUMSFX     (UE_Literal (LP_Integer (NUMSFX, NUMSFXleft)))
        | TTRUE      (UE_Literal (LP_Bool (true, TTRUEleft)))
        | TFALSE     (UE_Literal (LP_Bool (false, TFALSEleft)))
        | STRING     (UE_Literal (LP_String (STRING, STRINGleft)))
        | IDENT      (UE_Ident (IDENT, IDENTleft))
        | IDENT LPAR ucallargs RPAR
            (mk_call (IDENT, IDENTleft, ucallargs, IDENTleft, RPARright))
        | LPAR RPAR  (UE_Unit LPARleft)
        | LPAR uval COMMA arglist RPAR
            (UE_Tuple (uval :: arglist, Position.range_position (LPARleft, RPARright)))
        | LPAR uval RPAR
            (UE_Group (uval, Position.range_position (LPARleft, RPARright)))
        | VALAQ      (UE_Literal (LP_ValAntiq VALAQ))
        | EXPRAQ     (UE_ExprAntiq EXPRAQ)
        | ublock %prec TIF (ublock)  (* block STAYS an operand atom (frontend priority 1000): `{e} + x`
                                        parses. Equal right precedence makes a following `if` shift into
                                        semicolon-free statement sequencing without a conflict. *)
        | uunsafe %prec TIF (uunsafe)
  (* Reference prefixes bind tighter than every binary operator and looser than `!`, matching the
     frontend priorities. Recursing through this tier makes `**x` two ordinary dereference nodes while
     preserving the binary meanings of `*` and `&`; mixed and deeper recursion is a documented
     accepted-surface improvement over the frontend's fixed prefix productions. *)
  unotprefix : upostfix (upostfix)
             | TBANG unotprefix (UE_Unary (U_Not, unotprefix, TBANGleft))
  urefprefix : unotprefix (unotprefix)
             | TAMP urefprefix
                 (UE_Unary (U_Borrow BM_Imm, urefprefix, TAMPleft))
             | TAMP TMUT urefprefix
                 (UE_Unary (U_Borrow BM_Mut, urefprefix, TAMPleft))
             | TSTAR urefprefix
                 (UE_Unary (U_Deref, urefprefix, TSTARleft))
  uexp : urefprefix (urefprefix)
       (* `uif` is deliberately NOT a `uexp` alternative (closes D-1): it reaches value position via `uval`
          and operand position only when parenthesized. Loops will join `uval` the same way. *)
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
  (* No dangling-else conflict: the branches are BRACE-DELIMITED, so TELSE is not in FOLLOW(uif) and the
     parser shifts it unambiguously. The whole grammar is verified conflict-free via the [verbose] grm.desc
     export -- RE-CHECK IT after any grammar change. *)
  ublock : TLBRACE ustmt TRBRACE            (UE_Block (ustmt, TLBRACEleft))
         | TLBRACE TRBRACE                  (UE_Block (UE_Unit TLBRACEleft, TLBRACEleft))
  (* Unsafe is block-like in operand and statement positions, but deliberately remains distinct from
     `ublock`: branch delimiters still require ordinary braces. Its frontend semantics are block erasure. *)
  uunsafe : TUNSAFE ublock                  (ublock)
  (* Condition is `uval` (the frontend's condition priority admits an `if`), so `if if c {..} {..}` parses. *)
  uif : TIF uval ublock                     (UE_If (uval, ublock, NONE, TIFleft))
      | TIF uval ublock TELSE ublock        (UE_If (uval, ublock1, SOME ublock2, TIFleft))
      | TIF uval ublock TELSE uif           (UE_If (uval, ublock, SOME uif, TIFleft))
  (* Comma lists stay nonempty and right-nested (source order preserved). Each list has an explicit terminal
     comma production, so a trailing separator cannot create an empty element. Call productions are
     IDENTIFIER-headed, so LPAR is never in FOLLOW(uexp) as a postfix operator -- no precedence directive
     is needed here (D23). *)
  arglist : uval               ([uval])
          | uval COMMA         ([uval])
          | uval COMMA arglist (uval :: arglist)
  ucallargs : ([])
            | arglist (arglist)
  (* A tuple has one element before the comma and a nonempty `arglist` after it. Even when `arglist` has a
     terminal comma, this requires at least two elements and keeps `(x,)` outside the grammar. *)
  (* All three `match` keywords are with-block forms, so they join `uval`, not `uexp`. They share ONE arms
     nonterminal over the unified pattern language and differ only in the flavour tag; the lowering split
     and the per-flavour pattern gate live in the elaborator (D28/D32). *)
  umatch     : TMATCH uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Auto, uval, uarms, Position.range_position (TMATCHleft, TRBRACEright)))
  umatchsw   : TMATCHSWITCH uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Switch, uval, uarms, Position.range_position (TMATCHSWITCHleft, TRBRACEright)))
  umatchcase : TMATCHCASE uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Case, uval, uarms, Position.range_position (TMATCHCASEleft, TRBRACEright)))
  uguard : uassign (uassign)
         | uif (uif)
         | umatch (umatch)
         | umatchsw (umatchsw)
         | umatchcase (umatchcase)
  uarms : upat TARROW uval
             ([UR_Arm (upat, NONE, uval)])
        | upat TARROW uval COMMA
             ([UR_Arm (upat, NONE, uval)])
        | upat TARROW uval COMMA uarms
             (UR_Arm (upat, NONE, uval) :: uarms)
        | upat TIF uguard TARROW uval
             ([UR_Arm (upat, SOME (uguard, TIFleft), uval)])
        | upat TIF uguard TARROW uval COMMA
             ([UR_Arm (upat, SOME (uguard, TIFleft), uval)])
        | upat TIF uguard TARROW uval COMMA uarms
             (UR_Arm (upat, SOME (uguard, TIFleft), uval) :: uarms)
  (* The single pattern grammar, shared by every binding site above (D28). Its own nonterminals, disjoint
     from `uexp`, so the constructor pattern cannot clash with the call production nor or-`|` with bitwise
     or. It deliberately ACCEPTS more than any one site can lower (a numeral in `let`, a constructor under
     `match_switch`); each site's elaborator rejects the rest WITH A POSITION, which beats a bare "syntax
     error" and keeps one grammar for one language. *)
  (* Pattern precedence is explicit rather than yacc-directed. A chained range is retained long enough
     for a positioned non-associativity diagnostic; disjunctions flatten in source order. *)
  upat : upat_range               (upat_range)
        | upat TBAR upat_range
            (mk_or_pat (upat, upat_range, TBARleft))
  upat_range : upat_alias         (upat_alias)
              | upat_range TDOTDOT upat_alias
                  (P_Range (RK_Exclusive, upat_range, upat_alias, TDOTDOTleft))
              | upat_range TDOTDOTEQ upat_alias
                  (P_Range (RK_Inclusive, upat_range, upat_alias, TDOTDOTEQleft))
  upat_alias : upat_prefix        (upat_prefix)
  upat_prefix : upat_atom         (upat_atom)
               | TAMP upat_prefix
                   (P_Borrow (BM_Imm, upat_prefix, TAMPleft))
               | TAMP TMUT upat_prefix
                   (P_Borrow (BM_Mut, upat_prefix, TAMPleft))
  upat_atom : upat_ident          (mk_bare_ident_pat upat_ident)   (* `_` normalises to P_Wild *)
             | NUM                (P_Literal (LP_Integer (NUM, NUMleft)))
             | TTRUE              (P_Literal (LP_Bool (true, TTRUEleft)))
             | TFALSE             (P_Literal (LP_Bool (false, TFALSEleft)))
             | STRING             (P_Literal (LP_String (STRING, STRINGleft)))
             | VALAQ              (P_Literal (LP_ValAntiq VALAQ))
             | upat_ident LPAR upats RPAR
                 (mk_ctor_pat (upat_ident, upats))
             | upat_ident TAT upat_alias
                 (mk_alias_pat (upat_ident, upat_alias, TATleft))
             | LPAR upat RPAR
                 (P_Group upat)
             | LPAR upat COMMA upats RPAR
                 (P_Tuple (upat :: upats, Position.range_position (LPARleft, RPARright)))
             | TLBRACK TRBRACK
                 (P_Slice ([], Position.range_position (TLBRACKleft, TRBRACKright)))
             | TLBRACK uslice_items TRBRACK
                 (P_Slice (uslice_items, Position.range_position (TLBRACKleft, TRBRACKright)))
             | upat_ident TLBRACE ustruct_fields TRBRACE
                 (mk_struct_pat (upat_ident, ustruct_fields))
  upat_ident : IDENT              (PI (IDENT, IDENTleft))
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
\<close>

end
