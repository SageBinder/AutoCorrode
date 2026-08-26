(* The custom uRust parser (Phase 1, in progress).

   An ml_lex_yacc lexer + LALR grammar -> reified SML AST -> elaboration into the EXISTING shallow terms,
   exposed as an outer-syntax command `urust_expr NAME <src>`. The governing invariant: the elaborated
   term is ALPHA-EQUAL to what the inner-syntax bracket `\<lbrakk> src \<rbrakk>` produces today -- validated
   by Micro_Rust_Parser_Conformance.thy (each row closes `unfolding NAME_def by (rule refl)`), with the
   accept-set boundary build-guarded in Micro_Rust_Parser_Negative_Conformance.thy.

   Notes (do not duplicate them here): coverage + deferred work = notes/agent-notes/urust-parser-features.md
   and urust-parser-plan.md; the surface BNF, the AST table, and the per-decision rationale (`D*`) =
   urust-parser-design-decisions.md; cross-cutting rules (markup classes C1, divergences C2) =
   urust-rules-and-conventions.md. Comments below are limited to what a future editor would otherwise
   BREAK; the `D*` tags point at the full story.

   Shared with Toy_Lex_Yacc (and a future C frontend) via Parser_Utils: the corrected symbol-position
   layer, binder/markup/antiquotation helpers, the command mutex. ASCII escape form throughout
   (isabelle build rejects raw UTF-8 cartouche delimiters). *)

theory Micro_Rust_Parser
  imports
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
    "Isabelle_Lex-Yacc.LexYacc"
    Parser_Utils
  keywords
    "urust_expr" :: thy_decl
begin

section\<open> Reified AST \<close>

text\<open> One constructor per uRust surface form. Positions are carried for markup/diagnostics. \<close>
ML\<open>
structure URust_AST =
struct
  (* THE pattern language: ONE datatype for EVERY binding site (let / const binder, match_switch key,
     match_case arm, and later closure params, `for` patterns, fn parameters) -- Rust has one pattern
     grammar, whose sites differ only in which patterns are LEGAL there, so each site's elaborator gates
     what it accepts with a positioned error instead of the grammar forking (D28). A bare id's ROLE
     (nullary ctor vs variable binder) needs `Code.is_constr`, invisible to the parser -- hence one
     `P_Ident`. Adding a pattern form = ONE constructor here + one clause per consuming site. *)
  datatype ur_pat =
      P_Wild   of Position.T                          (* _ *)
    | P_Ident  of string * Position.T                 (* bare id: nullary ctor OR variable binder *)
    | P_Lit    of int * Position.T                    (* numeral pattern (a match_switch key) *)
    | P_Constr of string * Position.T * ur_pat list   (* C(args): name, name-pos, args *)
    | P_Or     of ur_pat list * Position.T            (* p | q | r  (flattened; source order) *)

  (* Which `match` surface keyword an arm set came from; the two lower DIFFERENTLY (see UE_Match), so the
     flavour is a tag rather than separate AST nodes -- the bare `match` keyword then becomes a third
     flavour that CLASSIFIES its arms into one of these two lowerings (D28/D32). *)
  datatype match_flavour = MF_Switch | MF_Case | MF_Auto

  (* `_` lexes as an ordinary IDENT: normalise to P_Wild in ONE place, not an `= "_"` test at every site. *)
  fun mk_ident_pat (s, pos) = if s = "_" then P_Wild pos else P_Ident (s, pos)

  (* Flatten nested or-patterns so `a | b | c` is one P_Or in source order, whatever %left TBAR bracketed. *)
  fun mk_or_pat (p, q, pos) =
    let fun alts (P_Or (ps, _)) = ps | alts p = [p]
    in P_Or (alts p @ alts q, pos) end

  (* Pure-value operators. Data-driven: each maps to one HOL const via URust_Translate.binop_const /
     unop_const, so adding an operator is one datatype line + one table row (D20). *)
  datatype binop =
      Add | Sub | Mul | Div | Mod              (* + - * / %       *)
    | Shl | Shr                                (* << >>           *)
    | BAnd | BOr | BXor                        (* & | ^  (infix)  *)
    | Eq | Ne | Lt | Le | Gt | Ge              (* == != < <= > >= *)
    | And | Or                                 (* && ||           *)
  datatype unop = Not                          (* !  (and !! = !(!_)) *)

  datatype ur_expr =
      UE_Num       of int * Position.T                (* bare decimal: 0, 1, 42 *)
    | UE_NumSfx    of string * Position.T             (* RAW lexeme of a suffixed int (1_u32 / 0x4_u8);
                                                         split + typed by parse_int_lit -- ALL suffix
                                                         knowledge sits in that one table (D29) *)
    | UE_Unit      of Position.T                      (* () *)
    | UE_Ident     of string * Position.T             (* bare identifier at value position *)
    | UE_ValAntiq  of Input.source                    (* <<v>>  body as a POSITIONED source -> literal v *)
    | UE_ExprAntiq of Input.source                    (* eps<e> body as a POSITIONED source -> e *)
    | UE_Let       of ur_pat * ur_expr * ur_expr      (* let <pat> = rhs; body -> bind *)
    | UE_Const     of ur_pat * ur_expr * ur_expr      (* const: same desugaring as let today; distinct node
                                                         keeps the keyword for when it diverges (B7) *)
    | UE_Seq       of ur_expr * ur_expr               (* e1; e2 -> sequence (trailing `;`: e2 = unit) *)
    | UE_Bin       of binop * ur_expr * ur_expr * Position.T   (* a <binop> b *)
    | UE_Un        of unop * ur_expr * Position.T              (* !a  (and !!a = !(!a)) *)
    | UE_Block     of ur_expr * Position.T            (* { stmts } -- ERASES to <stmts>, no `scoped`
                                                         wrapper: `_urust_scoping` is identity (D22) *)
    | UE_If        of ur_expr * ur_expr * ur_expr option * Position.T
                                                      (* NONE else-branch = one-armed -> skip (D22) *)
    | UE_Call      of string * Position.T * ur_expr list * Position.T
                                                      (* f(a0..aN) -> funcallN. Callee is an IDENTIFIER
                                                         (name, name-pos) resolved in NFunction context;
                                                         then args and the SPAN of the whole call, so an
                                                         arity error underlines the call, not just the name
                                                         (D23/D29). Non-identifier callees (antiquotation,
                                                         turbofish, path) are deferred -- D-5. *)
    | UE_Match     of match_flavour * ur_expr * (ur_pat * ur_expr) list * Position.T
                                                      (* match_<flavour> scrut { pat => body, .. }. ONE node
                                                         for both keywords; only the LOWERING differs --
                                                         MF_Switch -> ncase_selector (first-order, D26),
                                                         MF_Case -> the Ctr_Sugar case skeleton (D27). Each
                                                         flavour's elaborator gates the patterns it cannot
                                                         lower with a positioned error. *)
end
\<close>

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> typing / sorting \<close>

ML\<open>
(* Positioned lexer error for the catch-all rule: an unrecognized character must ABORT with a clickable
   position, not be silently skipped (D21). In Isabelle/ML because `error`/`quote`/`Position.here` are not
   in the lexer's SML environment; SML_imported below. *)
structure URust_Err =
struct
  fun lex_error text pos =
    error ("urust_expr: unexpected input " ^ quote text ^ Position.here pos)
end
\<close>
SML_import \<open> structure URust_Err = URust_Err \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>  \<comment>\<open> shared lexer position math \<close>

section\<open> Lexer + grammar \<close>

text\<open> The antiquotation brackets are the Isabelle symbols \<open>\<llangle>\<close>/\<open>\<rrangle>\<close> (value
escape) and \<open>\<epsilon>\<close> + \<open>\<open>\<close>/\<open>\<close>\<close> (expression escape); each has an explicit
escape rule and captures its body with a start state, without lexing the HOL inside. Operator precedence
is declared once with yacc directives, reproducing the frontend's infix priorities
(\<open>Micro_Rust_Syntax.thy:559-603\<close>). The \<open>the_src\<close>/\<open>tokF\<close>/\<open>tok_ident\<close> shims below must stay HERE (not in
\<open>Parser_Utils\<close>): they run in this \<open>ml_lex_yacc\<close> block's SML environment and each lexer's \<open>Tokens\<close>
constructors differ; only the position MATH is shared (D19). \<close>
ml_lex_yacc [verbose] "URust" where
lex_user_declarations\<open>
val aq_buf = ref ""
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)

(* A suffixed integer literal is deliberately NOT interpreted here: the lexer captures the raw lexeme and
   URust_Translate.parse_int_lit reads it against the single int_suffix_typ table, so an unknown suffix is
   a POSITIONED elaborator error rather than an unpositioned `raise Fail` in lexer code (D29).

   Per-lexer source ref + set-shadow; the position MATH is shared (Parser_Lex_Util). tok_ident emits NO
   colour -- ident_term does that once it knows the name's role, so the markup cannot split (D14). *)
val the_src = ref (Input.string "")
fun set source ctxt = (Isabelle_lex_yacc.set source ctxt; the_src := source)

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!the_src) yypos
fun tokF args       = Parser_Lex_Util.tokF (!the_src) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!the_src) args
fun report_fixed args  = Parser_Lex_Util.report_fixed (!the_src) args
fun tok_ident (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!the_src) (yypos, yytext)
  in Tokens.IDENT (yytext, p, p) end
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
<INITIAL>({digit}+|"0x"{hexdigit}+)"_"{idchar}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", "", Tokens.NUMSFX, yytext));
<INITIAL>{digit}+ => (tok_valF (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", "", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", "", Tokens.TCONST));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", "", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", "", Tokens.TELSE));
<INITIAL>"match"        => (tokF (yypos, yytext, Markup.keyword1, "TMATCH", "", Tokens.TMATCH));
<INITIAL>"match_switch" => (tokF (yypos, yytext, Markup.keyword1, "TMATCHSWITCH", "", Tokens.TMATCHSWITCH));
<INITIAL>"match_case"   => (tokF (yypos, yytext, Markup.keyword1, "TMATCHCASE", "", Tokens.TMATCHCASE));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.delimiter, "TEQ", "", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", "", Tokens.TSEMI));
<INITIAL>"<<"     => (tokF (yypos, yytext, Markup.operator, "TSHL", "", Tokens.TSHL));
<INITIAL>">>"     => (tokF (yypos, yytext, Markup.operator, "TSHR", "", Tokens.TSHR));
<INITIAL>"<="     => (tokF (yypos, yytext, Markup.operator, "TLE", "", Tokens.TLE));
<INITIAL>">="     => (tokF (yypos, yytext, Markup.operator, "TGE", "", Tokens.TGE));
<INITIAL>"=="     => (tokF (yypos, yytext, Markup.operator, "TEQEQ", "", Tokens.TEQEQ));
<INITIAL>"!="     => (tokF (yypos, yytext, Markup.operator, "TNE", "", Tokens.TNE));
<INITIAL>"&&"     => (tokF (yypos, yytext, Markup.operator, "TAMPAMP", "", Tokens.TAMPAMP));
<INITIAL>"||"     => (tokF (yypos, yytext, Markup.operator, "TBARBAR", "", Tokens.TBARBAR));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.operator, "TPLUS", "", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.operator, "TMINUS", "", Tokens.TMINUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.operator, "TSTAR", "", Tokens.TSTAR));
<INITIAL>"/"      => (tokF (yypos, yytext, Markup.operator, "TSLASH", "", Tokens.TSLASH));
<INITIAL>"%"      => (tokF (yypos, yytext, Markup.operator, "TPERCENT", "", Tokens.TPERCENT));
<INITIAL>"<"      => (tokF (yypos, yytext, Markup.operator, "TLT", "", Tokens.TLT));
<INITIAL>">"      => (tokF (yypos, yytext, Markup.operator, "TGT", "", Tokens.TGT));
<INITIAL>"&"      => (tokF (yypos, yytext, Markup.operator, "TAMP", "", Tokens.TAMP));
<INITIAL>"|"      => (tokF (yypos, yytext, Markup.operator, "TBAR", "", Tokens.TBAR));
<INITIAL>"^"      => (tokF (yypos, yytext, Markup.operator, "TCARET", "", Tokens.TCARET));
<INITIAL>"!"      => (tokF (yypos, yytext, Markup.operator, "TBANG", "", Tokens.TBANG));
<INITIAL>{idstart}{idchar}* => (tok_ident (yypos, yytext));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "LPAR", "", Tokens.LPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "RPAR", "", Tokens.RPAR));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "COMMA", "", Tokens.COMMA));
<INITIAL>"."      => (tokF (yypos, yytext, Markup.delimiter, "TDOT", "", Tokens.TDOT));
<INITIAL>"{"      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACE", "", Tokens.TLBRACE));
<INITIAL>"}"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACE", "", Tokens.TRBRACE));
<INITIAL>\\"<llangle>"          => (report_fixed (yypos, 1, Markup.delimiter, "VALAQ", ""); aq_buf := ""; aq_start := yypos + size yytext; YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (report_fixed (yypos, 1, Markup.literal, "EXPRAQ", ""); aq_buf := ""; aq_start := yypos + size yytext; YYBEGIN EAQ; lex());
<INITIAL>\\"<Rightarrow>" => (report_fixed (yypos, 1, Markup.delimiter, "TARROW", "");
    Tokens.TARROW (fixed_pos yypos, fixed_pos (yypos + size yytext)));
<INITIAL>.        => (URust_Err.lex_error yytext (fixed_pos yypos));
<VAQ>\\"<rrangle>" => (YYBEGIN INITIAL; report_fixed (yypos, 1, Markup.delimiter, "VALAQ", "");
    let val p = fixed_pos (!aq_start) val q = fixed_pos yypos
    in Tokens.VALAQ (Input.source true (!aq_buf) (Position.range (p, q)), p, q) end);
<VAQ>\n           => (aq_buf := !aq_buf ^ "\n"; lex());
<VAQ>.            => (aq_buf := !aq_buf ^ yytext; lex());
<EAQ>\\"<close>"   => (YYBEGIN INITIAL; report_fixed (yypos, 1, Markup.delimiter, "EXPRAQ", "");
    let val p = fixed_pos (!aq_start) val q = fixed_pos yypos
    in Tokens.EXPRAQ (Input.source true (!aq_buf) (Position.range (p, q)), p, q) end);
<EAQ>\n           => (aq_buf := !aq_buf ^ "\n"; lex());
<EAQ>.            => (aq_buf := !aq_buf ^ yytext; lex());
\<close>
and yacc_user_declarations\<open>
open URust_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

(* Operator precedence, loosest -> tightest (the frontend's infix priorities). Comparisons are
   non-associative (Rust rejects `a == b == c`); prefix `!` binds tighter than every binary operator.
   These directives are what keep the ambiguous `uexp OP uexp` productions conflict-free. *)
%left TBARBAR
%left TAMPAMP
%nonassoc TEQEQ TNE TLT TLE TGT TGE
%left TBAR
%left TCARET
%left TAMP
%left TSHL TSHR
%left TPLUS TMINUS
%left TSTAR TSLASH TPERCENT
%right TBANG
%left TDOT    (* method `.` binds tightest, tighter than prefix `!`: `a + b.m(c)` = `a + (b.m(c))`,
                 `!x.m()` = `!(x.m())`. This is what resolves `uexp . TDOT` against the operators. *)

%term NUM of int | NUMSFX of string | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TLET | TCONST | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE | COMMA | TDOT
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG
    | TMATCH | TMATCHSWITCH | TMATCHCASE | TARROW
%nonterm ustart of URust_AST.ur_expr option
       | ustmt of URust_AST.ur_expr
       | uval of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
       | arglist of URust_AST.ur_expr list
       | ublock of URust_AST.ur_expr
       | uif of URust_AST.ur_expr
       | umatch of URust_AST.ur_expr
       | umatchsw of URust_AST.ur_expr
       | umatchcase of URust_AST.ur_expr
       | uarms of (URust_AST.ur_pat * URust_AST.ur_expr) list
       | upat of URust_AST.ur_pat
       | upats of URust_AST.ur_pat list
\<close>
yacc_rules\<open>
  ustart : ustmt (SOME ustmt)
         | (NONE)
  (* Statements: a value expression `uval` sequenced with `;`, OR a with-block form (`ublock`/`uif`) in
     statement position with NO trailing `;` (Rust's optional semicolon after a block-like expr; closes
     divergence D-2 -- D25). Both desugar to the same `sequence`. The `ublock`-as-operand vs `ublock
     ustmt` decision resolves by lookahead (operator/`;`/`}`/EOF -> operand; statement-start -> sequence). *)
  ustmt : uval                              (uval)
        | uval TSEMI ustmt                  (UE_Seq (uval, ustmt))
        | uval TSEMI                        (UE_Seq (uval, UE_Unit TSEMIleft))
        | ublock ustmt                      (UE_Seq (ublock, ustmt))
        | uif ustmt                         (UE_Seq (uif, ustmt))
        | umatch ustmt                      (UE_Seq (umatch, ustmt))
        (* NO `umatchsw ustmt` / `umatchcase ustmt` forms: only the bare `match` keyword has the
           frontend's no-`;` sequencing production. The explicit forms still need a trailing `;`. *)
        (* The binder is the SHARED `upat`, not an inline IDENT, so `let (a, b) = ..` / `let mut x` become
           pattern-datatype extensions rather than new productions per site; bind_pat gates refutable
           patterns with a positioned error (D28). *)
        | TLET upat TEQ uval TSEMI ustmt   (UE_Let (upat, uval, ustmt))
        | TCONST upat TEQ uval TSEMI ustmt (UE_Const (upat, uval, ustmt))
  (* Value position: an operand OR a with-block control-flow expr. `uval` is where `if`/`match` (later
     loops) are admitted -- let-RHS, condition, call args, parens -- WITHOUT being a bare binary-operator
     operand (that stays `uexp`, closing divergence D-1 -- D25). *)
  uval : uexp (uexp)
       | uif  (uif)
       | umatch (umatch)
       | umatchsw (umatchsw)
       | umatchcase (umatchcase)
  uexp : NUM        (UE_Num (NUM, NUMleft))
       | NUMSFX     (UE_NumSfx (NUMSFX, NUMSFXleft))
       | IDENT      (UE_Ident (IDENT, IDENTleft))
       | IDENT LPAR RPAR          (UE_Call (IDENT, IDENTleft, [],
                                     Position.range_position (IDENTleft, RPARright)))
       | IDENT LPAR arglist RPAR  (UE_Call (IDENT, IDENTleft, arglist,
                                     Position.range_position (IDENTleft, RPARright)))
       (* Method call `recv.m(args)` = a plain call to `m` with the RECEIVER PREPENDED as first arg, so it
          reuses UE_Call with no new machinery (D24). Postfix on any `uexp` receiver, so `g(c).f(b)` and
          chains work. Field access `x.f` (no parens) is a different construct (NField/lens) -- deferred. *)
       | uexp TDOT IDENT LPAR RPAR         (UE_Call (IDENT, IDENTleft, [uexp],
                                              Position.range_position (uexpleft, RPARright)))
       | uexp TDOT IDENT LPAR arglist RPAR (UE_Call (IDENT, IDENTleft, uexp :: arglist,
                                              Position.range_position (uexpleft, RPARright)))
       | LPAR RPAR  (UE_Unit LPARleft)
       | LPAR uval RPAR (uval)      (* parens wrap a uval: `(if ...)` becomes a usable operand -- the D-1 escape *)
       | VALAQ      (UE_ValAntiq VALAQ)
       | EXPRAQ     (UE_ExprAntiq EXPRAQ)
       | ublock     (ublock)        (* block STAYS an operand atom (frontend priority 1000): `{e} + x` parses *)
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
       | TBANG uexp          (UE_Un (Not, uexp, TBANGleft))
  (* No dangling-else conflict: the branches are BRACE-DELIMITED, so TELSE is not in FOLLOW(uif) and the
     parser shifts it unambiguously. The whole grammar is verified conflict-free via the [verbose] grm.desc
     export -- RE-CHECK IT after any grammar change. *)
  ublock : TLBRACE ustmt TRBRACE            (UE_Block (ustmt, TLBRACEleft))
  (* Condition is `uval` (the frontend's condition priority admits an `if`), so `if if c {..} {..}` parses. *)
  uif : TIF uval ublock                     (UE_If (uval, ublock, NONE, TIFleft))
      | TIF uval ublock TELSE ublock        (UE_If (uval, ublock1, SOME ublock2, TIFleft))
      | TIF uval ublock TELSE uif           (UE_If (uval, ublock, SOME uif, TIFleft))
  (* Call arguments, right-nested (source order preserved). Conflict-free because the call productions are
     IDENTIFIER-headed, so LPAR is never in FOLLOW(uexp) as a postfix operator -- no precedence directive
     needed here (D23). *)
  arglist : uval               ([uval])
          | uval COMMA arglist (uval :: arglist)
  (* All three `match` keywords are with-block forms, so they join `uval`, not `uexp`. They share ONE arms
     nonterminal over the unified pattern language and differ only in the flavour tag; the lowering split
     and the per-flavour pattern gate live in the elaborator (D28/D32). *)
  umatch     : TMATCH uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Auto, uval, uarms, Position.range_position (TMATCHleft, TRBRACEright)))
  umatchsw   : TMATCHSWITCH uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Switch, uval, uarms, Position.range_position (TMATCHSWITCHleft, TRBRACEright)))
  umatchcase : TMATCHCASE uval TLBRACE uarms TRBRACE
                 (UE_Match (MF_Case, uval, uarms, Position.range_position (TMATCHCASEleft, TRBRACEright)))
  uarms : upat TARROW uval               ([(upat, uval)])
        | upat TARROW uval COMMA uarms   ((upat, uval) :: uarms)
  (* The single pattern grammar, shared by every binding site above (D28). Its own nonterminals, disjoint
     from `uexp`, so the constructor pattern cannot clash with the call production nor or-`|` with bitwise
     or. It deliberately ACCEPTS more than any one site can lower (a numeral in `let`, a constructor under
     `match_switch`); each site's elaborator rejects the rest WITH A POSITION, which beats a bare "syntax
     error" and keeps one grammar for one language. *)
  upat : IDENT                    (mk_ident_pat (IDENT, IDENTleft))   (* `_` normalises to P_Wild *)
       | NUM                      (P_Lit (NUM, NUMleft))
       | IDENT LPAR upats RPAR    (P_Constr (IDENT, IDENTleft, upats))
       | upat TBAR upat           (mk_or_pat (upat1, upat2, TBARleft))
  upats : upat                    ([upat])
        | upat COMMA upats        (upat :: upats)
\<close>

section\<open> Elaborator (AST -> shallow terms) \<close>

text\<open> Each form lowers to the EXISTING shallow HOL consts -- see the per-node table in
\<open>urust-parser-design-decisions.md\<close> \<open>\<section>2\<close>. Bare numerals stay POLYMORPHIC (matching the frontend's
open default); suffixed ones pin an \<open>N word\<close>. Everything is built with \<open>dummyT\<close>; a single
\<open>Syntax.check_term\<close> runs in the command. \<close>
ML\<open>
structure URust_Translate =
struct
  open URust_AST

  (* All Core terms are built with dummyT; a single Syntax.check_term (in the command) resolves types. *)
  fun mk_const name args = Term.list_comb (Const (name, dummyT), args)
  fun mk_literal v = mk_const \<^const_name>\<open>literal\<close> [v]

  (* Arity -> the funcallN const, DERIVED from the family's `<prefix><n>` naming rather than 15 rows; the
     prefix comes from an antiquoted const name and the derived name at the cap is asserted against its own
     antiquotation at build time, so a rename breaks the build here (D29). The cap is 14, NOT 16:
     Core_Expression defines funcall0..16 but the frontend's surface lowering stops at 14, so a >14 call has
     no golden to conform against. *)
  val max_funcall_arity = 14
  val funcall_prefix = unsuffix "0" \<^const_name>\<open>funcall0\<close>
  val _ = funcall_prefix ^ string_of_int max_funcall_arity = \<^const_name>\<open>funcall14\<close> orelse
            error "urust_expr: the funcallN const family no longer follows the <prefix><n> naming"

  fun funcall_const pos n =
    if 0 <= n andalso n <= max_funcall_arity then funcall_prefix ^ string_of_int n
    else error ("urust_expr: unsupported call arity " ^ string_of_int n ^ " (max " ^
                string_of_int max_funcall_arity ^
                "; the frontend's surface lowering caps here)" ^ Position.here pos)

  (* Integer-literal SUFFIX -> HOL type: the SINGLE place suffix knowledge lives, so adding `u128` or the
     signed `i*` types is ONE row here + a conformance golden (D29). *)
  fun int_suffix_typ "u8"    = SOME \<^typ>\<open>8 word\<close>
    | int_suffix_typ "u16"   = SOME \<^typ>\<open>16 word\<close>
    | int_suffix_typ "u32"   = SOME \<^typ>\<open>32 word\<close>
    | int_suffix_typ "u64"   = SOME \<^typ>\<open>64 word\<close>
    | int_suffix_typ "usize" = SOME \<^typ>\<open>64 word\<close>   (* usize is modelled as 64-bit *)
    | int_suffix_typ _       = NONE

  (* A suffixed integer lexeme ("0x4_u8" / "1_usize") -> (value, type). Splits at the FIRST `_`; digits are
     decimal, or hex with an `0x` prefix. Malformed digits and unknown suffix both error WITH a position. *)
  fun parse_int_lit pos lexeme =
    let
      val (numstr, sfx) =
        (case first_field "_" lexeme of
           SOME (a, b) => (a, b)
         | NONE => error ("urust_expr: malformed suffixed integer literal " ^ quote lexeme ^
                          Position.here pos))
      val value =
        (case (if String.isPrefix "0x" numstr
               then StringCvt.scanString (Int.scan StringCvt.HEX) (String.extract (numstr, 2, NONE))
               else Int.fromString numstr) of
           SOME v => v
         | NONE => error ("urust_expr: cannot read integer literal " ^ quote numstr ^ Position.here pos))
    in
      (case int_suffix_typ sfx of
         SOME T => (value, T)
       | NONE => error ("urust_expr: unsupported integer-literal suffix " ^ quote ("_" ^ sfx) ^
                        " (supported: _u8 _u16 _u32 _u64 _usize)" ^ Position.here pos))
    end

  (* Peel the `_type_constraint_` wrapper (and positions) to reach the leaf a name resolved to. TRAP:
     `Syntax.parse_term` wraps a resolved constant in `_type_constraint_` and `Term_Position.strip_positions`
     does NOT remove it, so a naive `Const (c,_)` match falls through and mis-paints `True`/`None`/... as a
     blue free. Markup only -- the returned `t` keeps the wrapper for check_term (D14). *)
  fun ident_leaf t =
    (case Term_Position.strip_positions t of
       Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ u => ident_leaf u
     | u => u)

  (* Resolve a bare identifier in a dispatch CONTEXT (`kind`): NLiteral at value position, NFunction for a
     call callee; the CALLER decides the `literal` wrapper (value position wraps, a callee does not). Three
     things here are load-bearing (D13/D14; full rationale in the design-decisions doc):
       - REGISTERED -> the frontend's urust_dispatch marker, resolved by its globally-installed term_check
         phases (reused, not reimplemented). Its witness must stay a bare `Free`, NOT parse_term'd, so an
         enclosing `Term.lambda` can capture it into a `Bound` -- that is what makes a binder outrank the
         notation table (witness precedence).
       - UNREGISTERED -> `Syntax.parse_term`, because building terms directly bypasses
         `Syntax_Phases.decode_term`, which is what promotes a bare `Free name` to the HOL `Const` (or the
         context-fixed variable). A raw Free would survive as an extra free variable and be rejected.
       - MARKUP is emitted HERE, once, over the token's full range: the token carries none (tok_ident), and
         decode_term's own report lands at Position.none because we hand parse_term a positionless name. *)
  fun ident_term ctxt kind name pos =
    (case Micro_Rust_Names.lookups ctxt kind name of
       [] =>
         let val t = Syntax.parse_term ctxt name in
           (case ident_leaf t of
              Const (c, _) =>
                Context_Position.report ctxt pos
                  (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
            | Free (a, _) =>
                (* decode_term's Free case, reproduced (syntax_phases.ML:304-313): a context-fixed free gets
                   markup_free = nav-to-`fixes` + colour; a genuine free just Markup.free. *)
                (case Proof_Context.lookup_free ctxt a of
                   SOME x =>
                     List.app (Context_Position.report ctxt pos)
                       (Syntax_Phases.markup_free ctxt x)
                 | NONE => Context_Position.report ctxt pos Markup.free)
            | _ => Context_Position.report ctxt pos Markup.free);
           t
         end
     | _  => Micro_Rust_Dispatch.mk_marker kind name pos (Free (name, dummyT)))

  (* Is a bare pattern identifier a data constructor? `Code.is_constr` is the SAME oracle the frontend's
     resolve_constructor_id uses. A constructor resolves to its RAW Const -- not the value embedding a
     value-position id gets, since a pattern head must be the bare constructor; anything else is NONE = a
     variable binder (D27). *)
  fun resolve_ctor ctxt name =
    let val thy = Proof_Context.theory_of ctxt in
      (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
         SOME (Const (full, _)) => if Code.is_constr thy full then SOME (Const (full, dummyT)) else NONE
       | _ => NONE)
    end

  (* Const entity markup (colour + ctrl-click-to-definition) for a resolved pattern constructor head, so
     `Some`/`Ok`/a user ctor navigates like any const. Emitted here rather than in `resolve_ctor`, which
     stays pure because it is also used merely to CLASSIFY (C1). *)
  fun report_ctor_markup ctxt pos (Const (c, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
    | report_ctor_markup _ _ _ = ()

  (* A wildcard binds nothing, so bind_var's colour/nav do not apply -- but it must still get a typing
     tooltip, or ctrl-hover falls through to the enclosing command span (rule C3). *)
  fun report_wildcard ctxt pos = Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

  (* `let x = e; k` -> bind e (\<lambda>x. k) (HOAS). Sequencing MUST be `sequence`, not `bind e (\<lambda>_. k)`:
     the latter is definitionally but NOT alpha-equal to the frontend, so `refl` conformance would fail. *)
  fun mk_bind e f     = mk_const \<^const_name>\<open>Core_Expression.bind\<close> [e, f]
  fun mk_sequence a b = mk_const \<^const_name>\<open>Core_Expression.sequence\<close> [a, b]

  (* if c {t} else {e} -> two_armed_conditional. A one-armed `if` fills the else with `skip`: the frontend's
     `{..}` path emits two_armed_conditional c t skip, NOT one_armed_conditional, and `skip` is an (input)
     abbreviation for `literal ()` -- so we must emit `literal ()` here (D22). *)
  fun mk_two_armed c t e = mk_const \<^const_name>\<open>two_armed_conditional\<close> [c, t, e]

  (* match_switch -> bind <<scrut>> (ncase_selector [(key, body), ..]): numeral key -> Some n, `_` -> None,
     each or-alternative its own pair with the same body. First-order -- no binders, no case skeleton (D26). *)
  fun mk_some v = mk_const \<^const_name>\<open>Option.Some\<close> [v]
  val mk_none   = Const (\<^const_name>\<open>Option.None\<close>, dummyT)
  fun mk_pair a b = mk_const \<^const_name>\<open>Product_Type.Pair\<close> [a, b]
  fun mk_cons h t = mk_const \<^const_name>\<open>List.Cons\<close> [h, t]
  val mk_nil      = Const (\<^const_name>\<open>List.Nil\<close>, dummyT)
  fun mk_ncase_selector lst = mk_const \<^const_name>\<open>ncase_selector\<close> [lst]

  (* Ctr_Sugar case skeleton (match_case, D27): case_guard/case_cons/case_nil/case_elem/case_abs are
     uninterpreted HOL markers, and the Case_Translation term-check phase folds a well-formed tree into the
     datatype's concrete `case_<T>` DURING our single check_term. So we build exactly the frontend's
     skeleton and never construct case_option / case_result ourselves. *)
  fun mk_case_guard b s cs = mk_const \<^const_name>\<open>case_guard\<close> [b, s, cs]
  fun mk_case_cons h t     = mk_const \<^const_name>\<open>case_cons\<close> [h, t]
  val mk_case_nil          = Const (\<^const_name>\<open>case_nil\<close>, dummyT)
  fun mk_case_elem p b     = mk_const \<^const_name>\<open>case_elem\<close> [p, b]
  fun mk_case_abs f        = mk_const \<^const_name>\<open>case_abs\<close> [f]

  (* Operator -> HOL const, one row each (the frontend's shallow-embedding targets: `+` is the overloaded
     urust_add, other arithmetic/shift/bitwise are the Numeric_Types word combinators, comparisons and
     connectives the comp_*/urust_* ones). *)
  fun binop_const Add  = \<^const_name>\<open>urust_add\<close>
    | binop_const Sub  = \<^const_name>\<open>word_minus_no_wrap\<close>
    | binop_const Mul  = \<^const_name>\<open>word_mul_no_wrap\<close>
    | binop_const Div  = \<^const_name>\<open>word_udiv\<close>
    | binop_const Mod  = \<^const_name>\<open>word_umod\<close>
    | binop_const Shl  = \<^const_name>\<open>word_shift_left_shift64\<close>
    | binop_const Shr  = \<^const_name>\<open>word_shift_right_shift64\<close>
    | binop_const BAnd = \<^const_name>\<open>word_bitwise_and\<close>
    | binop_const BOr  = \<^const_name>\<open>word_bitwise_or\<close>
    | binop_const BXor = \<^const_name>\<open>word_bitwise_xor\<close>
    | binop_const Eq   = \<^const_name>\<open>urust_eq\<close>
    | binop_const Ne   = \<^const_name>\<open>urust_neq\<close>
    | binop_const Lt   = \<^const_name>\<open>comp_lt\<close>
    | binop_const Le   = \<^const_name>\<open>comp_le\<close>
    | binop_const Gt   = \<^const_name>\<open>comp_gt\<close>
    | binop_const Ge   = \<^const_name>\<open>comp_ge\<close>
    | binop_const And  = \<^const_name>\<open>urust_conj\<close>
    | binop_const Or   = \<^const_name>\<open>urust_disj\<close>
  fun unop_const Not = \<^const_name>\<open>negation_const\<close>
  fun mk_bin bop a b = mk_const (binop_const bop) [a, b]
  fun mk_un uop a    = mk_const (unop_const uop) [a]

  (* Shared binder / markup / antiquotation helpers (Parser_Utils, see there); the entity-kind string is
     partially applied once so the call sites below read unchanged. *)
  val vkind       = "urust_var"
  val report_ref  = Parser_Utils.report_ref vkind
  val bind_var    = Parser_Utils.bind_var vkind
  val parse_antiq = Parser_Utils.parse_antiq vkind
  val anon_abs    = Parser_Utils.anon_abs

  (* Abstract a mixed list of binder SLOTS over an inner term, leftmost binder OUTERMOST: `SOME free` is a
     NAMED source binder (abstracted by name, so its occurrences anywhere inside are captured -- HOAS),
     `NONE` an ANONYMOUS one, referenced only through the `Bound` index handed to `mk_inner`. `wrap` goes
     around each abstraction (Ctr_Sugar's `case_abs` here). For a SINGLE binder, abstract directly instead
     (`Term.lambda` / `anon_abs`); this exists for the several-binders case, where the indices interact.

     Mixing the two kinds is sound because the indices handed out are the FINAL ones (counting all `n`
     abstractions): `Term.abstract_over` (behind `Term.lambda`) tracks its own level as it descends and
     LEAVES existing `Bound`s untouched (Pure/term.ML:841-852), while each `Abs` binds the loose index 0 of
     its body. So a pre-placed index still denotes its slot after any number of outer abstractions.
     uRust-specific (the only caller is the constructor-pattern branch below), so it lives here rather than
     in the shared Parser_Utils layer. *)
  fun abs_slots wrap slots mk_inner =
    let
      val n = length slots
      val args = map_index (fn (_, SOME free) => free | (j, NONE) => Bound (n - 1 - j)) slots
    in
      fold_rev (fn slot => fn t =>
          wrap (case slot of SOME free => Term.lambda free t | NONE => anon_abs t))
        slots (mk_inner args)
    end

  (* The IRREFUTABLE pattern seam (`let`/`const`, later closure and `fn` parameters): register the
     pattern's variable(s), return an abstraction builder for the binder's body + the extended env.
     `bind_case_pat` below is the refutable (match-arm) seam and the `MF_Switch` `key` function the
     first-order one; all three consume the SAME `ur_pat`, so a new pattern form is one constructor + one
     clause per seam, with every binding SITE unchanged (D28). *)
  fun pat_pos (P_Wild pos) = pos
    | pat_pos (P_Ident (_, pos)) = pos
    | pat_pos (P_Lit (_, pos)) = pos
    | pat_pos (P_Constr (_, pos, _)) = pos
    | pat_pos (P_Or (_, pos)) = pos

  (* Bare `match` mirrors the frontend's syntactic head-based router. Identifiers and `_` fit either
     lowering, so case wins; a disjunction is case-shaped even when its alternatives are numerals, leaving
     the existing Tier-0 `MF_Case` diagnostic to reject it. *)
  fun classify_match arms pos =
    let
      fun case_compatible (P_Lit _) = false
        | case_compatible _ = true
      fun switch_compatible (P_Lit _) = true
        | switch_compatible (P_Ident _) = true
        | switch_compatible (P_Wild _) = true
        | switch_compatible _ = false
      val pats = map #1 arms
    in
      if List.all case_compatible pats then MF_Case
      else if List.all switch_compatible pats then MF_Switch
      else
        error ("urust_expr: mixed numeral and constructor patterns in bare `match`" ^
               Position.here pos)
    end

  fun bind_pat ctxt env pat =
    (case pat of
       (* A bare id here is ALWAYS a variable binder, deliberately NOT run through resolve_ctor: the
          frontend's `let` binder is a plain identifier, so `let None = e; ..` binds a variable named
          `None`, and rejecting it as a nullary constructor would be a DIVERGENCE, not extra fidelity. *)
       P_Ident (x, def_pos) =>
         let val (free, env') = bind_var ctxt env (x, def_pos)
         in (fn body => Term.lambda free body, env') end
       (* `let _ = e; k` binds nothing: an anonymous lambda, NOT a variable literally named "_" (that
          leaked a `Free "_"` into the defined term). *)
     | P_Wild _ => (fn body => anon_abs body, env)
     | _ =>
         error ("urust_expr: refutable pattern in an irrefutable (let/const) binder position" ^
                Position.here (pat_pos pat)))

  (* The REFUTABLE (match-arm) seam: a pattern -> a Ctr_Sugar case branch builder + the extended env.
     Reuses bind_var for per-variable registration but builds the case_abs/case_elem skeleton instead of a
     plain lambda. Tier-0 = wildcard / variable / nullary ctor / single-level ctor with binder-or-`_` args;
     everything else errors WITH a position (D27). *)
  fun bind_case_pat ctxt env pat =
      (case pat of
         P_Wild pos =>
           (report_wildcard ctxt pos;
            (fn body => mk_case_abs (anon_abs (mk_case_elem (Bound 0) body)), env))
       | P_Ident (name, pos) =>
           (case resolve_ctor ctxt name of
              SOME c => (report_ctor_markup ctxt pos c;                      (* nullary constructor *)
                         (fn body => mk_case_elem c body, env))
            | NONE =>                                                        (* variable binder *)
                let val (f, env') = bind_var ctxt env (name, pos)
                in (fn body => mk_case_abs (Term.lambda f (mk_case_elem f body)), env') end)
       | P_Constr (name, pos, args) =>
           (case resolve_ctor ctxt name of
              NONE => error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^ Position.here pos)
            | SOME c =>
                let
                  val _ = report_ctor_markup ctxt pos c
                  (* Each arg is a SLOT: `SOME free` = a named source binder, `NONE` = a `_` (anonymous). *)
                  fun arg (P_Wild pos) env = (report_wildcard ctxt pos; (NONE, env))
                    | arg (P_Ident (a, ap)) env =
                        (case resolve_ctor ctxt a of
                           SOME _ => error ("urust_expr: nested nullary-constructor pattern `" ^ a ^
                                       "` not yet supported (Tier-0: binder / `_` constructor args only)" ^
                                       Position.here ap)
                         | NONE => let val (f, env') = bind_var ctxt env (a, ap) in (SOME f, env') end)
                    | arg p _ =
                        error ("urust_expr: nested " ^
                               (case p of P_Constr _ => "constructor" | P_Lit _ => "literal"
                                        | P_Or _ => "or-" | _ => "") ^
                               " pattern not yet supported (Tier-0: binder / `_` constructor args only)" ^
                               Position.here (pat_pos p))
                  val (slots, env') = fold_map arg args env
                in
                  (* the one shape where several binders nest and mix named with anonymous -- hence
                     abs_slots (rows `mc_pair`, `mc_hyg_sibling`) *)
                  (fn body =>
                     abs_slots mk_case_abs slots
                       (fn ps => mk_case_elem (Term.list_comb (c, ps)) body), env')
                end)
       (* Parseable (the pattern grammar is shared) but not yet lowerable here, so: positioned errors. A
          literal pattern needs the frontend's guarded path; an or-pattern needs arm duplication. *)
       | P_Lit (_, pos) =>
           error ("urust_expr: literal patterns are not yet supported in `match_case`" ^
                  " (numeral patterns belong to `match_switch` today)" ^ Position.here pos)
       | P_Or (_, pos) =>
           error ("urust_expr: or-patterns are not yet supported in `match_case`" ^ Position.here pos))

  (* env : source name -> var_info for the enclosing binders (lexical scope). A bound use resolves to its
     binder's Free + nav markup and is NOT sent through dispatch -- lexical scoping wins, matching the
     frontend's witness precedence. Capture is by construction: the enclosing Term.lambda abstracts the
     `Free name` returned here (and any a nested antiquotation parses). *)
  fun mk ctxt env e =
    (case e of
       UE_Num (n, _)       => mk_literal (HOLogic.mk_number dummyT n)
     | UE_NumSfx (lexeme, pos) =>
         let val (v, T) = parse_int_lit pos lexeme in mk_literal (HOLogic.mk_number T v) end
     | UE_Unit _           => mk_literal HOLogic.unit
     | UE_Ident (name, pos) =>
         (case Symtab.lookup env name of
            SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) pos; mk_literal free)
          | NONE => mk_literal (ident_term ctxt Micro_Rust_Names.NLiteral name pos))
     | UE_ValAntiq src     => mk_literal (parse_antiq ctxt env src)
     | UE_ExprAntiq src    => parse_antiq ctxt env src
     | UE_Seq (e1, e2)     => mk_sequence (mk ctxt env e1) (mk ctxt env e2)
     | UE_Bin (bop, a, b, _) => mk_bin bop (mk ctxt env a) (mk ctxt env b)
     | UE_Un (uop, a, _)     => mk_un uop (mk ctxt env a)
     | UE_Block (e1, _)    => mk ctxt env e1          (* erase: alpha-equal to the frontend `{ e } = e` *)
     | UE_If (c, t, eopt, _) =>
         mk_two_armed (mk ctxt env c) (mk ctxt env t)
           (case eopt of SOME e => mk ctxt env e | NONE => mk_literal HOLogic.unit)
     | UE_Let bnd          => elab_let ctxt env bnd
     | UE_Const bnd        => elab_let ctxt env bnd   (* same desugaring as let today (SE:433-434) *)
     | UE_Call (name, npos, args, cpos) =>
         (* The callee resolves in NFunction context and is NOT wrapped in `literal` (a bound callee -> its
            env Free). Args are ordinary value expressions, so nested calls fall out of the recursion. *)
         let
           val func =
             (case Symtab.lookup env name of
                SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) npos; free)
              | NONE => ident_term ctxt Micro_Rust_Names.NFunction name npos)
         in mk_const (funcall_const cpos (length args)) (func :: map (mk ctxt env) args) end
     (* ONE match clause; the flavour picks the lowering. Both are `bind <<scrut>> <selector>` with the
        scrutinee in the OUTER env (as elab_let does) and each arm body in the env its own pattern extends. *)
     | UE_Match (flavour, scrut, arms, pos) =>
         let
           val selected = (case flavour of MF_Auto => classify_match arms pos | explicit => explicit)
         in
           mk_bind (mk ctxt env scrut)
           (case selected of
              (* MF_Switch: first-order, so a pattern must be a numeral, `_`, or an or-list of those; a
                 binding pattern is rejected WITH ITS POSITION -- the point of sharing the grammar (D26). *)
              MF_Switch =>
                let
                  fun key (P_Lit (n, _))    = mk_some (HOLogic.mk_number dummyT n)
                    | key (P_Wild pos)      = (report_wildcard ctxt pos; mk_none)
                    | key (P_Ident (s, pos)) =
                        error ("urust_expr: unsupported match_switch key " ^ quote s ^
                               " (numeral or `_` only; const-id / path keys not yet supported)" ^
                               Position.here pos)
                    | key p =
                        error ("urust_expr: unsupported match_switch pattern" ^
                               " (numeral, `_`, or an or-list of those; binding patterns need" ^
                               " `match_case`)" ^ Position.here (pat_pos p))
                  (* one (key, body) pair per or-alternative, sharing the body elaborated ONCE *)
                  fun arm_pairs (pat, body) =
                    let val b = mk ctxt env body
                    in map (fn k => mk_pair (key k) b)
                         (case pat of P_Or (ps, _) => ps | p => [p])
                    end
                in mk_ncase_selector (fold_rev mk_cons (maps arm_pairs arms) mk_nil) end
              (* MF_Case (D27): \<lambda>anon. case_guard True anon (case_cons B1 .. case_nil), each Bi from
                 bind_case_pat; Case_Translation folds it to case_<T> during check_term. *)
            | MF_Case =>
                let
                  fun arm (pat, body) =
                    let val (absf, env') = bind_case_pat ctxt env pat
                    in absf (mk ctxt env' body) end
                  val branches = fold_rev (fn a => fn acc => mk_case_cons (arm a) acc) arms mk_case_nil
                in
                  (* the invented scrutinee binder is ANONYMOUS (`Abs` + `Bound`), never a named Free, so it
                     cannot capture anything in the branches -- see anon_abs *)
                  anon_abs (mk_case_guard \<^term>\<open>True\<close> (Bound 0) branches)
                end
            | MF_Auto => error "urust_expr: internal unresolved auto match flavour")
         end)

  (* `let`/`const` <pat> = rhs; body -> bind rhs (<pat-abstraction> body); shared by both nodes. *)
  and elab_let ctxt env (pat, rhs, body) =
    let
      val rhs'         = mk ctxt env rhs        (* rhs is in the OUTER scope (pat not yet visible) *)
      val (absf, env') = bind_pat ctxt env pat  (* register pattern vars; get body abstraction *)
      val body'        = mk ctxt env' body      (* innermost binding wins -> shadowing-correct *)
    in mk_bind rhs' (absf body') end

  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

section\<open> The command \<close>

text\<open> `urust_expr NAME <src>` parses, elaborates, type-checks once, and defines NAME := <term>. No
attributes: the conformance proof uses the primitive \<open>NAME_def\<close> and corpus defs must stay out of the
global simp set. \<close>
ML\<open>
(* THE pipeline, exported: every uRust command runs source through exactly this function, so the positive
   harness (`urust_expr`) and the negative one (`urust_expr_rejects`, Micro_Rust_Parser_Negative_Conformance)
   can never drift on WHAT they exercise -- only on how they interpret success/failure. Raises (positioned)
   on any rejection: lexer (URust_Err.lex_error), yacc (parse_source's print_error), elaborator, or
   check_term.
   ONLY `parse_source` touches the Isabelle_lex_yacc global refs, so only it is serialized; elaboration and
   check_term are pure w.r.t. those, and holding the lock across them would serialize the (slower)
   type-checking of every uRust command theory-wide. *)
fun elab_urust lthy source : term =
  (case Parser_Utils.with_parser_lock (fn () => URust.parse_source lthy source) of
     SOME ast => Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun define_urust (binding, source) lthy =
  let
    val ((_, _), lthy') =
      Local_Theory.define
        ((binding, NoSyn), ((Thm.def_binding binding, []), elab_urust lthy source)) lthy
  in lthy' end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding -- Parse.input Parse.cartouche >> define_urust)
\<close>

section\<open> Smoke test \<close>

text\<open> A few definitions to confirm the command works in isolation; the real conformance check (against
the frontend's golden terms) lives in Micro_Rust_Parser_Conformance.thy. \<close>
urust_expr smoke_num  \<open> 42 \<close>
urust_expr smoke_sfx  \<open> 1_u32 \<close>
urust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

end
