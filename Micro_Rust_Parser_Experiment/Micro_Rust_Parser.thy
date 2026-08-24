(* The custom uRust parser (Phase 1, in progress).

   A real uRust parser built as an ml_lex_yacc lexer + LALR grammar -> reified SML AST -> elaboration
   into the EXISTING shallow terms, exposed as an outer-syntax command `micro_rust_expr NAME <src>`.
   The governing invariant is that the elaborated term is ALPHA-EQUAL to what the inner-syntax bracket
   `\<lbrakk> src \<rbrakk>` produces today -- validated by the companion Micro_Rust_Parser_Conformance.thy
   (each row closes by `unfolding NAME_def by (rule refl)`).

   Constructs covered so far (see the surface-grammar BNF in notes/urust-parser-design-decisions.md):
     * literals -- bare decimal numerals, suffixed integer literals (decimal + hex), unit ();
     * value / expression antiquotations <<v>> / eps<e> (raw HOL spliced in);
     * bare identifiers -- registered (literal) micro_rust_notation names resolve via the frontend's
       urust_dispatch term_check phases (reused, not reimplemented); otherwise parsed as HOL (a known
       constant -> its Const, else a Free);
     * let / const bindings and statement sequencing (`;`, trailing `;`);
     * pure-value operators (arithmetic / bitwise / shifts / comparison / logical + unary `!`);
     * block expressions { stmts } (erase to their body) and if / else (two-armed, one-armed, else-if).
   Deferred (later steps -- notes/urust-parser-plan.md): the reference tier (`*` deref, `&`/`&mut`,
   `=`/compound-assign, `?`), let mut, tuple/constructor patterns, match / loops, calls, return,
   panic!/strings, paths Foo::Bar, and the no-semicolon "optional `;` after a block-like expression"
   sequencing (a block/if in statement position currently requires a trailing `;`).

   Technique carried over from Toy_Lex_Yacc: the corrected symbol-position layer (fixed_pos / tokF /
   tok_valF), the antiquotation start-state lexing, dummyT + a single Syntax.check_term, and the
   command mutex. ASCII escape form throughout (isabelle build rejects raw UTF-8 cartouche delimiters). *)

theory Micro_Rust_Parser
  imports
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
    "Isabelle_Lex-Yacc.LexYacc"
    Parser_Utils
  keywords
    "micro_rust_expr" :: thy_decl
begin

section\<open> Reified AST (literal tier) \<close>

text\<open> One constructor per dispatch-free literal form. Positions are carried for markup/diagnostics. \<close>
ML\<open>
structure URust_AST =
struct
  (* Binder pattern. Currently only a single variable; this is the EXTENSION POINT for tuple /
     constructor / wildcard patterns (tuple `let (a, b)`, match arms `Some(x, y)`, `_`). Adding a
     constructor here + a case in bind_pat (the elaborator) generalises every binding construct
     (let/const, and future closures / for-loops / match) at once -- the binders themselves are
     unchanged. *)
  datatype ur_pat =
      P_Var of string * Position.T                    (* x  (its name position, for def markup) *)

  (* Pure-value operators (arithmetic / bitwise / comparison / logical + unary !). Data-driven: the
     elaborator maps each to a single HOL const (URust_Translate.binop_const / unop_const), so adding
     an operator is one datatype line + one table row, not a bespoke case. *)
  datatype binop =
      Add | Sub | Mul | Div | Mod              (* + - * / %       *)
    | Shl | Shr                                (* << >>           *)
    | BAnd | BOr | BXor                        (* & | ^  (infix)  *)
    | Eq | Ne | Lt | Le | Gt | Ge              (* == != < <= > >= *)
    | And | Or                                 (* && ||           *)
  datatype unop = Not                          (* !  (and !! = !(!_)) *)

  datatype ur_expr =
      UE_Num       of int * Position.T                (* bare decimal: 0, 1, 42 *)
    | UE_NumSfx    of int * int * Position.T          (* value, width; 1_u32 / 0x4_u8; usize -> 64 *)
    | UE_Unit      of Position.T                       (* () *)
    | UE_Ident     of string * Position.T             (* bare identifier at value position *)
    | UE_ValAntiq  of Input.source                    (* <<v>>  body as a POSITIONED source -> literal v *)
    | UE_ExprAntiq of Input.source                    (* eps<e> body as a POSITIONED source -> e *)
    | UE_Let       of ur_pat * ur_expr * ur_expr      (* let <pat> = rhs; body -> bind *)
    | UE_Const     of ur_pat * ur_expr * ur_expr      (* const <pat> = rhs; body; SAME desugaring as
                                                          let today (SE:433-434) -- kept a distinct
                                                          node so the source keyword is preserved for
                                                          when const diverges (item-level const, B7) *)
    | UE_Seq       of ur_expr * ur_expr               (* e1; e2 -> sequence (trailing `;`: e2 = unit) *)
    | UE_Bin       of binop * ur_expr * ur_expr * Position.T   (* a <binop> b *)
    | UE_Un        of unop * ur_expr * Position.T              (* !a  (and !!a = !(!a)) *)
    | UE_Block     of ur_expr * Position.T                    (* { stmts } -- ERASES to <stmts> (no
                                                                 `scoped` wrapper); frontend
                                                                 `_urust_scoping` is identity (SE:360-362) *)
    | UE_If        of ur_expr * ur_expr * ur_expr option * Position.T
                                                              (* if c {t} [else {e} | else if ...];
                                                                 NONE else-branch -> skip (one-armed) *)
end
\<close>

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> typing / sorting \<close>

ML\<open>
(* Positioned lexer error, raised from the catch-all lex rule so an unrecognized character ABORTS with
   a clickable position instead of being silently skipped (the parser's whole rationale includes
   positioned diagnostics). Defined in Isabelle/ML -- where `error` / `quote` / `Position.here` are in
   scope -- and SML_imported for the lexer's SML environment. *)
structure URust_Err =
struct
  fun lex_error text pos =
    error ("micro_rust_expr: unexpected input " ^ quote text ^ Position.here pos)
end
\<close>
SML_import \<open> structure URust_Err = URust_Err \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>  \<comment>\<open> shared lexer position math \<close>

section\<open> Lexer + grammar \<close>

text\<open> The antiquotation brackets are the Isabelle symbols \<open>\<llangle>\<close>/\<open>\<rrangle>\<close> (value
escape) and \<open>\<epsilon>\<close> + \<open>\<open>\<close>/\<open>\<close>\<close> (expression escape); each is matched by an
explicit escape rule and its body captured with a start state, without lexing the HOL inside.
Operator precedence is declared once with yacc %left/%nonassoc/%right directives, reproducing the
frontend's infix priorities (Micro_Rust_Syntax.thy:559-603). The fixed_pos / report_fixed / tokF /
tok_valF / tok_ident position layer is INTENTIONALLY DUPLICATED with Toy_Lex_Yacc: it runs in this
ml_lex_yacc block's SML environment and is scoped to it, so it cannot move into the shared Parser_Utils
(plain Isabelle/ML) -- the elaborator helpers, which are plain ML, did move there. \<close>
ml_lex_yacc "URust" where
lex_user_declarations\<open>
val aq_buf = ref ""
val aq_pos = ref 0
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)

(* Parse a suffixed integer literal lexeme, e.g. "0x4_u8" / "1_usize", to (value, width). *)
fun parse_sfx s =
  let
    val (numSS, sfxSS) = Substring.position "_u" (Substring.full s)
    val numstr = Substring.string numSS
    val sfx = Substring.string (Substring.triml 2 sfxSS)   (* drop "_u" *)
    val width = (case sfx of "8" => 8 | "16" => 16 | "32" => 32 | "64" => 64 | "size" => 64
                           | other => raise Fail ("micro_rust_expr: unsupported integer width _u" ^ other))
    val value =
      if String.isPrefix "0x" numstr
      then valOf (StringCvt.scanString (Int.scan StringCvt.HEX) (String.extract (numstr, 2, NONE)))
      else valOf (Int.fromString numstr)
  in (value, width) end

(* Per-lexer source ref + set-shadow (SML environment). The corrected char-vs-symbol position MATH is
   shared in Parser_Lex_Util (see Parser_Utils); these thin wrappers pass the current source. tok_ident
   keeps this lexer's Tokens.IDENT constructor and emits NO colour -- URust_Translate.ident_term colours
   each identifier once it knows the name's role (registered notation / HOL const / free), producing one
   correctly-ranged markup (eager Markup.free here previously split the highlight on registered names). *)
val the_src = ref (Input.string "")
fun set source ctxt = (Isabelle_lex_yacc.set source ctxt; the_src := source)

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!the_src) yypos
fun tokF args       = Parser_Lex_Util.tokF (!the_src) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!the_src) args
fun report_colour args = Parser_Lex_Util.report_colour (!the_src) args
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
<INITIAL>({digit}+|"0x"{hexdigit}+)"_u"("8"|"16"|"32"|"64"|"size") =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", "", Tokens.NUMSFX, parse_sfx yytext));
<INITIAL>{digit}+ => (tok_valF (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", "", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", "", Tokens.TCONST));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", "", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", "", Tokens.TELSE));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.keyword2, "TEQ", "", Tokens.TEQ));
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
<INITIAL>"{"      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACE", "", Tokens.TLBRACE));
<INITIAL>"}"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACE", "", Tokens.TRBRACE));
<INITIAL>\\"<llangle>"          => (aq_buf := ""; aq_pos := yypos; aq_start := yypos + size yytext; YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (report_colour (yypos, 1, Markup.literal); aq_buf := ""; aq_pos := yypos; aq_start := yypos + size yytext; YYBEGIN EAQ; lex());
<INITIAL>.        => (URust_Err.lex_error yytext (fixed_pos yypos));
<VAQ>\\"<rrangle>" => (YYBEGIN INITIAL;
    let val p = fixed_pos (!aq_start) val q = fixed_pos yypos
    in Tokens.VALAQ (Input.source true (!aq_buf) (Position.range (p, q)), p, q) end);
<VAQ>\n           => (aq_buf := !aq_buf ^ "\n"; lex());
<VAQ>.            => (aq_buf := !aq_buf ^ yytext; lex());
<EAQ>\\"<close>"   => (YYBEGIN INITIAL;
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

(* Operator precedence, loosest -> tightest (reproduces the frontend's infix priorities,
   Micro_Rust_Syntax.thy:559-603). Comparisons are non-associative (Rust rejects `a == b == c`);
   prefix `!` binds tighter than every binary operator. The ambiguous `uexp OP uexp` productions are
   resolved by these directives, keeping the LALR construction conflict-free. *)
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

%term NUM of int | NUMSFX of int * int | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TLET | TCONST | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG
%nonterm ustart of URust_AST.ur_expr option
       | ustmt of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
       | ublock of URust_AST.ur_expr
       | uif of URust_AST.ur_expr
\<close>
yacc_rules\<open>
  ustart : ustmt (SOME ustmt)
         | (NONE)
  ustmt : uexp                              (uexp)
        | uexp TSEMI ustmt                  (UE_Seq (uexp, ustmt))
        | uexp TSEMI                        (UE_Seq (uexp, UE_Unit TSEMIleft))
        | TLET IDENT TEQ uexp TSEMI ustmt   (UE_Let (P_Var (IDENT, IDENTleft), uexp, ustmt))
        | TCONST IDENT TEQ uexp TSEMI ustmt (UE_Const (P_Var (IDENT, IDENTleft), uexp, ustmt))
  uexp : NUM        (UE_Num (NUM, NUMleft))
       | NUMSFX     (UE_NumSfx (#1 NUMSFX, #2 NUMSFX, NUMSFXleft))
       | IDENT      (UE_Ident (IDENT, IDENTleft))
       | LPAR RPAR  (UE_Unit LPARleft)
       | LPAR uexp RPAR (uexp)
       | VALAQ      (UE_ValAntiq VALAQ)
       | EXPRAQ     (UE_ExprAntiq EXPRAQ)
       | ublock     (ublock)
       | uif        (uif)
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
  (* Block { stmts }: erases to <stmts> (see UE_Block). if / else: two-armed, one-armed (no else),
     and else-if (the else branch is itself a uif -> nested UE_If). No dangling-else conflict arises:
     because the branches are BRACE-DELIMITED (ublock), TELSE is not in FOLLOW(uif), so after
     `TIF uexp ublock` the parser shifts TELSE unambiguously -- verified conflict-free via [verbose]
     grm.desc (76 states, zero shift/reduce or reduce/reduce). *)
  ublock : TLBRACE ustmt TRBRACE            (UE_Block (ustmt, TLBRACEleft))
  uif : TIF uexp ublock                     (UE_If (uexp, ublock, NONE, TIFleft))
      | TIF uexp ublock TELSE ublock        (UE_If (uexp, ublock1, SOME ublock2, TIFleft))
      | TIF uexp ublock TELSE uif           (UE_If (uexp, ublock, SOME uif, TIFleft))
\<close>

section\<open> Elaborator (AST -> shallow `literal` terms) \<close>

text\<open> Every form lowers to CONST literal (or, for a suffixed literal, literal at a fixed word width --
alpha-equal to the golden ascribeuN, which is an abbreviation of literal). The value type of a bare
numeral is left POLYMORPHIC (matching the frontend's open "what type by default" choice). Built with
dummyT; a single Syntax.check_term runs in the command. \<close>
ML\<open>
structure URust_Translate =
struct
  open URust_AST

  (* All Core terms are built with dummyT; a single Syntax.check_term (in the command) resolves types. *)
  fun mk_const name args = Term.list_comb (Const (name, dummyT), args)
  fun mk_literal v = mk_const \<^const_name>\<open>literal\<close> [v]

  fun word_typ 8  = \<^typ>\<open>8 word\<close>
    | word_typ 16 = \<^typ>\<open>16 word\<close>
    | word_typ 32 = \<^typ>\<open>32 word\<close>
    | word_typ 64 = \<^typ>\<open>64 word\<close>            (* u64 and usize (usize -> 64 in parse_sfx) *)
    | word_typ w  = error ("micro_rust_expr: unsupported integer width u" ^ string_of_int w)

  (* A bare identifier at value position lowers exactly as the frontend's lookup_id_tr
     (Micro_Rust_Shallow_Embedding.thy:911-930): if (NLiteral, name) has a registered backend, emit
     the urust_dispatch marker carrying the source-named Free as witness -- resolved by the
     GLOBALLY-INSTALLED term_check phases during check_term (Micro_Rust_Notations.thy:820-826), which
     we reuse rather than reimplement. The caller wraps the result in `literal`, matching SE:502-503
     `_urust_identifier \<rightharpoonup> literal (_shallow_identifier_as_literal ident)`.

     UNREGISTERED fallback: because we build the term directly, we bypass Syntax_Phases.decode_term,
     which in the frontend's parse pipeline promotes a bare `Free name` to the HOL `Const` of that
     name (or resolves a context-fixed variable). A raw `Free name` would instead survive as an extra
     free variable and be rejected by the definition (e.g. `\<up>True` with `True` free). So we run
     `Syntax.parse_term ctxt name` for the fallback: parsing the identifier as ordinary HOL reproduces
     exactly that promotion (`True`/`None` -> Const, `foo` under `context fixes` -> the fixed Free).

     REGISTERED (marker) witness: kept as a bare `Free (name, dummyT)`, NOT parse_term'd. The witness
     must stay a Free so a future enclosing `Term.lambda (Free (name, T))` (from a `let`) captures it
     into a Bound, at which point resolve_bound makes the binder win (the frontend's
     witness-precedence). Its Free-vs-Const shape does not affect the top-level resolved result -- only
     a Bound witness takes precedence; a Free/Const one defers to the table.

     MARKUP: the IDENT token carries no colour markup (see tok_ident) -- we emit exactly one here, over
     the token's full range `pos`, so it can't split. Registered names are styled by the dispatch
     resolver (emit_use_markup_at_pos). Unregistered names we style ourselves: a resolved HOL Const
     gets the standard const entity markup (colour + ctrl-click to its definition), matching the
     frontend; anything else (a context-fixed / genuine free) gets Markup.free.

     To decide which, we must look at the LEAF the name resolved to -- but `Syntax.parse_term` wraps a
     resolved constant in a `_type_constraint_` node (carrying its most-general type), and
     `Term_Position.strip_positions` does NOT remove that wrapper. So a naive `Const (c,_)` match sees
     the wrapper's application `_type_constraint_ $ Const ...`, fails, and mis-paints a genuine HOL
     constant (`True`/`False`/`None`/...) as a blue Markup.free. `ident_leaf` peels the type-constraint
     wrapper (and positions) to reach the real leaf; the returned term `t` still carries the wrapper,
     which the command's final `check_term` consumes -- so this affects markup only, not the term. *)
  fun ident_leaf t =
    (case Term_Position.strip_positions t of
       Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ u => ident_leaf u
     | u => u)

  fun ident_term ctxt name pos =
    (case Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral name of
       [] =>
         let val t = Syntax.parse_term ctxt name in
           (case ident_leaf t of
              Const (c, _) =>
                Context_Position.report ctxt pos
                  (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
            | _ => Context_Position.report ctxt pos Markup.free);
           t
         end
     | _  => Micro_Rust_Dispatch.mk_marker Micro_Rust_Names.NLiteral name pos (Free (name, dummyT)))

  (* `let x = e; k` / `const x = e; k` -> bind e (\<lambda>x. k)  (HOAS; SE:431-434). MUST be `bind` and
     `e1; e2` MUST be `sequence` (a non-simp definition) to be alpha-equal to the frontend -- emitting
     `bind e (\<lambda>_. k)` for sequencing would be definitionally-but-not-alpha-equal. Trailing `;` ->
     `sequence e (literal ())` (skip is an (input) abbreviation for `literal ()`). *)
  fun mk_bind e f     = mk_const \<^const_name>\<open>Core_Expression.bind\<close> [e, f]
  fun mk_sequence a b = mk_const \<^const_name>\<open>Core_Expression.sequence\<close> [a, b]

  (* if c {t} else {e} -> two_armed_conditional c t e (Bool_Type.thy:30-35, via SE:364-365). A one-armed
     `if c {t}` fills the else with skip; the frontend `{...}`-path emits `two_armed_conditional c t skip`
     (NOT the one_armed_conditional const), and `skip` is an (input) abbreviation for `literal ()`, so we
     emit `literal ()` (the same builder as UE_Unit). else-if is a nested UE_If -> nested two_armed. *)
  fun mk_two_armed c t e = mk_const \<^const_name>\<open>two_armed_conditional\<close> [c, t, e]

  (* Operator -> HOL const, one row per operator (the frontend's shallow-embedding targets). `+` heads
     with the overloaded urust_add (adhoc-overloaded to word_add_no_wrap); the other arithmetic / shift
     / bitwise ops are the direct Numeric_Types word combinators; comparisons and logical connectives
     are the comp_* / urust_* combinators. Each operand is an elaborated expression, so mk_bin / mk_un
     just apply the const to the elaborated arguments. *)
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

  (* Binder / markup / antiquotation helpers shared with Toy_Lex_Yacc via Parser_Utils (plain
     Isabelle/ML; see that theory). Partially apply the def/ref entity-kind string once -- the call
     sites below are then unchanged. report_def / bind_vars / mark_bound are used internally by
     bind_var / parse_antiq, so only these three are surfaced here. *)
  val vkind       = "urust_var"
  val report_ref  = Parser_Utils.report_ref vkind
  val bind_var    = Parser_Utils.bind_var vkind
  val parse_antiq = Parser_Utils.parse_antiq vkind

  (* Elaborate a binder PATTERN: register its variable(s) and return (a) an abstraction builder that
     wraps the binder's body, and (b) the extended env. The abstraction is the pattern-specific part:
     for a single variable it is `Term.lambda free`; a tuple pattern would `bind_vars` all names and
     wrap with nested lambdas under `case_prod` (etc.). This is the SINGLE pattern-generic seam --
     adding tuple / constructor / wildcard patterns is a case here, and the let/const/match/closure
     elaborators stay unchanged. *)
  fun bind_pat ctxt env (P_Var (x, def_pos)) =
        let val (free, env') = bind_var ctxt env (x, def_pos)
        in (fn body => Term.lambda free body, env') end

  (* env : source name -> { free, def_pos, id } for the enclosing `let` binders (lexical scope). A
     let-bound use resolves to its binder's Free (+ nav markup); it is NOT sent through dispatch --
     lexical scoping wins, matching the frontend's witness-precedence. Non-let names fall through to
     ident_term (dispatch/parse). Capture is by construction: the enclosing Term.lambda abstracts the
     `Free name` this returns (and any `Free name` a nested antiquotation parses). *)
  fun mk ctxt env e =
    (case e of
       UE_Num (n, _)       => mk_literal (HOLogic.mk_number dummyT n)
     | UE_NumSfx (v, w, _) => mk_literal (HOLogic.mk_number (word_typ w) v)
     | UE_Unit _           => mk_literal HOLogic.unit
     | UE_Ident (name, pos) =>
         (case Symtab.lookup env name of
            SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) pos; mk_literal free)
          | NONE => mk_literal (ident_term ctxt name pos))
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
     | UE_Const bnd        => elab_let ctxt env bnd   (* same desugaring as let today (SE:433-434) *))

  (* `let`/`const` <pat> = rhs; body  ->  bind rhs (<pat-abstraction> body). Shared by both so they
     stay DRY while remaining distinct AST nodes (UE_Let / UE_Const). *)
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

text\<open> `micro_rust_expr NAME <src>` parses the source, elaborates to a term, type-checks it once, and
defines NAME := <term>. No attributes (the conformance refl proof uses the primitive NAME_def; we do
not want corpus defs in the global simp set). Serialized behind the shared Parser_Utils.with_parser_lock
(the Isabelle_lex_yacc runtime holds global refs, shared across all ml_lex_yacc parsers). \<close>
ML\<open>
fun define_urust (binding, source) lthy =
  Parser_Utils.with_parser_lock (fn () =>
    (case URust.parse_source lthy source of
       SOME ast =>
         let
           val t = Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
           val ((_, _), lthy') =
             Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
         in lthy' end
     | NONE => error ("micro_rust_expr: empty expression" ^ Position.here (Input.pos_of source))))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>micro_rust_expr\<close>
          "Parse a uRust expression (literal tier) and define it as a HOL constant"
          (Parse.binding -- Parse.input Parse.cartouche >> define_urust)
\<close>

section\<open> Smoke test \<close>

text\<open> A few definitions to confirm the command works in isolation; the real conformance check (against
the frontend's golden terms) lives in Micro_Rust_Parser_Conformance.thy. \<close>
micro_rust_expr smoke_num  \<open> 42 \<close>
micro_rust_expr smoke_sfx  \<open> 1_u32 \<close>
micro_rust_expr smoke_unit \<open> () \<close>
thm smoke_num_def smoke_sfx_def smoke_unit_def

end
