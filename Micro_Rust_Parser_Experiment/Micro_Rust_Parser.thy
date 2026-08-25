(* The custom uRust parser (Phase 1, in progress).

   A real uRust parser built as an ml_lex_yacc lexer + LALR grammar -> reified SML AST -> elaboration
   into the EXISTING shallow terms, exposed as an outer-syntax command `urust_expr NAME <src>`.
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
     * block expressions { stmts } (erase to their body), if / else (two-armed, one-armed, else-if) and
       no-`;` block-like statement sequencing;
     * function calls f(a..) and method calls x.m(a..) (funcallN);
     * match_switch (numeric / wildcard / or-pattern) and match_case (binding patterns: wildcard /
       variable / nullary + single-level constructor, via the Ctr_Sugar case skeleton).
   Deferred (later steps -- notes/urust-parser-plan.md): the reference tier (`*` deref, `&`/`&mut`,
   `=`/compound-assign, `?`), let mut, let/tuple destructuring, the bare `match` keyword + guards /
   disjunction / nested / literal / struct / slice patterns, loops, return, panic!/strings, paths Foo::Bar.

   Technique carried over from Toy_Lex_Yacc: the corrected symbol-position layer (fixed_pos / tokF /
   tok_valF), the antiquotation start-state lexing, dummyT + a single Syntax.check_term, and the
   command mutex. ASCII escape form throughout (isabelle build rejects raw UTF-8 cartouche delimiters). *)

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
  (* Binder pattern. `P_Var` is the irrefutable let/const binder (a single variable). `P_Ident` /
     `P_Constr` are REFUTABLE match-arm patterns (D27): `P_Ident` is a bare id classified in the
     elaborator (via Code.is_constr) as `_` -> wildcard, a nullary constructor, or a variable binder;
     `P_Constr` is `C(args)` (Tier-0: args are P_Ident). The irrefutable let path (bind_pat) and the
     refutable match path (bind_case_pat) BOTH reuse the shared per-variable registration (bind_var /
     bind_vars) but build DIFFERENT abstractions -- a plain lambda for let, the Ctr_Sugar
     case_abs/case_elem skeleton for match -- so they are distinct elaborator clauses, not one shared
     bind_pat. Extending the match pattern set (tuple / nested / literal / guard / disjunction) adds a
     ur_pat constructor + a bind_case_pat clause. *)
  datatype ur_pat =
      P_Var    of string * Position.T                 (* x  (irrefutable let/const binder; name pos) *)
    | P_Ident  of string * Position.T                 (* match arm bare id: `_` / nullary ctor / binder *)
    | P_Constr of string * Position.T * ur_pat list * Position.T  (* C(args); Tier-0 args are P_Ident *)

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

  (* A match_switch arm's key(s) (D26). A numeral pattern -> Some <numeral>; `_` -> None. An or-pattern
     `k1 | k2 | ...` carries multiple keys, each expanding to its own (key, body) pair. `SK_Name` covers
     `_` (wildcard) and, later, const-id / path keys (currently rejected in the elaborator). *)
  datatype ur_switch_key = SK_Num of int * Position.T | SK_Name of string * Position.T

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
    | UE_Call      of string * Position.T * ur_expr list * Position.T
                                                              (* f(a0, ..., aN) -> funcallN f a0 ... aN.
                                                                 The callee is an IDENTIFIER (name, name-pos);
                                                                 resolved in NFunction (call) context, NOT
                                                                 wrapped in `literal`. args, then call-pos.
                                                                 Non-identifier callees (method x.m(a),
                                                                 antiquotation eps<g>(a), turbofish, path)
                                                                 don't parse into this node -- deferred. *)
    | UE_MatchSwitch of ur_expr * (ur_switch_key list * ur_expr) list * Position.T
                                                              (* match_switch scrut { keys => body, ... } ->
                                                                 bind <<scrut>> (ncase_selector
                                                                   [(Some k, <<body>>) ... (None, <<body>>)]).
                                                                 Numeric / wildcard only; NO binders, first-order
                                                                 (D26). An arm = (keys, body); keys > 1 = or-pattern. *)
    | UE_MatchCase of ur_expr * (ur_pat * ur_expr) list * Position.T
                                                              (* match_case scrut { pat => body, ... } ->
                                                                 bind <<scrut>> (\<lambda>anon. case_guard True anon
                                                                   (case_cons B1 ... (case_cons Bn case_nil))),
                                                                 each Bi the Ctr_Sugar case branch for its arm;
                                                                 Case_Translation folds to case_<T> at check_term.
                                                                 Binding patterns (D27): wildcard / var / nullary
                                                                 ctor / single-level ctor with binder|_ args. *)
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
    error ("urust_expr: unexpected input " ^ quote text ^ Position.here pos)
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
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)

(* Parse a suffixed integer literal lexeme, e.g. "0x4_u8" / "1_usize", to (value, width). *)
fun parse_sfx s =
  let
    val (numSS, sfxSS) = Substring.position "_u" (Substring.full s)
    val numstr = Substring.string numSS
    val sfx = Substring.string (Substring.triml 2 sfxSS)   (* drop "_u" *)
    val width = (case sfx of "8" => 8 | "16" => 16 | "32" => 32 | "64" => 64 | "size" => 64
                           | other => raise Fail ("urust_expr: unsupported integer width _u" ^ other))
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
<INITIAL>({digit}+|"0x"{hexdigit}+)"_u"("8"|"16"|"32"|"64"|"size") =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", "", Tokens.NUMSFX, parse_sfx yytext));
<INITIAL>{digit}+ => (tok_valF (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", "", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", "", Tokens.TCONST));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", "", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", "", Tokens.TELSE));
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
%left TDOT    (* method access `.` binds tightest -- tighter than prefix `!` and every binary op:
                 `a + b.m(c)` = `a + (b.m(c))`, `!x.m()` = `!(x.m())`. Resolves the `uexp . TDOT`
                 shift/reduce against operators by precedence (no reported conflict). *)

%term NUM of int | NUMSFX of int * int | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TLET | TCONST | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE | COMMA | TDOT
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG
    | TMATCHSWITCH | TMATCHCASE | TARROW
%nonterm ustart of URust_AST.ur_expr option
       | ustmt of URust_AST.ur_expr
       | uval of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
       | arglist of URust_AST.ur_expr list
       | ublock of URust_AST.ur_expr
       | uif of URust_AST.ur_expr
       | umatchsw of URust_AST.ur_expr
       | swarms of (URust_AST.ur_switch_key list * URust_AST.ur_expr) list
       | swpat of URust_AST.ur_switch_key list
       | umatchcase of URust_AST.ur_expr
       | casearms of (URust_AST.ur_pat * URust_AST.ur_expr) list
       | casepat of URust_AST.ur_pat
       | patargs of URust_AST.ur_pat list
\<close>
yacc_rules\<open>
  ustart : ustmt (SOME ustmt)
         | (NONE)
  (* Statements. A statement is a VALUE expression `uval` (an operand `uexp` OR a with-block control-flow
     expr `uif`), sequenced with `;` -- OR a with-block form (`ublock`/`uif`) in statement position with
     NO trailing `;` followed by more statements (Rust's optional semicolon after a block-like expr; the
     frontend `_urust_sequence_scoping`/`_urust_sequence_if_*`, closing divergence D-2). The no-`;` forms
     desugar to the same `sequence` as an explicit `;` would. Block `{...}` is operand-legal (it is a
     `uexp` atom, frontend priority 1000) AND has a no-`;` statement form -- the `ublock`-as-operand vs
     `ublock ustmt` decision is resolved by lookahead (operator/`;`/`}`/EOF -> operand; a statement-start
     token -> no-`;` sequence). *)
  ustmt : uval                              (uval)
        | uval TSEMI ustmt                  (UE_Seq (uval, ustmt))
        | uval TSEMI                        (UE_Seq (uval, UE_Unit TSEMIleft))
        | ublock ustmt                      (UE_Seq (ublock, ustmt))
        | uif ustmt                         (UE_Seq (uif, ustmt))
        (* NOTE: no `umatchsw ustmt` (no-`;` match_switch statement): the frontend has
           `_urust_sequence_scoping`/`_urust_sequence_if_*` but NO no-`;` sequencing for the `match_switch`
           keyword, so `match_switch … {} stmt` is a frontend PARSE ERROR -- match_switch in statement
           position needs a trailing `;` (via `uval TSEMI ustmt`), matching the frontend. *)
        | TLET IDENT TEQ uval TSEMI ustmt   (UE_Let (P_Var (IDENT, IDENTleft), uval, ustmt))
        | TCONST IDENT TEQ uval TSEMI ustmt (UE_Const (P_Var (IDENT, IDENTleft), uval, ustmt))
  (* Value position: an operand OR a with-block control-flow expr. `uval` is where `if` (and later
     `match`/loops) is admitted -- at let-RHS, condition, call args, and parens -- WITHOUT being a bare
     binary-operator operand (that stays `uexp`, closing divergence D-1). *)
  uval : uexp (uexp)
       | uif  (uif)
       | umatchsw (umatchsw)
       | umatchcase (umatchcase)
  uexp : NUM        (UE_Num (NUM, NUMleft))
       | NUMSFX     (UE_NumSfx (#1 NUMSFX, #2 NUMSFX, NUMSFXleft))
       | IDENT      (UE_Ident (IDENT, IDENTleft))
       | IDENT LPAR RPAR          (UE_Call (IDENT, IDENTleft, [], IDENTleft))
       | IDENT LPAR arglist RPAR  (UE_Call (IDENT, IDENTleft, arglist, IDENTleft))
       (* Method call `recv.m(args)` = a plain call to `m` with the RECEIVER PREPENDED as the first arg
          (SE:380-381,416-417): `x.m(a) = funcall2 m <<x>> <<a>>`, `x.m() = funcall1 m <<x>>`. The method
          name resolves in NFunction (call) context like any callee; the receiver is an ordinary value
          expression. So it desugars into the existing UE_Call node -- no new AST/elaborator machinery.
          Field access `x.f` (no parens) is a DIFFERENT construct (NField/lens) and is deferred (parse
          error here). Postfix on any uexp receiver, so `g(c).f(b)` and chains `x.m().n()` work. *)
       | uexp TDOT IDENT LPAR RPAR         (UE_Call (IDENT, IDENTleft, [uexp], IDENTleft))
       | uexp TDOT IDENT LPAR arglist RPAR (UE_Call (IDENT, IDENTleft, uexp :: arglist, IDENTleft))
       | LPAR RPAR  (UE_Unit LPARleft)
       | LPAR uval RPAR (uval)      (* parens wrap a uval: `(if ...)` becomes a usable operand -- the D-1 escape *)
       | VALAQ      (UE_ValAntiq VALAQ)
       | EXPRAQ     (UE_ExprAntiq EXPRAQ)
       | ublock     (ublock)        (* block STAYS an operand atom (frontend priority 1000): `{e} + x` parses *)
       (* NOTE: `uif` is deliberately NOT a `uexp` alternative -- a with-block control-flow expr is not a
          bare binary-operator operand (closes D-1). It reaches value positions only via `uval`, and
          operand position only when parenthesized (`LPAR uval RPAR`). match / loops will join `uval`. *)
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
     `TIF uexp ublock` the parser shifts TELSE unambiguously. The whole grammar is verified conflict-free
     (zero shift/reduce or reduce/reduce) via the [verbose] grm.desc export; re-check it after any grammar
     change (state count grows with each tier, so it is not pinned here). *)
  ublock : TLBRACE ustmt TRBRACE            (UE_Block (ustmt, TLBRACEleft))
  (* Condition is `uval` (frontend condition priority 20 admits an `if` at 21), so `if if c {..} {..}`
     parses; branches are brace-delimited `ublock`. *)
  uif : TIF uval ublock                     (UE_If (uval, ublock, NONE, TIFleft))
      | TIF uval ublock TELSE ublock        (UE_If (uval, ublock1, SOME ublock2, TIFleft))
      | TIF uval ublock TELSE uif           (UE_If (uval, ublock, SOME uif, TIFleft))
  (* Call argument list, right-nested (source order preserved), mirroring the frontend's
     _urust_args_single / _urust_args_app (Micro_Rust_Syntax.thy:229-232). Conflict-free: the call
     productions are IDENTIFIER-headed (IDENT LPAR ...), so LPAR is never in FOLLOW(uexp) as a postfix
     operator -- no operator-vs-call shift/reduce and no precedence directive needed (cf. Toy_Lex_Yacc). *)
  arglist : uval               ([uval])
          | uval COMMA arglist (uval :: arglist)
  (* match_switch (numeric/wildcard match, D26): a with-block form, so it joins `uval` (value position)
     and the no-`;` statement level -- NOT `uexp` (it is not a bare operator operand, like `if`).
     `scrut { arm, ... }`, each arm `keys => body`; a key is a numeral, `_`, or an or-`|` list. Lowers to
     `bind <<scrut>> (ncase_selector [(Some k, <<body>>) ..])`. The or-`|` reuses the TBAR token (disjoint
     nonterminal context from the bitwise-or operator -- verify conflict-free via grm.desc). *)
  umatchsw : TMATCHSWITCH uval TLBRACE swarms TRBRACE  (UE_MatchSwitch (uval, swarms, TMATCHSWITCHleft))
  swarms : swpat TARROW uval               ([(swpat, uval)])
         | swpat TARROW uval COMMA swarms  ((swpat, uval) :: swarms)
  swpat : NUM               ([SK_Num (NUM, NUMleft)])
        | IDENT             ([SK_Name (IDENT, IDENTleft)])   (* `_` = wildcard; other id -> elaborator errors (const-id keys deferred) *)
        | swpat TBAR swpat  (swpat1 @ swpat2)                (* or-pattern: concatenate the alternatives' keys *)
  (* match_case (binding match, D27): like match_switch a with-block form joining `uval`. Arm patterns
     BIND variables (wildcard `_` / variable / nullary constructor / single-level `C(args)`); lowers to
     the Ctr_Sugar case skeleton (bind + case_guard/case_cons/case_abs/case_elem/case_nil), folded to
     case_<T> at check_term. `casepat`/`patargs` are their OWN nonterminals, disjoint from `uexp` -- so
     a constructor pattern `IDENT LPAR ... RPAR` (only reachable between `{`/COMMA and TARROW) does not
     clash with the `IDENT LPAR arglist RPAR` call production (verify conflict-free via grm.desc). No
     `umatchcase ustmt` no-`;` form: match_case in statement position needs a trailing `;` (like
     match_switch, D26). Nested constructor args / literal / guard / disjunction patterns are gated in
     the elaborator (positioned errors), not the grammar. *)
  umatchcase : TMATCHCASE uval TLBRACE casearms TRBRACE  (UE_MatchCase (uval, casearms, TMATCHCASEleft))
  casearms : casepat TARROW uval                 ([(casepat, uval)])
           | casepat TARROW uval COMMA casearms  ((casepat, uval) :: casearms)
  casepat : IDENT                    (P_Ident (IDENT, IDENTleft))
          | IDENT LPAR patargs RPAR  (P_Constr (IDENT, IDENTleft, patargs, IDENTleft))
  patargs : casepat                  ([casepat])
          | casepat COMMA patargs    (casepat :: patargs)
\<close>

section\<open> Elaborator (AST -> shallow terms) \<close>

text\<open> Each form lowers to the existing shallow HOL const(s): literals -> literal (bare numerals stay
POLYMORPHIC, matching the frontend's open "what type by default"; suffixed literals pin an N word,
alpha-equal to the golden ascribeuN abbreviation); let/const -> bind, sequencing -> sequence; operators
-> the binop_const/unop_const targets; blocks ERASE to their body; if/else -> two_armed_conditional.
Everything is built with dummyT; a single Syntax.check_term runs in the command. \<close>
ML\<open>
structure URust_Translate =
struct
  open URust_AST

  (* All Core terms are built with dummyT; a single Syntax.check_term (in the command) resolves types. *)
  fun mk_const name args = Term.list_comb (Const (name, dummyT), args)
  fun mk_literal v = mk_const \<^const_name>\<open>literal\<close> [v]

  (* Arity -> the funcallN const for a call `f(a0,...,a{N-1})` -> funcallN f a0 ... a{N-1}. Cap is 14
     (NOT 16): Core_Expression defines funcall0..16, but Core_Syntax wires the surface `_urust_shallow_fun_*`
     lowering only up to funcall14, so the frontend `<<...>>` produces no golden beyond 14 -- a >14 call has
     nothing to conform against. Hand-enumerated so each const name is compile-checked. (TODO: a generic
     `funcall<n>`-with-declared-check would drop the table and auto-track the backend family;
     notes/claude/urust-todos.md.) *)
  fun funcall_const _   0  = \<^const_name>\<open>funcall0\<close>
    | funcall_const _   1  = \<^const_name>\<open>funcall1\<close>
    | funcall_const _   2  = \<^const_name>\<open>funcall2\<close>
    | funcall_const _   3  = \<^const_name>\<open>funcall3\<close>
    | funcall_const _   4  = \<^const_name>\<open>funcall4\<close>
    | funcall_const _   5  = \<^const_name>\<open>funcall5\<close>
    | funcall_const _   6  = \<^const_name>\<open>funcall6\<close>
    | funcall_const _   7  = \<^const_name>\<open>funcall7\<close>
    | funcall_const _   8  = \<^const_name>\<open>funcall8\<close>
    | funcall_const _   9  = \<^const_name>\<open>funcall9\<close>
    | funcall_const _   10 = \<^const_name>\<open>funcall10\<close>
    | funcall_const _   11 = \<^const_name>\<open>funcall11\<close>
    | funcall_const _   12 = \<^const_name>\<open>funcall12\<close>
    | funcall_const _   13 = \<^const_name>\<open>funcall13\<close>
    | funcall_const _   14 = \<^const_name>\<open>funcall14\<close>
    | funcall_const pos n  =
        error ("urust_expr: unsupported call arity " ^ string_of_int n ^
               " (max 14; the frontend's surface lowering caps here)" ^ Position.here pos)

  fun word_typ 8  = \<^typ>\<open>8 word\<close>
    | word_typ 16 = \<^typ>\<open>16 word\<close>
    | word_typ 32 = \<^typ>\<open>32 word\<close>
    | word_typ 64 = \<^typ>\<open>64 word\<close>            (* u64 and usize (usize -> 64 in parse_sfx) *)
    | word_typ w  = error ("urust_expr: unsupported integer width u" ^ string_of_int w)

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
     frontend; a context-fixed FREE gets colour + ctrl-click-to-its-`fixes` (see below); a genuine
     (unfixed) free gets plain Markup.free.

     FREE-VARIABLE NAVIGATION (context-fixed frees). The frontend gives ctrl-click nav for a
     context-fixed free `foo` -> its `fixes` declaration. That nav comes from `Syntax_Phases.markup_free`
     (Variable.markup_fixed = the entity ref markup + Variable.markup = the colour), reported by
     `decode_term` during check. In OUR pipeline the final check_term DOES run decode_term, but it emits
     that markup at Position.none: we hand `Syntax.parse_term` a bare `name` string with no source
     position, so the parsed Free carries no position and the auto-report is dropped -- exactly why D14/D15
     re-emit markup manually here at the real `pos`. Previously this branch emitted only Markup.free
     (colour), losing the nav. Fix: reproduce decode_term's Free case verbatim (syntax_phases.ML:304-313)
     -- intern the source name via `Proof_Context.lookup_free`; if fixed, report every markup in
     `Syntax_Phases.markup_free ctxt x` at `pos` (nav entity + colour); if not fixed, plain Markup.free.
     Reuses the frontend mechanism rather than hand-rolling the entity markup.

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

  (* Resolve a bare identifier in a dispatch CONTEXT (`kind`): NLiteral for a value-position id,
     NFunction for a call callee. Same markup logic for both (registered -> dispatch marker; unregistered
     Const -> const nav; context-fixed free -> markup_free nav; else Markup.free). The CALLER decides the
     `literal` wrapper (value position wraps; a call callee does NOT). *)
  fun ident_term ctxt kind name pos =
    (case Micro_Rust_Names.lookups ctxt kind name of
       [] =>
         let val t = Syntax.parse_term ctxt name in
           (case ident_leaf t of
              Const (c, _) =>
                Context_Position.report ctxt pos
                  (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
            | Free (a, _) =>
                (* decode_term's Free case (syntax_phases.ML:304-313): intern the source name; a
                   context-fixed free reports markup_free = [markup_fixed (ctrl-click nav to the
                   `fixes`), markup (colour)]; a genuine free just Markup.free. *)
                (case Proof_Context.lookup_free ctxt a of
                   SOME x =>
                     List.app (Context_Position.report ctxt pos)
                       (Syntax_Phases.markup_free ctxt x)
                 | NONE => Context_Position.report ctxt pos Markup.free)
            | _ => Context_Position.report ctxt pos Markup.free);
           t
         end
     | _  => Micro_Rust_Dispatch.mk_marker kind name pos (Free (name, dummyT)))

  (* Classify a bare match-pattern identifier as a data constructor (reproducing the frontend's
     resolve_constructor_id, SE:960-988): intern the name and test Code.is_constr -- the SAME oracle the
     frontend uses. A constructor resolves to its RAW Const (NOT the lift_fun1 value embedding a value-
     position id would get via ident_term/NLiteral -- a pattern head must be the bare constructor); a
     non-constructor id (`y`, `_`) yields NONE and is a variable binder. Used only by bind_case_pat. *)
  fun resolve_ctor ctxt name =
    let val thy = Proof_Context.theory_of ctxt in
      (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
         SOME (Const (full, _)) => if Code.is_constr thy full then SOME (Const (full, dummyT)) else NONE
       | _ => NONE)
    end

  (* Report the const ENTITY markup (colour + ctrl-click-to-definition) for a resolved pattern
     constructor at its name position — the SAME `Name_Space.markup` ident_term emits for a resolved HOL
     Const, so a match-arm constructor head (`Some`, `None`, `Ok`, `Err`, a user `datatype` ctor)
     navigates to its declaration like any other const. `resolve_ctor` stays pure (it is also used only to
     CLASSIFY, in `binder_names`); the markup is emitted once, here, when a branch actually resolves the
     head — not during classification. *)
  fun report_ctor_markup ctxt pos (Const (c, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
    | report_ctor_markup _ _ _ = ()

  (* A wildcard `_` binds nothing referenceable, so bind_var's colour/nav do not apply; still emit a
     typing tooltip at its position so ctrl-hover identifies it (the same Markup.typing channel tokF uses
     for a token's kind string, e.g. `=` -> " :: TEQ") instead of falling through to the enclosing command
     span. `pos` is the IDENT token's full range (tok_ident builds it, so IDENTleft spans the whole `_`). *)
  fun report_wildcard ctxt pos = Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

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

  (* match_switch scrut { keys => body, ... } -> bind <<scrut>> (ncase_selector <list of (key, body) pairs>)
     (D26; SE:829-830, Core_Syntax.thy:655-685, Num_Case_Expression.thy). A numeral key -> Some <numeral>,
     `_` -> None; an or-pattern's keys each get their own pair with the SAME body. First-order: no binders,
     no case skeleton. `ncase_selector` is reachable via the Micro_Rust_Shallow_Embedding import. *)
  fun mk_some v = mk_const \<^const_name>\<open>Option.Some\<close> [v]
  val mk_none   = Const (\<^const_name>\<open>Option.None\<close>, dummyT)
  fun mk_pair a b = mk_const \<^const_name>\<open>Product_Type.Pair\<close> [a, b]
  fun mk_cons h t = mk_const \<^const_name>\<open>List.Cons\<close> [h, t]
  val mk_nil      = Const (\<^const_name>\<open>List.Nil\<close>, dummyT)
  fun mk_ncase_selector lst = mk_const \<^const_name>\<open>ncase_selector\<close> [lst]

  (* Ctr_Sugar case skeleton (match_case, D27). case_guard / case_cons / case_nil / case_elem / case_abs
     are the uninterpreted HOL markers (HOL.Ctr_Sugar; no defining equations). The Case_Translation
     term-check phase folds a well-formed `case_guard True scrut (case_cons ... case_nil)` tree into the
     datatype's concrete `case_<T>` combinator DURING our single Syntax.check_term -- so we build exactly
     the skeleton the frontend builds and never construct case_option / case_result ourselves
     (SE:780-830, Core_Syntax.thy:688-1137, Basic_Case_Expression.thy:113-350). *)
  fun mk_case_guard b s cs = mk_const \<^const_name>\<open>case_guard\<close> [b, s, cs]
  fun mk_case_cons h t     = mk_const \<^const_name>\<open>case_cons\<close> [h, t]
  val mk_case_nil          = Const (\<^const_name>\<open>case_nil\<close>, dummyT)
  fun mk_case_elem p b     = mk_const \<^const_name>\<open>case_elem\<close> [p, b]
  fun mk_case_abs f        = mk_const \<^const_name>\<open>case_abs\<close> [f]

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
    | bind_pat _ _ p =
        error ("urust_expr: refutable pattern in an irrefutable (let/const) binder position" ^
               (case p of P_Ident (_, q) => Position.here q | P_Constr (_, q, _, _) => Position.here q
                        | P_Var (_, q) => Position.here q))

  (* Elaborate a REFUTABLE match-arm pattern (D27) into a Ctr_Sugar case branch. Reuses bind_var (the
     shared per-variable registration -- markup / click-to-def / capture) but, UNLIKE bind_pat (the
     irrefutable let binder, a plain lambda), builds the case_abs/case_elem skeleton. Returns (a branch
     builder taking the elaborated arm body, extended env). Tier-0 patterns: wildcard `_`, variable
     binder, nullary constructor, single-level constructor with binder/`_` args; nested-constructor args,
     let-patterns, and (grammar-unreachable today) other shapes raise positioned errors. Fresh wildcard
     binders are named from a Name.context seeded with this pattern's binder names (+ the proof context),
     so `_` never collides with a sibling binder (mirrors the frontend's collect_ids_from_pattern). *)
  fun bind_case_pat ctxt env pat =
    let
      fun binder_names (P_Ident (a, _)) =
            if a = "_" then [] else (case resolve_ctor ctxt a of SOME _ => [] | NONE => [a])
        | binder_names (P_Constr (_, _, args, _)) = maps binder_names args
        | binder_names (P_Var (a, _)) = [a]
      val names0 = fold Name.declare (binder_names pat) (Variable.names_of ctxt)
      fun fresh names = let val (n, names') = Name.variant "uu" names in (Free (n, dummyT), names') end
    in
      (case pat of
         P_Ident ("_", pos) =>
           (report_wildcard ctxt pos;
            let val (f, _) = fresh names0
            in (fn body => mk_case_abs (Term.lambda f (mk_case_elem f body)), env) end)
       | P_Ident (name, pos) =>
           (case resolve_ctor ctxt name of
              SOME c => (report_ctor_markup ctxt pos c;                      (* nullary constructor *)
                         (fn body => mk_case_elem c body, env))
            | NONE =>                                                        (* variable binder *)
                let val (f, env') = bind_var ctxt env (name, pos)
                in (fn body => mk_case_abs (Term.lambda f (mk_case_elem f body)), env') end)
       | P_Constr (name, pos, args, _) =>
           (case resolve_ctor ctxt name of
              NONE => error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^ Position.here pos)
            | SOME c =>
                let
                  val _ = report_ctor_markup ctxt pos c
                  fun arg (P_Ident ("_", pos)) (env, names) =
                        (report_wildcard ctxt pos;
                         let val (f, names') = fresh names in (f, (env, names')) end)
                    | arg (P_Ident (a, ap)) (env, names) =
                        (case resolve_ctor ctxt a of
                           SOME _ => error ("urust_expr: nested nullary-constructor pattern `" ^ a ^
                                       "` not yet supported (Tier-0: binder / `_` constructor args only)" ^
                                       Position.here ap)
                         | NONE => let val (f, env') = bind_var ctxt env (a, ap) in (f, (env', names)) end)
                    | arg (P_Constr (_, _, _, cp)) _ =
                        error ("urust_expr: nested constructor pattern not yet supported (Tier-0)" ^
                               Position.here cp)
                    | arg (P_Var (_, vp)) _ =
                        error ("urust_expr: unexpected let-pattern in a match arm" ^ Position.here vp)
                  val (frees, (env', _)) = fold_map arg args (env, names0)
                  val pat_term = Term.list_comb (c, frees)
                in
                  (fn body => fold_rev (fn f => fn t => mk_case_abs (Term.lambda f t)) frees
                                (mk_case_elem pat_term body), env')
                end))
    end

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
         (* f(a0,...,a{N-1}) -> funcallN func <<a0>> ... <<a{N-1}>>  (Core_Syntax.thy:503-587).
            The callee `func` resolves in NFunction (call) context and is NOT wrapped in `literal`:
            a let-bound callee -> its env Free (+ nav); else ident_term NFunction (registered call
            notation -> dispatch marker; unregistered -> parse_term = fixed Free / Const). Args are
            ordinary value expressions (mk), so nested calls f(g(c),b) fall out of the recursion. *)
         let
           val func =
             (case Symtab.lookup env name of
                SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) npos; free)
              | NONE => ident_term ctxt Micro_Rust_Names.NFunction name npos)
         in mk_const (funcall_const cpos (length args)) (func :: map (mk ctxt env) args) end
     | UE_MatchSwitch (scrut, arms, _) =>
         (* bind <<scrut>> (ncase_selector [(Some k0, <<e0>>), ..., (None, <<en>>)]). A numeral key ->
            Some <numeral>; `_` -> None; a non-`_` identifier key is a const-id/path (deferred) -> error.
            An or-pattern's keys each pair with the SAME (elaborated-once) body. *)
         let
           fun key (SK_Num (n, _))       = mk_some (HOLogic.mk_number dummyT n)
             | key (SK_Name ("_", pos))  = (report_wildcard ctxt pos; mk_none)
             | key (SK_Name (s, pos))    =
                 error ("urust_expr: unsupported match_switch key " ^ quote s ^
                        " (numeral or `_` only; const-id / path keys not yet supported)" ^ Position.here pos)
           fun arm_pairs (keys, body) =
             let val b = mk ctxt env body in map (fn k => mk_pair (key k) b) keys end
           val lst = fold_rev mk_cons (maps arm_pairs arms) mk_nil
         in mk_bind (mk ctxt env scrut) (mk_ncase_selector lst) end
     | UE_MatchCase (scrut, arms, _) =>
         (* bind <<scrut>> (\<lambda>anon. case_guard True anon (case_cons B1 ... (case_cons Bn case_nil))),
            each Bi the Ctr_Sugar case branch for its arm, its body elaborated in the pattern-extended
            env' (the scrutinee stays in the OUTER env, mirroring elab_let). Case_Translation folds the
            skeleton to case_<T> at check_term (D27). The `anon` scrutinee binder is named to avoid the
            branches' free names (so it can never capture); its name is alpha-irrelevant to `refl`. *)
         let
           fun arm (pat, body) =
             let val (absf, env') = bind_case_pat ctxt env pat
             in absf (mk ctxt env' body) end
           val branches = fold_rev (fn a => fn acc => mk_case_cons (arm a) acc) arms mk_case_nil
           val anon =
             Free (singleton (Name.variant_list (Term.add_free_names branches [])) "anon_case", dummyT)
         in
           mk_bind (mk ctxt env scrut)
             (Term.lambda anon (mk_case_guard \<^term>\<open>True\<close> anon branches))
         end)

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

text\<open> `urust_expr NAME <src>` parses the source, elaborates to a term, type-checks it once, and
defines NAME := <term>. No attributes (the conformance refl proof uses the primitive NAME_def; we do
not want corpus defs in the global simp set). Serialized behind the shared Parser_Utils.with_parser_lock
(the Isabelle_lex_yacc runtime holds global refs, shared across all ml_lex_yacc parsers). \<close>
ML\<open>
fun define_urust (binding, source) lthy =
  (* Only `parse_source` touches the Isabelle_lex_yacc global refs (src/ctxt/the_src), so ONLY it is
     serialized. Elaboration (mk_closed, incl. its Syntax.parse_term calls), check_term, and define are
     pure w.r.t. those globals -- holding the lock across them would needlessly serialize the (slower)
     type-checking of every urust_expr theory-wide, throttling parallel checking at corpus scale. *)
  (case Parser_Utils.with_parser_lock (fn () => URust.parse_source lthy source) of
     SOME ast =>
       let
         val t = Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
         val ((_, _), lthy') =
           Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
       in lthy' end
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

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
