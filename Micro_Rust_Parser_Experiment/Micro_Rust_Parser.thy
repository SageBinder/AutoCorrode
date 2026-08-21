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
     * let / const bindings and statement sequencing (`;`, trailing `;`).
   Deferred (later steps -- notes/urust-parser-plan.md): operators, let mut, tuple/constructor patterns,
   blocks { }, if / match / loops, calls, return, panic!/strings, paths Foo::Bar.

   Technique carried over from Toy_Lex_Yacc: the corrected symbol-position layer (fixed_pos / tokF /
   tok_valF), the antiquotation start-state lexing, dummyT + a single Syntax.check_term, and the
   command mutex. ASCII escape form throughout (isabelle build rejects raw UTF-8 cartouche delimiters). *)

theory Micro_Rust_Parser
  imports
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
    "Isabelle_Lex-Yacc.LexYacc"
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
end
\<close>

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> typing / sorting \<close>

section\<open> Lexer + grammar \<close>

text\<open> No infix operators at this tier, so no precedence is needed. The antiquotation brackets are the
Isabelle symbols \<open>\<llangle>\<close>/\<open>\<rrangle>\<close> (value escape) and \<open>\<epsilon>\<close> + \<open>\<open>\<close>/\<open>\<close>\<close>
(expression escape); each is matched by an explicit escape rule and its body captured with a start
state, without lexing the HOL inside. The fixed_pos / tokF / tok_valF layer is copied from
Toy_Lex_Yacc (it corrects the per-character-vs-per-symbol position drift). \<close>
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
    val width = (case sfx of "8" => 8 | "16" => 16 | "32" => 32 | "64" => 64 | _ => 64)
    val value =
      if String.isPrefix "0x" numstr
      then valOf (StringCvt.scanString (Int.scan StringCvt.HEX) (String.extract (numstr, 2, NONE)))
      else valOf (Int.fromString numstr)
  in (value, width) end

(* Corrected position mapping (see Toy_Lex_Yacc): map the per-CHARACTER yypos to the position of the
   containing Isabelle symbol, so markup after a multi-char escape does not drift. *)
val the_src = ref (Input.string "")
fun set source ctxt = (Isabelle_lex_yacc.set source ctxt; the_src := source)

fun inner_syms () =
  let val syms = Input.source_explode (!the_src)
  in if length syms >= 2 then List.take (tl syms, length syms - 2) else syms end

fun fixed_pos yypos =
  let
    val syms = inner_syms ()
    val target = yypos - 1
    fun go _ [] = Input.pos_of (!the_src)
      | go _ [(_, p)] = p
      | go acc ((s, p) :: rest) = if target < acc + size s then p else go (acc + size s) rest
  in
    if null syms then Input.pos_of (!the_src)
    else if target < 0 then #2 (hd syms)
    else go 0 syms
  end

fun report_fixed (yypos, len, markup, typ, sort) =
  if 0 < len then
    (* End of the range is start_offset + len, NOT a second fixed_pos (yypos + len): the latter maps
       to the symbol FOLLOWING the token, so its result depends on the trailing character (leaving the
       token's last char uncoloured, and shifting with trailing whitespace). These tokens are ASCII,
       so symbol count = len and end_offset is exclusive. *)
    let
      val {line, offset, props, ...} = Position.dest (fixed_pos yypos)
      val p = Position.make {line = line, offset = offset, end_offset = offset + len, props = props}
    in Position.report p markup;
       Position.report_text p Markup.typing typ;
       Position.report_text p Markup.sorting sort
    end
  else ()

fun tokF (yypos, yytext, markup, typ, sort, cons) =
  (report_fixed (yypos, size yytext, markup, typ, sort);
   cons (fixed_pos yypos, fixed_pos (yypos + size yytext)))

fun tok_valF (yypos, yytext, markup, typ, sort, cons, value) =
  (report_fixed (yypos, size yytext, markup, typ, sort);
   cons (value, fixed_pos yypos, fixed_pos yypos))

(* Identifier token: carry a FULL-RANGE position (not a start point) and emit NO colour markup here.
   Colouring an identifier is deferred to the elaborator (URust_Translate.ident_term), which alone
   knows whether the name resolves to a registered notation (const-styling via the dispatch resolver),
   a HOL constant, or a free variable -- so exactly one, correctly-ranged markup is produced per
   identifier. Emitting Markup.free eagerly here (as the other tokens do) caused a split highlight on
   registered names: our free markup covered the whole token while the resolver's const-styling was
   anchored to the token's start point. *)
fun tok_ident (yypos, yytext) =
  let
    (* Build the full-range position from the START position's offset plus the token length, rather
       than a second fixed_pos (yypos + size) for the end: the latter's result depends on the symbol
       that FOLLOWS the token, which left the last identifier char uncoloured (and shifted with
       trailing whitespace). Identifiers are ASCII, so symbol count = String.size, and end_offset is
       exclusive (offset of the symbol just past the token). *)
    val {line, offset, props, ...} = Position.dest (fixed_pos yypos)
    val p = Position.make {line = line, offset = offset, end_offset = offset + size yytext, props = props}
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
<INITIAL>"="      => (tokF (yypos, yytext, Markup.keyword2, "TEQ", "", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", "", Tokens.TSEMI));
<INITIAL>{idstart}{idchar}* => (tok_ident (yypos, yytext));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "LPAR", "", Tokens.LPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "RPAR", "", Tokens.RPAR));
<INITIAL>\\"<llangle>"          => (aq_buf := ""; aq_pos := yypos; aq_start := yypos + size yytext; YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (aq_buf := ""; aq_pos := yypos; aq_start := yypos + size yytext; YYBEGIN EAQ; lex());
<INITIAL>.        => (lex());
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

%term NUM of int | NUMSFX of int * int | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TLET | TCONST | TEQ | TSEMI | EOF
%nonterm ustart of URust_AST.ur_expr option
       | ustmt of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
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
       | VALAQ      (UE_ValAntiq VALAQ)
       | EXPRAQ     (UE_ExprAntiq EXPRAQ)
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

  fun mk_literal v = Const (\<^const_name>\<open>literal\<close>, dummyT) $ v

  fun word_typ 8  = \<^typ>\<open>8 word\<close>
    | word_typ 16 = \<^typ>\<open>16 word\<close>
    | word_typ 32 = \<^typ>\<open>32 word\<close>
    | word_typ _  = \<^typ>\<open>64 word\<close>   (* 64 and usize *)

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
     frontend; anything else (a context-fixed / genuine free) gets Markup.free. *)
  fun ident_term ctxt name pos =
    (case Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral name of
       [] =>
         let val t = Syntax.parse_term ctxt name in
           (case Term_Position.strip_positions t of
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
  fun mk_bind e f     = Const (\<^const_name>\<open>Core_Expression.bind\<close>, dummyT) $ e $ f
  fun mk_sequence a b = Const (\<^const_name>\<open>Core_Expression.sequence\<close>, dummyT) $ a $ b

  (* Click-to-definition for `let`-bound variables (mirrors Toy_Lex_Yacc / D16): a `def` entity markup
     at the binder and a `ref` at each use sharing a serial, so ctrl-click on a use jumps to its `let`. *)
  val urust_varN = "urust_var"
  (* A `let`/`const`-bound name (binder + uses) is coloured GREEN (Markup.bound) -- like Isabelle's own
     bound variables and the frontend's resolve_bound -- plus a def/ref entity pair for ctrl-click nav.
     tok_ident emits no colour, so this is the only markup on the identifier (no split/conflict). *)
  fun report_def ctxt id (x, def_pos) =
    (Context_Position.report ctxt def_pos Markup.bound;
     Context_Position.report ctxt def_pos (Position.make_entity_markup {def = true} id urust_varN (x, def_pos)))
  fun report_ref ctxt id (x, def_pos) use_pos =
    (Context_Position.report ctxt use_pos Markup.bound;
     Context_Position.report ctxt use_pos (Position.make_entity_markup {def = false} id urust_varN (x, def_pos)))

  (* Register a binder occurrence: fresh serial, def markup at its name position, env entry; returns
     (its Free, the extended env). Binder-GENERIC -- EVERY binding construct should go through this
     (`let`/`const` today; future closures / for-loops / match patterns), so colour, click-to-def,
     capture, and antiquotation handling are uniform, not per-construct. *)
  fun bind_var ctxt env (x, def_pos) =
    let
      val id   = serial ()
      val _    = report_def ctxt id (x, def_pos)
      val free = Free (x, dummyT)
    in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

  (* Multi-variable binders (tuple `let (a, b) = …`, a match arm `Some(x, y) => …`) register EACH
     bound variable through bind_var, threading the env; this returns the Frees (binder order) and the
     env extended with all of them. Colour / click-to-def / capture / antiquotation handling then work
     for every variable uniformly. NOTE: this is only the per-variable REGISTRATION; how the N Frees
     are abstracted into the term (nested Term.lambda, case_prod, a pattern combinator, …) is
     necessarily construct-specific and is the binder's own job. *)
  fun bind_vars ctxt xps env = fold_map (fn xp => fn e => bind_var ctxt e xp) xps env

  (* Elaborate a binder PATTERN: register its variable(s) and return (a) an abstraction builder that
     wraps the binder's body, and (b) the extended env. The abstraction is the pattern-specific part:
     for a single variable it is `Term.lambda free`; a tuple pattern would `bind_vars` all names and
     wrap with nested lambdas under `case_prod` (etc.). This is the SINGLE pattern-generic seam --
     adding tuple / constructor / wildcard patterns is a case here, and the let/const/match/closure
     elaborators stay unchanged. *)
  fun bind_pat ctxt env (P_Var (x, def_pos)) =
        let val (free, env') = bind_var ctxt env (x, def_pos)
        in (fn body => Term.lambda free body, env') end

  (* Colour every enclosing bound variable GREEN + click-to-def wherever it occurs in an antiquotation
     body --
     at ANY depth (`⟪x⟫`, `⟪x + 1⟫`, `ε‹f x›`). Syntax.parse_term gives the correct term and full
     inner-HOL highlighting, but colours a captured variable blue: it parses the body in isolation,
     unaware of the µRust binder. So after parsing we overlay Markup.bound at each bound-variable
     occurrence, computed from the body's OWN per-symbol positions (Input.source_explode) -- no position
     surgery, general for arbitrary bodies. Reported after the parse, it is the innermost markup and so
     wins over parse_term's blue (Rendering.select picks the innermost). Markup-only: the term is
     exactly parse_term's, so capture / conformance is unaffected. *)
  fun mark_bound ctxt env src =
    let
      fun is_start c = Symbol.is_ascii_letter c orelse c = "_"
      fun is_cont c  = is_start c orelse Symbol.is_ascii_digit c
      fun span [] = ([], [])
        | span (sp :: r) =
            if is_cont (#1 sp) then let val (a, b) = span r in (sp :: a, b) end else ([], sp :: r)
      fun go [] = ()
        | go (sp :: r) =
            if is_start (#1 sp) then
              let
                val (idsyms, rest) = span (sp :: r)
                val nm = Symbol_Pos.content idsyms
              in
                (case Symtab.lookup env nm of
                   SOME {def_pos, id, ...} =>   (* green + click-to-def, like an ordinary bound use *)
                     report_ref ctxt id (nm, def_pos) (Position.range_position (Symbol_Pos.range idsyms))
                 | NONE => ());
                go rest
              end
            else go r
    in go (Input.source_explode src) end

  fun parse_antiq ctxt env src =
    let val t = Syntax.parse_term ctxt (Syntax.implode_input src)
    in mark_bound ctxt env src; t end

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
not want corpus defs in the global simp set). Serialized behind a mutex (the runtime holds global
refs). \<close>
ML\<open>
val urust_lock = Synchronized.var "urust_lock" ()
fun with_urust_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result urust_lock (fn () => (f (), ()))

fun define_urust (binding, source) lthy =
  with_urust_lock (fn () =>
    (case URust.parse_source lthy source of
       SOME ast =>
         let
           val t = Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
           val ((_, _), lthy') =
             Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
         in lthy' end
     | NONE => error "micro_rust_expr: failed to parse expression"))

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
