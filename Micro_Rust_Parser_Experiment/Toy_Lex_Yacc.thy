(* Toy_Lex_Yacc: a self-contained ml_lex_yacc toy language, kept as a permanent sandbox and debugging
   reference for the custom uRust parser (Micro_Rust_Parser.thy). This is NOT uRust -- it is a small
   integer expression language that demonstrates, end to end, the techniques the real parser uses:

     * parse -> reified SML AST -> HOL term -> Local_Theory.define, built with dummyT and resolved by
       a single Syntax.check_term, serialized behind a command mutex (the Isabelle_lex_yacc runtime
       holds global refs);
     * `let x = e; e` binders closed with a source-named Free + Term.lambda (capture-safe and
       shadowing-correct);
     * <<HOL>> antiquotations captured as a POSITIONED Input.source (so the inner HOL is
       syntax-highlighted) whose free variables are captured by an enclosing binder; and deferred
       name resolution -- an unbound identifier becomes a dummyT Free resolved by the final
       check_term against the surrounding HOL context;
     * the grammar mechanics the real parser needs: a UNARY operator sharing a token with a binary
       one (unary vs binary `-`), disambiguated by a %prec override on a pseudo-terminal (UMINUS, a la
       Pascal's UNARYSIGN); precedence-directive disambiguation that keeps the LALR construction
       conflict-free (replacing hand-tuned mixfix priorities); and comma-separated function-call
       argument lists lowered to an APPLIED HEAD (Free f $ a1 $ ... $ aN via Term.list_comb) -- the
       shape the real elaborator uses for funcallN;
     * the corrected symbol-position layer (fixed_pos / tokF / tok_valF) that keeps PIDE markup
       aligned when the source contains multi-char Isabelle-symbol escapes.

   NOTE ON ENCODING: ASCII escape form for Isabelle symbols (\<open> / \<close> etc.), NOT raw UTF-8
   glyphs -- `isabelle build` rejects raw UTF-8 cartouche delimiters even though ic2/PIDE tolerates
   them. See notes/urust-parser-plan.md and notes/isabelle-lex-yacc-notes.md. *)

theory Toy_Lex_Yacc
  imports "Isabelle_Lex-Yacc.LexYacc"
  keywords
    "toy_def" :: thy_decl
    and "toy_demo_inspect" :: diag
begin

section\<open> Toy: unary %prec, precedence-directive disambiguation, and comma-argument calls \<close>

text\<open> The reified AST: numerals, variables, antiquotations, unary minus (E_Neg), binary +/-/*
(E_Add/E_Sub/E_Mul), `let` (E_Let), and a function call (E_Call) -- a head applied to an argument
list. \<close>
ML\<open>
structure Toy_AST =
struct
  datatype expr =
      E_Num  of int * Position.T
    | E_Var  of string * Position.T
    | E_Antiq of Input.source          (* the <<...>> body as a POSITIONED source (for inner markup) *)
    | E_Neg  of expr * Position.T
    | E_Add  of expr * expr
    | E_Sub  of expr * expr
    | E_Mul  of expr * expr
    | E_Let  of string * expr * expr * Position.T
    | E_Call of string * expr list * Position.T   (* f(a1, ..., aN) *)
end
\<close>

SML_import \<open> structure Toy_AST = Toy_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>   \<comment>\<open> re-import for the position map (idempotent) \<close>

text\<open> Lexer. The corrected fixed_pos / tokF / tok_valF position layer (below) keeps PIDE markup
aligned across multi-char Isabelle-symbol escapes; those helpers are local to this generated lexer. \<close>
ml_lex_yacc "Toy" where
lex_user_declarations\<open>
val aq_buf = ref ""
val aq_pos = ref 0
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)

(* Corrected position mapping: map the per-CHARACTER yypos to the position of the containing Isabelle
   symbol, so markup after a multi-char escape does not drift. (The framework's own get_pos indexes a
   per-symbol vector with the per-character yypos, which drifts.) *)
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

(* Identifier token: carry a FULL-RANGE position (offset + length) but emit NO colour here. The lexer
   cannot tell a `let` binder / bound use (green, Markup.bound) from a genuine free (blue, Markup.free);
   only the elaborator knows the role, so it colours each identifier (see Toy_Translate). The full range
   makes both the colour and the click-to-definition entity markup cover the whole identifier. *)
fun tok_id (yypos, yytext) =
  let
    val {line, offset, props, ...} = Position.dest (fixed_pos yypos)
    val p = Position.make {line = line, offset = offset, end_offset = offset + size yytext, props = props}
  in Tokens.TID (yytext, p, p) end
\<close>
lex_definitions\<open>
%s AQ;
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
<INITIAL>\n       => (lex());
<INITIAL>{ws}+    => (lex());
<INITIAL>{digit}+ => (tok_valF (yypos, yytext, Markup.numeral, "TNUM", "", Tokens.TNUM, valOf (Int.fromString yytext)));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", "", Tokens.TLET));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.keyword2, "TEQ", "", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", "", Tokens.TSEMI));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "TCOMMA", "", Tokens.TCOMMA));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.keyword2, "TPLUS", "", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.keyword2, "TMINUS", "", Tokens.TMINUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.keyword2, "TTIMES", "", Tokens.TTIMES));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "TLPAR", "", Tokens.TLPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "TRPAR", "", Tokens.TRPAR));
<INITIAL>{alpha}({alpha}|{digit})* => (tok_id (yypos, yytext));
<INITIAL>\\"<llangle>" => (aq_buf := ""; aq_pos := yypos; aq_start := yypos + size yytext; YYBEGIN AQ; lex());
<INITIAL>.        => (lex());
<AQ>\\"<rrangle>"   => (YYBEGIN INITIAL;
    let val p = fixed_pos (!aq_start) val q = fixed_pos yypos
    in Tokens.TAQ (Input.source true (!aq_buf) (Position.range (p, q)), p, q) end);
<AQ>\n            => (aq_buf := !aq_buf ^ "\n"; lex());
<AQ>.             => (aq_buf := !aq_buf ^ yytext; lex());
\<close>
and yacc_user_declarations\<open>
open Toy_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

(* Precedence, lowest to highest. UMINUS is a pseudo-terminal (it appears only after %prec) used to
   give unary minus its own precedence -- tighter than * so `-a*b` parses as `(-a)*b`. This is the
   Pascal UNARYSIGN idiom: declare the pseudo-terminal in %term, give it a precedence line, and
   reference it with %prec on the unary rule. *)
%left TPLUS TMINUS
%left TTIMES
%left UMINUS

%term TNUM of int | TID of string | TAQ of Input.source
    | TLET | TEQ | TSEMI | TCOMMA
    | TPLUS | TMINUS | TTIMES | TLPAR | TRPAR | UMINUS | EOF
%nonterm tstart of Toy_AST.expr option
       | texp of Toy_AST.expr
       | targs of Toy_AST.expr list
\<close>
yacc_rules\<open>
  tstart : texp (SOME texp)
         | (NONE)
  texp : TNUM                          (E_Num (TNUM, TNUMleft))
       | TID                           (E_Var (TID, TIDleft))
       | TAQ                           (E_Antiq TAQ)
       | TMINUS texp %prec UMINUS      (E_Neg (texp, TMINUSleft))
       | texp TPLUS texp               (E_Add (texp1, texp2))
       | texp TMINUS texp              (E_Sub (texp1, texp2))
       | texp TTIMES texp              (E_Mul (texp1, texp2))
       | TLPAR texp TRPAR              (texp)
       | TID TLPAR TRPAR               (E_Call (TID, [], TIDleft))
       | TID TLPAR targs TRPAR         (E_Call (TID, targs, TIDleft))
       | TLET TID TEQ texp TSEMI texp  (E_Let (TID, texp1, texp2, TIDleft))
  targs : texp                         ([texp])
        | texp TCOMMA targs            (texp :: targs)
\<close>

text\<open> Elaborator:
  \<^item> E_Neg  -> uminus;  E_Sub -> minus;
  \<^item> E_Call (f, args) -> Term.list_comb (Free (f, dummyT), args') -- the head applied to its
    arguments, i.e. `Free f $ a1 $ ... $ aN`. This is exactly the shape uRust's elaborator produces
    for funcallN (there the head is a specific lifted combinator rather than a bare Free, but the
    parse-a-comma-list-and-fold-into-application mechanic transfers directly). The head resolves at
    the single check_term against the context (a `context fixes` function, below). \<close>
ML\<open>
structure Toy_Translate =
struct
  open Toy_AST
  fun mk_binop c a b = Const (c, dummyT) $ a $ b

  (* PIDE click-to-definition: link each let-bound variable USE to its binder via a shared serial --
     a `def` entity markup at the binder's name position and a `ref` at each use (carrying the binder
     position), so ctrl-click on a use jumps to its `let`. Colour is separate (the lexer's Markup.free
     on TID); this only adds navigation. Same recipe Isabelle's own calculation.ML uses. *)
  val toy_varN = "toy_var"
  (* Binder-GENERIC variable machinery (not `let`-specific): a bound name -- at its binder and at every
     use, including inside antiquotations -- is coloured GREEN (Markup.bound, like Isabelle's own bound
     variables / the frontend's resolve_bound) and carries a def/ref entity pair (shared serial) for
     ctrl-click navigation. A genuine free / call head is coloured blue (Markup.free), below. *)
  fun report_def ctxt id (x, def_pos) =
    (Context_Position.report ctxt def_pos Markup.bound;
     Context_Position.report ctxt def_pos (Position.make_entity_markup {def = true} id toy_varN (x, def_pos)))
  fun report_ref ctxt id (x, def_pos) use_pos =
    (Context_Position.report ctxt use_pos Markup.bound;
     Context_Position.report ctxt use_pos (Position.make_entity_markup {def = false} id toy_varN (x, def_pos)))

  (* Register a binder occurrence: fresh serial, def markup at its name position, env entry; returns
     (its Free, the extended env). EVERY binding construct should go through this -- `let` today, and
     future closures / for-loops / match patterns -- so colour, click-to-def, capture, and
     antiquotation handling are uniform and binder-generic. *)
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

  (* Colour every enclosing-`let`-bound variable GREEN wherever it occurs in an antiquotation body --
     at ANY depth (`⟪x⟫`, `⟪x + 1⟫`, `⟪f x (g y)⟫`). Syntax.parse_term gives the correct term and full
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

  (* env : source name -> { its Free, the binder's name position, its def serial } *)
  fun mk ctxt env e =
    (case e of
       E_Num (i, _)      => HOLogic.mk_number \<^typ>\<open>int\<close> i
     | E_Var (x, use_pos) =>
         (case Symtab.lookup env x of
            SOME {free, def_pos, id} => (report_ref ctxt id (x, def_pos) use_pos; free)
          | NONE => (Context_Position.report ctxt use_pos Markup.free; Free (x, dummyT)))
              (* deferred: a genuine free var (blue); not a let binder, so no navigation target *)
     | E_Antiq src => parse_antiq ctxt env src   (* HOL body; captured vars coloured green (see above) *)
     | E_Neg (a, _)      => Const (\<^const_name>\<open>uminus\<close>, dummyT) $ mk ctxt env a
     | E_Add (a, b)      => mk_binop \<^const_name>\<open>plus\<close>  (mk ctxt env a) (mk ctxt env b)
     | E_Sub (a, b)      => mk_binop \<^const_name>\<open>minus\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Mul (a, b)      => mk_binop \<^const_name>\<open>times\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Call (f, args, fpos) =>
         (Context_Position.report ctxt fpos Markup.free;   (* call head is a free function (blue) *)
          Term.list_comb (Free (f, dummyT), map (mk ctxt env) args))   (* applied head = funcallN shape *)
     | E_Let (x, rhs, body, def_pos) =>
         let
           val rhs'         = mk ctxt env rhs       (* rhs is in the OUTER scope (x not yet visible) *)
           val (free, env') = bind_var ctxt env (x, def_pos)   (* binder-generic registration *)
           val body'        = mk ctxt env' body     (* innermost binding wins -> shadowing-correct *)
         in Const (\<^const_name>\<open>Let\<close>, dummyT) $ rhs' $ Term.lambda free body' end)
  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

text\<open> The command, serialized behind a mutex (the Isabelle_lex_yacc runtime holds global refs). Each
toy theory is self-contained, so it declares its own lock. \<close>
ML\<open>
val toy_lock = Synchronized.var "toy_lock" ()
fun with_toy_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result toy_lock (fn () => (f (), ()))

fun define_toy (binding, source) lthy =
  with_toy_lock (fn () =>
    (case Toy.parse_source lthy source of
       SOME ast =>
         let
           val t = Syntax.check_term lthy (Toy_Translate.mk_closed lthy ast)
           val ((_, _), lthy') =
             Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
         in lthy' end
     | NONE => error "Failed to parse Toy expression."))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>toy_def\<close>
          "Parse a Toy expression (unary minus, calls) and define it as a HOL int term"
          (Parse.binding -- Parse.input Parse.cartouche >> define_toy)
\<close>

text\<open> NOTE ON PRECEDENCE / CONFLICTS. The expression grammar (texp OP texp for +, -, *) is ambiguous
by construction. Rather than restructuring it into precedence tiers by hand, we declare precedence
ONCE and let the LALR generator resolve the ambiguity -- so the construction is CONFLICT-FREE (this
build reports no conflicts and no warnings; verified). This is exactly the mechanic the real uRust
parser will use in place of the current frontend's hand-tuned mixfix priorities. Specifically:
  \<^item> associativity + tiers: %left TPLUS TMINUS (loosest) then %left TTIMES (tighter) fix how
    `a + b * c` and `a - b - c` group;
  \<^item> unary vs binary `-` (the sharp case): the token TMINUS is shared, so the `TMINUS texp` rule
    would otherwise inherit binary-minus precedence; the %prec UMINUS override retags it with the
    higher UMINUS precedence, so `-a*b = (-a)*b` and `- -5` nests. This override is what keeps the
    unary rule from conflicting;
  \<^item> variable vs call head needs NO precedence: after TID, the lookahead TLPAR is not in
    FOLLOW(texp) (no rule places a texp immediately before `(`), so LALR lookahead alone selects the
    call rule -- there is no conflict here to resolve.
To inspect the generated tables, add the [verbose] command option (ml_lex_yacc [verbose] "Toy"),
which dumps grm.desc under lex_yacc/ in Isabelle's virtual FS. \<close>


subsection\<open> Examples: unary minus and precedence \<close>

text\<open> Unary minus binds tighter than *, so this is (-2)*3 + -4 = -6 + -4 = -10. \<close>
toy_def neg1 \<open> -2 * 3 + -4 \<close>
thm neg1_def

text\<open> Binary vs unary minus in one expression: 10 - -3 = 13; double negation --5 = 5. \<close>
toy_def neg2 \<open> 10 - -3 \<close>
toy_def neg3 \<open> - -5 \<close>
thm neg2_def
thm neg3_def

text\<open> Subtraction associativity (left): 10 - 3 - 2 = (10 - 3) - 2 = 5. \<close>
toy_def sub_assoc \<open> 10 - 3 - 2 \<close>
lemma \<open> sub_assoc = 5 \<close> unfolding sub_assoc_def by simp


subsection\<open> Examples: comma-argument function calls (applied-head / funcallN shape) \<close>

text\<open> Calls lower to an applied head. The head resolves against the enclosing context: g is binary,
h is unary. Nested calls and toy arithmetic in argument position both work. \<close>
context fixes g :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and h :: \<open>int \<Rightarrow> int\<close>
begin
toy_def call1 \<open> g(1, 2) \<close>
thm call1_def

text\<open> Arguments are full Toy expressions (arithmetic, unary minus, nested calls). \<close>
toy_def call2 \<open> g(h(3), -4 * 2) + h(10) \<close>
thm call2_def

text\<open> A call head applied to arguments that mention a `let` binder -- capture still works. \<close>
toy_def call3 \<open> let x = 5; g(x, x * x) \<close>
thm call3_def
end

text\<open> Zero-argument call: lowers to the bare head (Free k applied to no arguments = k), resolved
against the context. \<close>
context fixes k :: int
begin
toy_def call0 \<open> k() + 1 \<close>
thm call0_def
end


subsection\<open> All features together: antiquotation + deferred name + call + unary minus \<close>

context fixes g :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and foo :: int
begin
toy_def combo \<open> let x = 3; g(\<llangle>x - 1\<rrangle>, -x) + foo \<close>
thm combo_def
end


subsection\<open> Click-to-definition (view in jEdit) \<close>

text\<open> In the cartouche arguments below, ctrl-click (Cmd-click on macOS) any \<^emph>\<open>use\<close> of a
\<^verbatim>\<open>let\<close>-bound variable and jEdit jumps to its binding \<^verbatim>\<open>let\<close> (from the def/ref entity
markup the elaborator emits). Binding is lexical, so under shadowing a use resolves to the NEAREST
enclosing binder. Colour is separate (identifiers are free-variable coloured). \<close>

text\<open> Two binders; the body's uses of \<^verbatim>\<open>a\<close> and \<^verbatim>\<open>b\<close> click to their own
\<^verbatim>\<open>let\<close>. \<close>
toy_def nav_two \<open> let a = 3; let b = a * a; a + b * a \<close>
thm nav_two_def

text\<open> Shadowing: the body's uses of \<^verbatim>\<open>x\<close> click to the INNER \<^verbatim>\<open>let x\<close>; the outer
\<^verbatim>\<open>let x\<close> is a separate, unused binder. \<close>
toy_def nav_shadow \<open> let x = 1; let x = 10; x * x + x \<close>
thm nav_shadow_def


subsection\<open> Inspection demos: input / AST / HOL \<close>

ML\<open>
local
  fun ast_str e =
    let
      open Toy_AST
      fun s (E_Num (i, _))        = "Num " ^ string_of_int i
        | s (E_Var (x, _))        = "Var " ^ quote x
        | s (E_Antiq src)         = "Antiq " ^ quote (#1 (Input.source_content src))
        | s (E_Neg (a, _))        = "Neg (" ^ s a ^ ")"
        | s (E_Add (a, b))        = "Add (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Sub (a, b))        = "Sub (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Mul (a, b))        = "Mul (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Let (x, a, b, _))  = "Let (" ^ quote x ^ ", " ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Call (f, args, _)) = "Call (" ^ quote f ^ ", [" ^ commas (map s args) ^ "])"
    in s e end
in
  fun toy_demo ctxt source =
    let val src = #1 (Input.source_content source) in
      (case Toy.parse_source ctxt source of
         NONE     => Pretty.writeln (Pretty.str ("input : " ^ src ^ "   <parse failed>"))
       | SOME ast =>
           let val t = Syntax.check_term ctxt (Toy_Translate.mk_closed ctxt ast) in
             Pretty.writeln (Pretty.chunks
               [ Pretty.str ("input : " ^ src),
                 Pretty.str ("AST   : " ^ ast_str ast),
                 Pretty.block [Pretty.str "HOL   : ", Syntax.pretty_term ctxt t] ])
           end)
    end
end
\<close>

text\<open> A diag command wrapping toy_demo: parse the cartouche and print input / AST / HOL. \<close>
ML\<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>toy_demo_inspect\<close>
          "Parse a Toy expression and print its input string, SML AST, and HOL term"
          (Parse.input Parse.cartouche >> (fn source =>
             Toplevel.keep (fn st =>
               with_toy_lock (fn () => toy_demo (Toplevel.context_of st) source))))
\<close>

toy_demo_inspect \<open> -2 * 3 + -4 \<close>            \<comment>\<open> unary vs binary minus, precedence \<close>
toy_demo_inspect \<open> 10 - -3 \<close>                \<comment>\<open> binary minus then unary minus \<close>
toy_demo_inspect \<open> g(h(3), -4 * 2) \<close>        \<comment>\<open> nested calls, comma args, unary arg \<close>
toy_demo_inspect \<open> let x = 5; g(x, x * x) \<close> \<comment>\<open> call args capture the let binder \<close>

end
