(* Toy 2 of the custom uRust parser effort: antiquotations + deferred name resolution.

   Starts from the Toy_Lex_Yacc1 language and adds the two remaining lex-yacc mechanics the real
   parser needs (both uRust-free): a <<HOL>> antiquotation (with binder capture) and deferred name
   resolution against the HOL context. Also carries the corrected symbol position layer (fixes the
   PIDE-markup drift after a multi-char Isabelle-symbol escape). See the header of Toy_Lex_Yacc0.thy
   for the full chain, and notes/urust-parser-plan.md / notes/isabelle-lex-yacc-notes.md. *)

theory Toy_Lex_Yacc2
  imports "Isabelle_Lex-Yacc.LexYacc"
  keywords
    "toy2_def" :: thy_decl
    and "toy2_demo_inspect" :: diag
begin

section\<open> Toy2: antiquotations + deferred name resolution \<close>

text\<open> Starts from the Toy language and adds the two remaining lex-yacc mechanics the real parser
needs (both \<mu>Rust-free):
  (a) an antiquotation <<...>> that embeds a HOL sublanguage -- the lexer matches the bracket's
      \<open>\<name>\<close> escape and captures the inner text (it does NOT lex the HOL); the elaborator hands
      that text to Syntax.parse_term in the current binder scope, so an enclosing `let` CAPTURES a
      same-named variable inside <<...>> (via Term.lambda, exactly as uRust's antiquotations do);
  (b) a bare identifier that is NOT let-bound resolves later, at the single Syntax.check_term,
      against the surrounding HOL context (e.g. a `context fixes` variable) -- built with dummyT, no
      dispatch machinery.

Background (settled in the retired symbol-lexing spike; see notes/isabelle-lex-yacc-notes.md):
Isabelle symbols are ASCII escapes on disk, handed to the lexer by Input.source_content. This is moot
for pure-ASCII (Rust-like) source, and only concerns tokens that ARE Isabelle symbols (the
antiquotation brackets here). Two facts drove this file: (1) such a token needs a lex rule matching
its escape or it mis-lexes (with ASCII-only rules the escape is grabbed as an identifier); (2)
get_pos maps a per-CHARACTER yypos against a per-SYMBOL source, so PIDE markup for tokens after a
multi-char escape drifts right by the escape length. Both are handled below: the brackets match
`\\"<llangle>"`/`\\"<rrangle>"`, and a corrected position layer (fixed_pos / tokF / tok_valF) maps
char offsets through Input.source_explode to the containing symbol's Position.T. \<close>

ML\<open>
structure Toy2_AST =
struct
  datatype expr =
      E_Num of int * Position.T
    | E_Var of string * Position.T
    | E_Add of expr * expr
    | E_Mul of expr * expr
    | E_Let of string * expr * expr * Position.T
    | E_Antiq of string * Position.T   (* captured HOL source text (the <<...>> body) *)
end
\<close>

SML_import \<open> structure Toy2_AST = Toy2_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>   \<comment>\<open> for the corrected position map below \<close>

text\<open> The antiquotation body is captured with a start state (AQ) + a buffer, à la Pascal's comment
scanner. The <<...>> brackets are the Isabelle symbols \<open>\<llangle>\<close>/\<open>\<rrangle>\<close>, matched by an
explicit escape rule. Under the command mutex the buffer ref is safe. \<close>
ml_lex_yacc "Toy2" where
lex_user_declarations\<open>
val aq_buf = ref ""
val aq_pos = ref 0

(* Corrected position mapping (fixes the markup drift). The framework's get_pos indexes a per-symbol
   vector with the lexer's per-CHARACTER yypos, so positions drift after a multi-char Isabelle-symbol
   escape. We capture the source (shadowing `set`, which the linker calls before parsing) and map a
   char offset to the position of the symbol that contains it. `Input` is SML_imported just above;
   Position.report needs no context. *)
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
    let val p = Position.range_position (Position.range (fixed_pos yypos, fixed_pos (yypos + len)))
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
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.keyword2, "TPLUS", "", Tokens.TPLUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.keyword2, "TTIMES", "", Tokens.TTIMES));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "TLPAR", "", Tokens.TLPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "TRPAR", "", Tokens.TRPAR));
<INITIAL>{alpha}({alpha}|{digit})* => (tok_valF (yypos, yytext, Markup.free, "TID", "", Tokens.TID, yytext));
<INITIAL>\\"<llangle>" => (aq_buf := ""; aq_pos := yypos; YYBEGIN AQ; lex());
<INITIAL>.        => (lex());
<AQ>\\"<rrangle>"   => (YYBEGIN INITIAL; tok_valF (!aq_pos, "", Markup.keyword3, "TAQ", "", Tokens.TAQ, !aq_buf));
<AQ>\n            => (aq_buf := !aq_buf ^ "\n"; lex());
<AQ>.             => (aq_buf := !aq_buf ^ yytext; lex());
\<close>
and yacc_user_declarations\<open>
open Toy2_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

%left TPLUS
%left TTIMES

%term TNUM of int | TID of string | TAQ of string | TLET | TEQ | TSEMI
    | TPLUS | TTIMES | TLPAR | TRPAR | EOF
%nonterm tstart of Toy2_AST.expr option | texp of Toy2_AST.expr
\<close>
yacc_rules\<open>
  tstart : texp (SOME texp)
         | (NONE)
  texp : TNUM                          (E_Num (TNUM, TNUMleft))
       | TID                           (E_Var (TID, TIDleft))
       | TAQ                           (E_Antiq (TAQ, TAQleft))
       | texp TPLUS texp               (E_Add (texp1, texp2))
       | texp TTIMES texp              (E_Mul (texp1, texp2))
       | TLPAR texp TRPAR              (texp)
       | TLET TID TEQ texp TSEMI texp  (E_Let (TID, texp1, texp2, TIDleft))
\<close>

text\<open> Elaborator. Differences from Toy: an unbound identifier is DEFERRED (a dummyT Free resolved
by the final check_term against the context) rather than an error; and E_Antiq splices a HOL term
parsed by Syntax.parse_term in scope -- its free variables are captured by any enclosing Term.lambda. \<close>
ML\<open>
structure Toy2_Translate =
struct
  open Toy2_AST
  fun mk_binop c a b = Const (c, dummyT) $ a $ b
  fun mk ctxt env e =
    (case e of
       E_Num (i, _)      => HOLogic.mk_number \<^typ>\<open>int\<close> i
     | E_Var (x, _)      =>
         (case Symtab.lookup env x of
            SOME free => free                      (* let-bound: use the binder's Free *)
          | NONE      => Free (x, dummyT))         (* deferred: resolved by check_term vs context *)
     | E_Antiq (text, _) => Syntax.parse_term ctxt text   (* embed HOL; free vars capturable *)
     | E_Add (a, b)      => mk_binop \<^const_name>\<open>plus\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Mul (a, b)      => mk_binop \<^const_name>\<open>times\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Let (x, rhs, body, _) =>
         let
           val rhs'  = mk ctxt env rhs
           val free  = Free (x, dummyT)
           val env'  = Symtab.update (x, free) env
           val body' = mk ctxt env' body
         in Const (\<^const_name>\<open>Let\<close>, dummyT) $ rhs' $ Term.lambda free body' end)
  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

text\<open> The command, serialized behind a mutex (the Isabelle_lex_yacc runtime holds global refs). Each
toy theory is self-contained, so it declares its own lock. \<close>
ML\<open>
val toy_lock = Synchronized.var "toy2_lock" ()
fun with_toy_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result toy_lock (fn () => (f (), ()))

fun define_toy2 (binding, source) lthy =
  with_toy_lock (fn () =>
    (case Toy2.parse_source lthy source of
       SOME ast =>
         let
           val t = Syntax.check_term lthy (Toy2_Translate.mk_closed lthy ast)
           val ((_, _), lthy') =
             Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
         in lthy' end
     | NONE => error "Failed to parse Toy2 expression."))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>toy2_def\<close>
          "Parse a Toy2 expression (with <<HOL>> antiquotations) and define it as a HOL int term"
          (Parse.binding -- Parse.input Parse.cartouche >> define_toy2)
\<close>

subsection\<open> Examples (define a constant per Toy2 expression) \<close>

text\<open> (a) Antiquotation embeds HOL: (2+3) is parsed by Syntax.parse_term, then * 2 by the toy. \<close>
toy2_def aq1 \<open> \<llangle>2 + 3\<rrangle> * 2 \<close>
thm aq1_def

text\<open> Antiquotation splicing a whole HOL expression that uses HOL operators the toy does not have
(here integer subtraction and division), then combined with toy arithmetic. \<close>
toy2_def aq2 \<open> \<llangle>(100 - 1) div 3\<rrangle> + 10 \<close>
thm aq2_def

text\<open> Capture: the HOL inside <<...>> refers to the toy `let` binder and is captured by Term.lambda;
a fresh-named copy is provably equal (cf. Experiment.thy's binder_captures_antiquotation). \<close>
toy2_def cap_a \<open> let x = 5; \<llangle>x\<rrangle> \<close>
toy2_def cap_b \<open> let z = 5; \<llangle>z\<rrangle> \<close>
lemma \<open> cap_a = cap_b \<close>
  unfolding cap_a_def cap_b_def by (rule refl)

text\<open> (b) Deferred names: foo and bar are not let-bound; they are built as dummyT Frees and resolved
at the single check_term against the enclosing `context fixes` (no dispatch machinery). \<close>
context fixes foo :: int and bar :: int
begin
toy2_def use_ctx \<open> foo + bar * 2 \<close>
thm use_ctx_def

text\<open> All three features at once: a `let` binder, an antiquotation capturing it, and a deferred
context name (bar). \<close>
toy2_def use_all \<open> let x = bar; \<llangle>x * x\<rrangle> + foo \<close>
thm use_all_def
end

subsection\<open> Inspection demos: input / AST / HOL (antiquotations + deferred names) \<close>

text\<open> Like Toy's toy_demo, but for Toy2 -- each block shows the input string, the reified AST
(note the E_Antiq node; positions dropped), and the checked HOL term. Click a block in jEdit to read
its Output. \<close>

ML\<open>
local
  fun ast_str e =
    let
      open Toy2_AST
      fun s (E_Num (i, _))       = "Num " ^ string_of_int i
        | s (E_Var (x, _))       = "Var " ^ quote x
        | s (E_Antiq (t, _))     = "Antiq " ^ quote t
        | s (E_Add (a, b))       = "Add (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Mul (a, b))       = "Mul (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Let (x, a, b, _)) = "Let (" ^ quote x ^ ", " ^ s a ^ ", " ^ s b ^ ")"
    in s e end
in
  fun toy2_demo ctxt source =
    let val src = #1 (Input.source_content source) in
      (case Toy2.parse_source ctxt source of
         NONE     => Pretty.writeln (Pretty.str ("input : " ^ src ^ "   <parse failed>"))
       | SOME ast =>
           let val t = Syntax.check_term ctxt (Toy2_Translate.mk_closed ctxt ast) in
             Pretty.writeln (Pretty.chunks
               [ Pretty.str ("input : " ^ src),
                 Pretty.str ("AST   : " ^ ast_str ast),
                 Pretty.block [Pretty.str "HOL   : ", Syntax.pretty_term ctxt t] ])
           end)
    end
end
\<close>

text\<open> A diag command wrapping toy2_demo (see Toy_Lex_Yacc1's toy_demo_inspect). \<close>
ML\<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>toy2_demo_inspect\<close>
          "Parse a Toy2 expression and print its input string, SML AST, and HOL term"
          (Parse.input Parse.cartouche >> (fn source =>
             Toplevel.keep (fn st =>
               with_toy_lock (fn () => toy2_demo (Toplevel.context_of st) source))))
\<close>

toy2_demo_inspect \<open> \<llangle>2 + 3\<rrangle> * 2 \<close>                 \<comment>\<open> antiquotation + toy arithmetic \<close>
toy2_demo_inspect \<open> \<llangle>(100 - 1) div 3\<rrangle> + 10 \<close>       \<comment>\<open> HOL ops the toy lacks \<close>
toy2_demo_inspect \<open> let x = 5; \<llangle>x\<rrangle> * \<llangle>x\<rrangle> \<close>     \<comment>\<open> binder captured inside the antiquotations \<close>
toy2_demo_inspect \<open> foo + bar * 2 \<close>                       \<comment>\<open> deferred names (free until check_term) \<close>


subsection\<open> jEdit visual check: does token highlighting after an antiquotation stay aligned? \<close>

text\<open> Open this theory in jEdit and compare the two commands below. They have the SAME trailing
tokens (\<^verbatim>\<open>+ let hello = 42; hello * 7\<close>); the only difference is the head:
\<^verbatim>\<open>hl_base\<close> starts with the ASCII \<^verbatim>\<open>(1)\<close>, while \<^verbatim>\<open>hl_aq\<close> starts with the
antiquotation \<open>\<llangle>1\<rrangle>\<close> whose brackets are multi-char Isabelle-symbol escapes.

  Look at whether the token COLOURS after the head sit exactly on their tokens in BOTH lines --
  \<^verbatim>\<open>let\<close> as a keyword, \<^verbatim>\<open>hello\<close> as a free variable, \<^verbatim>\<open>= + *\<close> as operators,
  \<^verbatim>\<open>42\<close>/\<^verbatim>\<open>7\<close> as numerals, \<^verbatim>\<open>;\<close> as a delimiter. Originally \<^verbatim>\<open>hl_aq\<close> was
  shifted ~18 chars right (the \<^verbatim>\<open>+\<close> colour landed on the second \<^verbatim>\<open>hello\<close>, \<^verbatim>\<open>let\<close>
  on its \<^verbatim>\<open>llo\<close>) -- the char/symbol drift reaching the PIDE markup. It is now FIXED by the
  corrected position layer above (\<^verbatim>\<open>fixed_pos\<close> / \<^verbatim>\<open>tokF\<close> / \<^verbatim>\<open>tok_valF\<close>): the
  colours in \<^verbatim>\<open>hl_aq\<close> now line up with \<^verbatim>\<open>hl_base\<close>. Keep this as a regression check.
  (NB: error-message columns via print_error's get_line_col are a separate framework path and may
  still be off by a little; the markup is what this fixes.) \<close>
toy2_def hl_base \<open> (1) + let hello = 42; hello * 7 \<close>
toy2_def hl_aq   \<open> \<llangle>1\<rrangle> + let hello = 42; hello * 7 \<close>

end
