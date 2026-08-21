(* Toy 3 of the custom uRust parser effort: the grammar mechanics the real parser needs.

   Extends the Toy_Lex_Yacc2 language (arithmetic + let + <<HOL>> antiquotations + deferred names)
   with the three parsing mechanics none of the earlier toys exercised -- exactly the gap identified
   before Phase 1:

     (1) a UNARY operator sharing a token with a binary one (unary vs binary `-`), disambiguated by a
         %prec precedence override on a pseudo-terminal (UMINUS), à la Pascal's UNARYSIGN;
     (2) precedence-directive disambiguation of an ambiguous expression grammar: the %left tiers and
         a %prec override keep the LALR construction conflict-free -- the mechanic that replaces the
         current frontend's hand-tuned mixfix priorities;
     (3) comma-separated function-call argument lists, lowered to an APPLIED HEAD
         (Free f $ a1 $ ... $ aN via Term.list_comb) -- the shape the real elaborator uses for
         funcallN.

   Everything else (parse -> AST -> HOL -> define, dummyT + one check_term, Free+Term.lambda binder
   capture, the with_toy_lock mutex, the corrected symbol position layer, antiquotation capture,
   deferred-name resolution) is carried over from Toy_Lex_Yacc2. See the header of Toy_Lex_Yacc0.thy
   for the full chain, and notes/urust-parser-plan.md. *)

theory Toy_Lex_Yacc3
  imports "Isabelle_Lex-Yacc.LexYacc"
  keywords
    "toy3_def" :: thy_decl
    and "toy3_demo_inspect" :: diag
begin

section\<open> Toy3: unary %prec, precedence-directive disambiguation, and comma-argument calls \<close>

text\<open> The reified AST. New over Toy2: E_Neg (unary minus), E_Sub (binary minus), and E_Call (a
function-call head applied to an argument list). \<close>
ML\<open>
structure Toy3_AST =
struct
  datatype expr =
      E_Num  of int * Position.T
    | E_Var  of string * Position.T
    | E_Antiq of string * Position.T
    | E_Neg  of expr * Position.T
    | E_Add  of expr * expr
    | E_Sub  of expr * expr
    | E_Mul  of expr * expr
    | E_Let  of string * expr * expr * Position.T
    | E_Call of string * expr list * Position.T   (* f(a1, ..., aN) *)
end
\<close>

SML_import \<open> structure Toy3_AST = Toy3_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>   \<comment>\<open> re-import for the position map (idempotent) \<close>

text\<open> Lexer. Same shape as Toy2 (the corrected fixed_pos / tokF / tok_valF position layer is
duplicated here because those helpers are local to each generated lexer). New tokens: TMINUS and
TCOMMA. \<close>
ml_lex_yacc "Toy3" where
lex_user_declarations\<open>
val aq_buf = ref ""
val aq_pos = ref 0

(* Corrected position mapping (see Toy_Lex_Yacc2 for the rationale): map the per-CHARACTER yypos to
   the position of the containing Isabelle symbol, so markup after a multi-char escape does not drift. *)
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
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "TCOMMA", "", Tokens.TCOMMA));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.keyword2, "TPLUS", "", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.keyword2, "TMINUS", "", Tokens.TMINUS));
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
open Toy3_AST
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

%term TNUM of int | TID of string | TAQ of string
    | TLET | TEQ | TSEMI | TCOMMA
    | TPLUS | TMINUS | TTIMES | TLPAR | TRPAR | UMINUS | EOF
%nonterm tstart of Toy3_AST.expr option
       | texp of Toy3_AST.expr
       | targs of Toy3_AST.expr list
\<close>
yacc_rules\<open>
  tstart : texp (SOME texp)
         | (NONE)
  texp : TNUM                          (E_Num (TNUM, TNUMleft))
       | TID                           (E_Var (TID, TIDleft))
       | TAQ                           (E_Antiq (TAQ, TAQleft))
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

text\<open> Elaborator. New over Toy2:
  \<^item> E_Neg  -> uminus;  E_Sub -> minus;
  \<^item> E_Call (f, args) -> Term.list_comb (Free (f, dummyT), args') -- the head applied to its
    arguments, i.e. `Free f $ a1 $ ... $ aN`. This is exactly the shape uRust's elaborator produces
    for funcallN (there the head is a specific lifted combinator rather than a bare Free, but the
    parse-a-comma-list-and-fold-into-application mechanic transfers directly). The head resolves at
    the single check_term against the context (a `context fixes` function, below). \<close>
ML\<open>
structure Toy3_Translate =
struct
  open Toy3_AST
  fun mk_binop c a b = Const (c, dummyT) $ a $ b
  fun mk ctxt env e =
    (case e of
       E_Num (i, _)      => HOLogic.mk_number \<^typ>\<open>int\<close> i
     | E_Var (x, _)      =>
         (case Symtab.lookup env x of
            SOME free => free
          | NONE      => Free (x, dummyT))
     | E_Antiq (text, _) => Syntax.parse_term ctxt text
     | E_Neg (a, _)      => Const (\<^const_name>\<open>uminus\<close>, dummyT) $ mk ctxt env a
     | E_Add (a, b)      => mk_binop \<^const_name>\<open>plus\<close>  (mk ctxt env a) (mk ctxt env b)
     | E_Sub (a, b)      => mk_binop \<^const_name>\<open>minus\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Mul (a, b)      => mk_binop \<^const_name>\<open>times\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Call (f, args, _) =>
         Term.list_comb (Free (f, dummyT), map (mk ctxt env) args)   (* applied head = funcallN shape *)
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
val toy_lock = Synchronized.var "toy3_lock" ()
fun with_toy_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result toy_lock (fn () => (f (), ()))

fun define_toy3 (binding, source) lthy =
  with_toy_lock (fn () =>
    (case Toy3.parse_source lthy source of
       SOME ast =>
         let
           val t = Syntax.check_term lthy (Toy3_Translate.mk_closed lthy ast)
           val ((_, _), lthy') =
             Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
         in lthy' end
     | NONE => error "Failed to parse Toy3 expression."))

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>toy3_def\<close>
          "Parse a Toy3 expression (unary minus, calls) and define it as a HOL int term"
          (Parse.binding -- Parse.input Parse.cartouche >> define_toy3)
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
To inspect the generated tables, add the [verbose] command option (ml_lex_yacc [verbose] "Toy3"),
which dumps grm.desc under lex_yacc/ in Isabelle's virtual FS. \<close>


subsection\<open> Examples: unary minus and precedence \<close>

text\<open> Unary minus binds tighter than *, so this is (-2)*3 + -4 = -6 + -4 = -10. \<close>
toy3_def neg1 \<open> -2 * 3 + -4 \<close>
thm neg1_def

text\<open> Binary vs unary minus in one expression: 10 - -3 = 13; double negation --5 = 5. \<close>
toy3_def neg2 \<open> 10 - -3 \<close>
toy3_def neg3 \<open> - -5 \<close>
thm neg2_def
thm neg3_def

text\<open> Subtraction associativity (left): 10 - 3 - 2 = (10 - 3) - 2 = 5. \<close>
toy3_def sub_assoc \<open> 10 - 3 - 2 \<close>
lemma \<open> sub_assoc = 5 \<close> unfolding sub_assoc_def by simp


subsection\<open> Examples: comma-argument function calls (applied-head / funcallN shape) \<close>

text\<open> Calls lower to an applied head. The head resolves against the enclosing context: g is binary,
h is unary. Nested calls and toy arithmetic in argument position both work. \<close>
context fixes g :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and h :: \<open>int \<Rightarrow> int\<close>
begin
toy3_def call1 \<open> g(1, 2) \<close>
thm call1_def

text\<open> Arguments are full Toy3 expressions (arithmetic, unary minus, nested calls). \<close>
toy3_def call2 \<open> g(h(3), -4 * 2) + h(10) \<close>
thm call2_def

text\<open> A call head applied to arguments that mention a `let` binder -- capture still works. \<close>
toy3_def call3 \<open> let x = 5; g(x, x * x) \<close>
thm call3_def
end

text\<open> Zero-argument call: lowers to the bare head (Free k applied to no arguments = k), resolved
against the context. \<close>
context fixes k :: int
begin
toy3_def call0 \<open> k() + 1 \<close>
thm call0_def
end


subsection\<open> All features together: antiquotation + deferred name + call + unary minus \<close>

context fixes g :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and foo :: int
begin
toy3_def combo \<open> let x = 3; g(\<llangle>x - 1\<rrangle>, -x) + foo \<close>
thm combo_def
end


subsection\<open> Inspection demos: input / AST / HOL \<close>

ML\<open>
local
  fun ast_str e =
    let
      open Toy3_AST
      fun s (E_Num (i, _))        = "Num " ^ string_of_int i
        | s (E_Var (x, _))        = "Var " ^ quote x
        | s (E_Antiq (t, _))      = "Antiq " ^ quote t
        | s (E_Neg (a, _))        = "Neg (" ^ s a ^ ")"
        | s (E_Add (a, b))        = "Add (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Sub (a, b))        = "Sub (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Mul (a, b))        = "Mul (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Let (x, a, b, _))  = "Let (" ^ quote x ^ ", " ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Call (f, args, _)) = "Call (" ^ quote f ^ ", [" ^ commas (map s args) ^ "])"
    in s e end
in
  fun toy3_demo ctxt source =
    let val src = #1 (Input.source_content source) in
      (case Toy3.parse_source ctxt source of
         NONE     => Pretty.writeln (Pretty.str ("input : " ^ src ^ "   <parse failed>"))
       | SOME ast =>
           let val t = Syntax.check_term ctxt (Toy3_Translate.mk_closed ctxt ast) in
             Pretty.writeln (Pretty.chunks
               [ Pretty.str ("input : " ^ src),
                 Pretty.str ("AST   : " ^ ast_str ast),
                 Pretty.block [Pretty.str "HOL   : ", Syntax.pretty_term ctxt t] ])
           end)
    end
end
\<close>

text\<open> A diag command wrapping toy3_demo (see Toy_Lex_Yacc1's toy_demo_inspect). \<close>
ML\<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>toy3_demo_inspect\<close>
          "Parse a Toy3 expression and print its input string, SML AST, and HOL term"
          (Parse.input Parse.cartouche >> (fn source =>
             Toplevel.keep (fn st =>
               with_toy_lock (fn () => toy3_demo (Toplevel.context_of st) source))))
\<close>

toy3_demo_inspect \<open> -2 * 3 + -4 \<close>            \<comment>\<open> unary vs binary minus, precedence \<close>
toy3_demo_inspect \<open> 10 - -3 \<close>                \<comment>\<open> binary minus then unary minus \<close>
toy3_demo_inspect \<open> g(h(3), -4 * 2) \<close>        \<comment>\<open> nested calls, comma args, unary arg \<close>
toy3_demo_inspect \<open> let x = 5; g(x, x * x) \<close> \<comment>\<open> call args capture the let binder \<close>

end
