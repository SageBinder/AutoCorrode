(* Small, uRust-independent sandbox for the parser pipeline: reified AST, precedence, calls, binders,
   positioned antiquotations, deferred names, PIDE markup, and one final Syntax.check_term. *)

theory Toy_Lex_Yacc
  imports "Isabelle_Lex-Yacc.LexYacc" Parser_Utils
  keywords
    "toy_def" :: thy_decl
    and "toy_demo_inspect" :: diag
begin

section\<open> Toy language \<close>

text\<open> Integer expressions with \<open>let\<close>, antiquotations, arithmetic, and calls. \<close>
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
SML_import \<open> structure Input = struct open Input end \<close>
SML_import \<open> structure Position = struct open Position end \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>

ML\<open>
structure Toy_Err =
struct
  fun lex_error text pos =
    error ("Toy parser: unexpected input " ^ quote text ^ Position.here pos)

  fun antiquotation_error pos =
    error ("Toy parser: unterminated antiquotation" ^ Position.here pos)
end
\<close>
SML_import \<open> structure Toy_Err = Toy_Err \<close>

text\<open> The generated lexer keeps only its source map and \<open>Tokens\<close> wrappers locally. \<close>
ml_lex_yacc "Toy" where
lex_user_declarations\<open>
val aq_active = ref false
val aq_buf = ref ([] : string list)
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)
val aq_open = ref 0
val aq_depth = ref 0

fun reset_aq () =
  (aq_active := false; aq_buf := []; aq_start := 0; aq_open := 0; aq_depth := 0)
fun start_aq open_pos body_pos =
  (aq_active := true; aq_buf := []; aq_start := body_pos; aq_open := open_pos; aq_depth := 0)
fun push_aq fragment = aq_buf := fragment :: !aq_buf
fun take_aq () =
  let val body = String.concat (rev (!aq_buf))
  in reset_aq (); body end

(* Keep generated Tokens constructors local; share position conversion. Identifiers are marked after
   their role is known. *)
val pos_map = ref (Parser_Lex_Util.make_position_map (Input.string ""))
fun set source ctxt =
  (Isabelle_lex_yacc.set source ctxt;
   pos_map := Parser_Lex_Util.make_position_map source;
   reset_aq ())

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!pos_map) yypos
fun tokF args       = Parser_Lex_Util.tokF (!pos_map) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!pos_map) args
fun report_text args = Parser_Lex_Util.report_text (!pos_map) args
fun tok_id (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!pos_map) (yypos, yytext)
  in Tokens.TID (yytext, p, p) end

fun eof () =
  if !aq_active then Toy_Err.antiquotation_error (fixed_pos (!aq_open))
  else Tokens.EOF (Position.none, Position.none)
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
<INITIAL>{digit}+ => (tok_valF (yypos, yytext, Markup.numeral, "TNUM", Tokens.TNUM, valOf (Int.fromString yytext)));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", Tokens.TLET));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.delimiter, "TEQ", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", Tokens.TSEMI));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "TCOMMA", Tokens.TCOMMA));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.operator, "TPLUS", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.operator, "TMINUS", Tokens.TMINUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.operator, "TTIMES", Tokens.TTIMES));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "TLPAR", Tokens.TLPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "TRPAR", Tokens.TRPAR));
<INITIAL>{alpha}({alpha}|{digit})* => (tok_id (yypos, yytext));
<INITIAL>\\"<llangle>" => (report_text (yypos, yytext, Markup.delimiter, "TAQ");
    start_aq yypos (yypos + size yytext); YYBEGIN AQ; lex());
<INITIAL>.        => (Toy_Err.lex_error yytext (fixed_pos yypos));
<AQ>\\"<llangle>" => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<AQ>\\"<rrangle>" =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_text (yypos, yytext, Markup.delimiter, "TAQ");
       let val p = fixed_pos (!aq_start) val q = fixed_pos yypos val body = take_aq ()
       in Tokens.TAQ (Input.source true body (Position.range (p, q)), p, q) end));
<AQ>\n            => (push_aq "\n"; lex());
<AQ>.             => (push_aq yytext; lex());
\<close>
and yacc_user_declarations\<open>
open Toy_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

(* A let body extends through following arithmetic. UMINUS is an unlexed precedence marker,
   tighter than multiplication. *)
%right TLET
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
       | TLET TID TEQ texp TSEMI texp %prec TLET
                                          (E_Let (TID, texp1, texp2, TIDleft))
  targs : texp                         ([texp])
        | texp TCOMMA targs            (texp :: targs)
\<close>

text\<open> Calls become applied free heads; one final \<open>check_term\<close> resolves them against the context. \<close>
ML\<open>
structure Toy_Translate =
struct
  open Toy_AST
  fun mk_binop c a b = Const (c, dummyT) $ a $ b

  val vkind       = "toy_var"
  val report_ref  = Parser_Utils.report_ref vkind
  val bind_var    = Parser_Utils.bind_var vkind
  val parse_antiq = Parser_Utils.parse_antiq vkind

  fun mk ctxt env e =
    (case e of
       E_Num (i, _)      => HOLogic.mk_number \<^typ>\<open>int\<close> i
     | E_Var (x, use_pos) =>
         (case Symtab.lookup env x of
            SOME {free, def_pos, id} => (report_ref ctxt id (x, def_pos) use_pos; free)
          | NONE => (Context_Position.report ctxt use_pos Markup.free; Free (x, dummyT)))
     | E_Antiq src => parse_antiq ctxt env src
     | E_Neg (a, _)      => Const (\<^const_name>\<open>uminus\<close>, dummyT) $ mk ctxt env a
     | E_Add (a, b)      => mk_binop \<^const_name>\<open>plus\<close>  (mk ctxt env a) (mk ctxt env b)
     | E_Sub (a, b)      => mk_binop \<^const_name>\<open>minus\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Mul (a, b)      => mk_binop \<^const_name>\<open>times\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Call (f, args, fpos) =>
         (Context_Position.report ctxt fpos Markup.free;
          Term.list_comb (Free (f, dummyT), map (mk ctxt env) args))
     | E_Let (x, rhs, body, def_pos) =>
         let
           val rhs'         = mk ctxt env rhs
           val (free, env') = bind_var ctxt env (x, def_pos)
           val body'        = mk ctxt env' body
         in Const (\<^const_name>\<open>Let\<close>, dummyT) $ rhs' $ Term.lambda free body' end)
  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

text\<open> Only parsing uses the shared mutex; term checking and definition remain parallel. \<close>
ML\<open>
fun define_toy (binding, source) lthy =
  (case Parser_Utils.with_parser_lock (fn () => Toy.parse_source lthy source) of
     SOME ast =>
       let
         val t = Syntax.check_term lthy (Toy_Translate.mk_closed lthy ast)
         val ((_, _), lthy') =
           Local_Theory.define ((binding, NoSyn), ((Thm.def_binding binding, []), t)) lthy
       in lthy' end
   | NONE => error "Failed to parse Toy expression.")

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>toy_def\<close>
          "Parse a Toy expression (unary minus, calls) and define it as a HOL int term"
          (Parse.binding -- Parse.input Parse.cartouche >> define_toy)
\<close>

text\<open> Yacc precedence resolves binary tiers and unary \<open>-\<close>; lookahead distinguishes variables from
calls. \<close>


subsection\<open> Precedence \<close>

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


subsection\<open> Calls \<close>

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


subsection\<open> Combined features \<close>

context fixes g :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> and foo :: int
begin
toy_def combo \<open> let x = 3; g(\<llangle>x - 1\<rrangle>, -x) + foo \<close>
thm combo_def
end


subsection\<open> Navigation \<close>

text\<open>
Ctrl-clicking a bound use jumps to its nearest lexical \<open>let\<close> via def/ref markup.
Identifier coloring remains independent.
\<close>

text\<open> Two binders; the body's uses of \<^verbatim>\<open>a\<close> and \<^verbatim>\<open>b\<close> click to their own
\<^verbatim>\<open>let\<close>. \<close>
toy_def nav_two \<open> let a = 3; let b = a * a; a + b * a \<close>
thm nav_two_def

text\<open> Shadowing: the body's uses of \<^verbatim>\<open>x\<close> click to the INNER \<^verbatim>\<open>let x\<close>; the outer
\<^verbatim>\<open>let x\<close> is a separate, unused binder. \<close>
toy_def nav_shadow \<open> let x = 1; let x = 10; x * x + x \<close>
thm nav_shadow_def


subsection\<open> Inspection \<close>

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
      (case Parser_Utils.with_parser_lock (fn () => Toy.parse_source ctxt source) of
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
               toy_demo (Toplevel.context_of st) source)))
\<close>

toy_demo_inspect \<open> -2 * 3 + -4 \<close>            \<comment>\<open> unary vs binary minus, precedence \<close>
toy_demo_inspect \<open> 10 - -3 \<close>                \<comment>\<open> binary minus then unary minus \<close>
toy_demo_inspect \<open> g(h(3), -4 * 2) \<close>        \<comment>\<open> nested calls, comma args, unary arg \<close>
toy_demo_inspect \<open> let x = 5; g(x, x * x) \<close> \<comment>\<open> call args capture the let binder \<close>

end
