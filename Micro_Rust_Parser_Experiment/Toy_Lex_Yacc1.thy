(* Toy 1 of the custom uRust parser effort: a binder-bearing arithmetic+let language.

   Previews the main techniques the real micro_rust_expr elaborator will use. Imports Toy_Lex_Yacc0
   (Calc). See the header of Toy_Lex_Yacc0.thy for the full chain, and notes/urust-parser-plan.md. *)

theory Toy_Lex_Yacc1
  imports "Isabelle_Lex-Yacc.LexYacc"
  keywords
    "toy_def" :: thy_decl
    and "toy_demo_inspect" :: diag
begin

section\<open> Toy: a binder-bearing language (mirrors the uRust elaborator) \<close>

text\<open> This part previews the main techniques the real micro_rust_expr elaborator will use:
  \<^item> grammar actions build a reified SML AST that carries source positions;
  \<^item> the elaborator threads a functional environment (source name -> its Free);
  \<^item> a binder (let) is closed with Term.lambda over a source-named Free -- capture-safe and
    shadowing-correct, exactly as uRust's `let x = e; k` becomes `bind e (\<lambda>x. k)`;
  \<^item> terms are built with dummyT and resolved by a single Syntax.check_term;
  \<^item> the command body is serialized behind a mutex (the Isabelle_lex_yacc runtime holds global refs).
  The Toy language is integer arithmetic (+, *, parens) with `let x = e1; e2` binding, lowered to
  ordinary HOL int expressions using HOL's Let combinator over a real lambda. \<close>

text\<open> The reified SML AST built by the grammar actions. Constructors are prefixed (E_) and carry a
Position.T where a source position is useful (numerals, variable uses, and the let binder). \<close>
ML\<open>
structure Toy_AST =
struct
  datatype expr =
      E_Num of int * Position.T
    | E_Var of string * Position.T
    | E_Add of expr * expr
    | E_Mul of expr * expr
    | E_Let of string * expr * expr * Position.T   (* let <name> = <rhs>; <body> *)
end
\<close>

SML_import \<open> structure Toy_AST = Toy_AST \<close>

ml_lex_yacc "Toy" where
lex_definitions\<open>
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
\n       => (lex());
{ws}+    => (lex());
{digit}+ => (tok_val (yypos, yytext, Markup.numeral, "TNUM", "", Tokens.TNUM, valOf (Int.fromString yytext)));
"let"    => (tok (yypos, yytext, Markup.keyword1, "TLET", "", Tokens.TLET));
"="      => (tok (yypos, yytext, Markup.keyword2, "TEQ", "", Tokens.TEQ));
";"      => (tok (yypos, yytext, Markup.delimiter, "TSEMI", "", Tokens.TSEMI));
"+"      => (tok (yypos, yytext, Markup.keyword2, "TPLUS", "", Tokens.TPLUS));
"*"      => (tok (yypos, yytext, Markup.keyword2, "TTIMES", "", Tokens.TTIMES));
"("      => (tok (yypos, yytext, Markup.delimiter, "TLPAR", "", Tokens.TLPAR));
")"      => (tok (yypos, yytext, Markup.delimiter, "TRPAR", "", Tokens.TRPAR));
{alpha}({alpha}|{digit})* => (tok_val (yypos, yytext, Markup.free, "TID", "", Tokens.TID, yytext));
.        => (lex());
\<close>
and yacc_user_declarations\<open>
open Toy_AST
\<close>
yacc_definitions\<open>
%eop EOF
%noshift EOF

%left TPLUS
%left TTIMES

%term TNUM of int | TID of string | TLET | TEQ | TSEMI
    | TPLUS | TTIMES | TLPAR | TRPAR | EOF
%nonterm tstart of Toy_AST.expr option | texp of Toy_AST.expr
\<close>
yacc_rules\<open>
  tstart : texp (SOME texp)
         | (NONE)
  texp : TNUM                          (E_Num (TNUM, TNUMleft))
       | TID                           (E_Var (TID, TIDleft))
       | texp TPLUS texp               (E_Add (texp1, texp2))
       | texp TTIMES texp              (E_Mul (texp1, texp2))
       | TLPAR texp TRPAR              (texp)
       | TLET TID TEQ texp TSEMI texp  (E_Let (TID, texp1, texp2, TIDleft))
\<close>

text\<open> Lower the SML AST to a HOL int term. Techniques mirrored from the uRust elaborator:
env-threaded Free lookup, a binder closed with Term.lambda (capture-safe), everything built with
dummyT and resolved by a single Syntax.check_term (run in define_toy). In addition, the elaborator
emits PIDE entity markup: each `let` binder is reported as a *definition* and each variable use as a
*reference* sharing the same serial, so in jEdit a variable use ctrl-clicks to its binder. (Token
colouring is separate -- it comes from the lexer's tok/tok_val Markup.T; this only adds navigation,
which tok/tok_val do NOT provide.) \<close>
ML\<open>
structure Toy_Translate =
struct
  open Toy_AST

  fun mk_binop c a b = Const (c, dummyT) $ a $ b

  (* PIDE navigation: link each variable use to its `let` binder via a shared serial.
     def at the binder's name position; ref at each use, carrying the binder position. *)
  val toy_varN = "toy_var"
  fun report_def ctxt id (x, def_pos) =
    Context_Position.report ctxt def_pos
      (Position.make_entity_markup {def = true} id toy_varN (x, def_pos))
  fun report_ref ctxt id (x, def_pos) use_pos =
    Context_Position.report ctxt use_pos
      (Position.make_entity_markup {def = false} id toy_varN (x, def_pos))

  (* env : source name -> {its Free, the binder's name position, its def serial} *)
  fun mk ctxt env e =
    (case e of
       E_Num (i, _)   => HOLogic.mk_number \<^typ>\<open>int\<close> i
     | E_Var (x, use_pos) =>
         (case Symtab.lookup env x of
            SOME {free, def_pos, id} =>
              (report_ref ctxt id (x, def_pos) use_pos; free)
          | NONE => error ("unbound variable " ^ quote x ^ Position.here use_pos))
     | E_Add (a, b)   => mk_binop \<^const_name>\<open>plus\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Mul (a, b)   => mk_binop \<^const_name>\<open>times\<close> (mk ctxt env a) (mk ctxt env b)
     | E_Let (x, rhs, body, def_pos) =>
         let
           val rhs'  = mk ctxt env rhs             (* rhs is in the OUTER scope *)
           val id    = serial ()
           val _     = report_def ctxt id (x, def_pos)
           val free  = Free (x, dummyT)            (* source-named binder *)
           val env'  = Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env
           val body' = mk ctxt env' body           (* innermost binding wins -> shadowing *)
         in
           Const (\<^const_name>\<open>Let\<close>, dummyT) $ rhs' $ Term.lambda free body'
         end)

  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

text\<open> The command: parse a Toy expression and define a HOL constant of type int. Serialized behind a
mutex because the Isabelle_lex_yacc runtime holds global Unsynchronized.ref state (src/ctxt). \<close>
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
          "Parse a Toy arithmetic/let expression and define it as a HOL int term"
          (Parse.binding -- Parse.input Parse.cartouche >> define_toy)
\<close>

text\<open> Plain arithmetic (precedence: * binds tighter than +). \<close>
toy_def toy_arith \<open> 1 + 2 * 3 \<close>
thm toy_arith_def

text\<open> A let-binder: lowers to `Let 5 (\<lambda>x. x * x)` -- built via a source-named Free closed with
Term.lambda. \<close>
toy_def toy_let \<open> let x = 5; x * x \<close>
thm toy_let_def

text\<open> Capture / shadowing: the inner `let x` shadows the outer one, and a fresh-named version is
provably equal -- i.e. the elaborator's Term.lambda captures correctly (cf. Experiment.thy's
binder_captures_antiquotation). \<close>
toy_def shadow_a \<open> let x = 1; let x = 10; x + x \<close>
toy_def shadow_b \<open> let y = 1; let z = 10; z + z \<close>
lemma \<open> shadow_a = shadow_b \<close>
  unfolding shadow_a_def shadow_b_def by (rule refl)


subsection\<open> Syntax highlighting and click-to-definition (view in jEdit) \<close>

text\<open> Open this theory in jEdit and look at the cartouche arguments of the \<^verbatim>\<open>toy_def\<close> commands
below.

  \<^bold>\<open>Syntax highlighting\<close> (from the lexer's tok/tok_val Markup.T): \<^verbatim>\<open>let\<close> is a keyword,
  numerals get the numeral colour, \<^verbatim>\<open>= + *\<close> render as operators, \<^verbatim>\<open>; ( )\<close> as delimiters,
  and identifiers as free variables.

  \<^bold>\<open>Click-to-definition\<close> (from the elaborator's entity markup): ctrl-click (Cmd-click on macOS)
  any variable *use* and jEdit jumps to its binding \<^verbatim>\<open>let\<close>; hovering a use shows the entity
  tooltip. Because binding is lexical, a use resolves to the nearest enclosing binder -- so in
  \<^verbatim>\<open>nav_shadow\<close> the uses jump to the INNER \<^verbatim>\<open>let x\<close>, not the outer one. \<close>

text\<open> Every token kind in one line -- good for eyeballing the colour scheme; the two \<^verbatim>\<open>a\<close> uses
click to \<^verbatim>\<open>let a\<close>. \<close>
toy_def hi_tokens \<open> let a = 10; (a + 2) * a \<close>
thm hi_tokens_def

text\<open> Two binders, several uses -- ctrl-click any use to jump to its \<^verbatim>\<open>let\<close>. \<close>
toy_def nav_two \<open> let a = 3; let b = a * a; a + b * a \<close>
thm nav_two_def

text\<open> Shadowing: the body's uses jump to the INNER \<^verbatim>\<open>let x\<close>; the outer \<^verbatim>\<open>let x\<close> is a
separate, unused binder. \<close>
toy_def nav_shadow \<open> let x = 1; let x = 10; x * x + x \<close>
thm nav_shadow_def


subsection\<open> Inspection demos: input string, SML AST, and HOL shallow embedding \<close>

text\<open> Each ML block below parses one Toy input and shows all three layers at once: the input string,
the reified SML AST (Position.T fields omitted for readability), and the final type-checked HOL term.
In jEdit, click a block and read the Output panel -- input / AST / HOL are stacked, and the HOL line
carries full term markup (hover for types, ctrl-click constants). For the raw SML AST value including
positions, use \<^verbatim>\<open>@{make_string} ast\<close> in place of \<^verbatim>\<open>ast_str ast\<close>. \<close>

ML\<open>
local
  (* A readable renderer for the SML AST value (drops the Position.T fields). *)
  fun ast_str e =
    let
      open Toy_AST
      fun s (E_Num (i, _))       = "Num " ^ string_of_int i
        | s (E_Var (x, _))       = "Var " ^ quote x
        | s (E_Add (a, b))       = "Add (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Mul (a, b))       = "Mul (" ^ s a ^ ", " ^ s b ^ ")"
        | s (E_Let (x, a, b, _)) = "Let (" ^ quote x ^ ", " ^ s a ^ ", " ^ s b ^ ")"
    in s e end
in
  (* source -> SML AST -> checked HOL term, printing all three layers. Takes the cartouche
     Input.source directly (so PIDE markup lands on the real source), and recovers the display
     string from its content. *)
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

text\<open> A diag command wrapping toy_demo: parse the cartouche and print input / AST / HOL. Serialized
behind the same mutex as toy_def (parse_source touches the runtime's global refs). \<close>
ML\<open>
val _ = Outer_Syntax.command \<^command_keyword>\<open>toy_demo_inspect\<close>
          "Parse a Toy expression and print its input string, SML AST, and HOL term"
          (Parse.input Parse.cartouche >> (fn source =>
             Toplevel.keep (fn st =>
               with_toy_lock (fn () => toy_demo (Toplevel.context_of st) source))))
\<close>

toy_demo_inspect \<open> 1 + 2 * 3 \<close>
toy_demo_inspect \<open> (1 + 2) * (3 + 4) \<close>
toy_demo_inspect \<open> let x = 5; x * x \<close>
toy_demo_inspect \<open> let a = 2; let b = a * a; b + a \<close>
toy_demo_inspect \<open> let x = 1; let x = 10; x + x \<close>

end
