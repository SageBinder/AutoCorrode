(* Toy 0 of the custom uRust parser effort: a verbatim port of the AFP Calc example.

   Purpose: get the AFP Isabelle_Lex-Yacc framework building and running INSIDE our own
   session, as a sandbox + debugging reference before writing any uRust grammar. This is the
   first of four INDEPENDENT toy theories (each imports only Isabelle_Lex-Yacc.LexYacc and stands
   alone -- later toys are supersets by copy, not by import), split out of the original monolithic
   Toy_Lex_Yacc.thy:

     * Toy_Lex_Yacc0 (Calc, THIS file) -- a print-only calculator, proving the ml_lex_yacc
                        workflow + PIDE markup end-to-end here.
     * Toy_Lex_Yacc1 (Toy)  -- a binder-bearing arithmetic+let language: the parse -> AST -> HOL ->
                        define seam, dummyT typing, Free+Term.lambda binder capture, the command
                        mutex, and PIDE highlighting + click-to-definition.
     * Toy_Lex_Yacc2 (Toy2) -- extends Toy with <<HOL>> antiquotations (with capture) and deferred
                        name resolution against the HOL context; carries the corrected symbol
                        position layer.
     * Toy_Lex_Yacc3 (Toy3) -- extends Toy2 with the grammar mechanics the real parser needs:
                        unary operators via %prec, precedence-resolved conflicts, and comma-argument
                        function-call syntax lowered to an applied head (the funcallN shape).

   (The old Part 3 "symbol-lexing spike" is retired -- its question is settled and captured in
   Toy_Lex_Yacc2's corrected position layer and in notes/isabelle-lex-yacc-notes.md.)

   NOTE ON ENCODING: these files use the ASCII escape form for Isabelle symbols (\<open>  /  \<close>
   etc.), NOT raw UTF-8 glyphs. `isabelle build` rejects raw UTF-8 cartouche delimiters (they
   parse as "malformed"), even though ic2/PIDE tolerates them. See notes/isabelle-lex-yacc-notes.md.

   See notes/urust-parser-plan.md (Phase 0). *)

theory Toy_Lex_Yacc0
  imports "Isabelle_Lex-Yacc.LexYacc"
  keywords
    "calc" :: diag
begin

section\<open> Calc: a verbatim AFP example (print-only) \<close>

ml_lex_yacc [verbose] "Calc" where
lex_definitions\<open>
alpha=[A-Za-z];
digit=[0-9];
ws = [\ \t\r];
\<close>
lex_rules\<open>
\n       => (lex());
{ws}+    => (lex());

{digit}+ => (tok_val (yypos, yytext, Markup.numeral, "NUM", "", Tokens.NUM, valOf (Int.fromString yytext)));

"+"      => (tok (yypos, yytext, Markup.keyword2, "PLUS", "", Tokens.PLUS));
"*"      => (tok (yypos, yytext, Markup.keyword2, "TIMES", "", Tokens.TIMES));
";"      => (tok (yypos, yytext, Markup.delimiter, "SEMI", "", Tokens.SEMI));

{alpha}+ => (if yytext="print"
                 then tok (yypos, yytext, Markup.keyword1, "PRINT", "", Tokens.PRINT)
                 else tok_val (yypos, yytext, Markup.free, "ID", "", Tokens.ID, yytext)
            );

"-"      => (tok (yypos, yytext, Markup.keyword2, "SUB", "", Tokens.SUB));
"^"      => (tok (yypos, yytext, Markup.keyword2, "CARAT", "", Tokens.CARAT));
"/"      => (tok (yypos, yytext, Markup.keyword2, "DIV", "", Tokens.DIV));
.        => (lex());
\<close>
and yacc_user_declarations\<open>
fun lookup "bogus" = 10000
  | lookup s = 0
\<close>
yacc_definitions\<open>
%eop EOF SEMI

%left SUB PLUS
%left TIMES DIV
%right CARAT

%term ID of string | NUM of int | PLUS | TIMES | PRINT |
      SEMI | EOF | CARAT | DIV | SUB
%nonterm EXP of int | START of int option


%subst PRINT for ID
%prefer PLUS TIMES DIV SUB
%keyword PRINT SEMI

%noshift EOF
%value ID ("bogus")
%verbose
\<close>
yacc_rules\<open>
  START : PRINT EXP (print (Int.toString EXP);
                     print "\n";
                     SOME EXP)
        | EXP (SOME EXP)
        | (NONE)
  EXP : NUM             (NUM)
      | ID              (lookup ID)
      | EXP PLUS EXP    (EXP1+EXP2)
      | EXP TIMES EXP   (EXP1*EXP2)
      | EXP DIV EXP     (EXP1 div EXP2)
      | EXP SUB EXP     (EXP1-EXP2)
      | EXP CARAT EXP   (let fun e (m,0) = 1
                                | e (m,l) = m*e(m,l-1)
                         in e (EXP1,EXP2)
                         end)
\<close>

text\<open> A simple Isar-toplevel command that prints the result of parsing. \<close>
ML\<open>
fun calc source thy =
    let
      val ctxt = Proof_Context.init_global thy
      val _ = writeln((Int.toString (the (Calc.parse_source ctxt source))))
    in thy end

val _ = Outer_Syntax.command \<^command_keyword>\<open>calc\<close>
        "A simple inline calculator"
        (Parse.input Parse.cartouche >> (fn source => Toplevel.theory (calc source)))
\<close>

calc\<open>
1
  /
    3
   * (201 - 7)
\<close>

end
