theory Micro_Rust_Parser_Command
  imports
    Micro_Rust_Parser_Grammar
    Micro_Rust_Parser_Elaboration
  keywords
    "urust_expr" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
It adds no attributes, keeping generated definitions out of the global simp set.
\<close>
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

end
