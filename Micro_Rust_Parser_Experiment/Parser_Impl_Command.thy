theory Parser_Impl_Command
  imports
    Parser_Impl_Diagnostics
    Parser_Impl_Translate
  keywords
    "urust_expr" :: thy_decl
    and "urust_expr_with_check" :: thy_decl
    and "urust_expr_with_check'" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr NAME src\<close> parses, elaborates, checks once, and defines \<open>NAME\<close>.
The standard Isabelle definition mechanism supplies one default code equation, but the command
adds no custom attributes and keeps generated definitions out of the global simp set.

\<open>urust_expr_with_check NAME src\<close> additionally checks the resulting definition
against the existing \<open>\<lbrakk>src\<rbrakk>\<close> frontend by definition unfolding and
\<open>refl\<close>, and records the theorem as \<open>NAME_conformance\<close>.

\<open>urust_expr_with_check' NAME new_src old_term\<close> performs the same check with
\<open>new_src\<close> sent to the new parser and the explicit
\<open>\<lbrakk>old_src\<rbrakk>\<close> in \<open>old_term\<close> sent to the existing frontend.
\<close>
ML\<open>
(* THE pipeline, exported: every uRust command runs source through exactly this function, so the
   definition commands (`urust_expr`, `urust_expr_with_check`, `urust_expr_with_check'`) and the
   negative harness (`urust_expr_rejects`, Parser_Test_Negative_Conformance) can never drift on
   WHAT they exercise -- only on how they interpret success/failure. Raises (positioned) on any
   rejection: lexer (URust_Err.lex_error), yacc (parse_source's print_error), elaborator, or check_term.
   ONLY `parse_source` touches the Isabelle_lex_yacc global refs, so only it is serialized; elaboration and
   check_term are pure w.r.t. those, and holding the lock across them would serialize the (slower)
   type-checking of every uRust command theory-wide. *)
fun elab_urust lthy source : term =
  (case
      (Parser_Utils.with_parser_lock
        (fn () => URust_Diagnostics.parse_source lthy source)) of
     SOME ast => Syntax.check_term lthy (URust_Translate.mk_closed lthy ast)
   | NONE => error ("urust_expr: empty expression" ^ Position.here (Input.pos_of source)))

fun define_urust_result (binding, source) lthy =
  let
    val term = elab_urust lthy source
    val name = Binding.name_of binding
  in
    Specification.definition
      (SOME (binding, NONE, NoSyn)) [] []
      ((Thm.def_binding binding, []),
        Logic.mk_equals
          (Free (name, fastype_of term), term)) lthy
  end

fun define_urust args lthy = snd (define_urust_result args lthy)

fun old_frontend_source source = "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"

fun define_urust_with_frontend_check (binding, new_source, old_frontend_source) lthy =
  let
    val ((lhs, (_, def_thm)), lthy') =
      define_urust_result (binding, new_source) lthy
    val old_frontend =
      Syntax.parse_term lthy' old_frontend_source
    val equality =
      Syntax.check_term lthy'
        (Const (\<^const_name>\<open>HOL.eq\<close>, dummyT) $ lhs $ old_frontend)
    val conformance =
      Goal.prove lthy' [] [] (HOLogic.mk_Trueprop equality)
        (fn {context = ctxt, ...} =>
          Local_Defs.unfold_tac ctxt
            [def_thm, @{thm urust_admin_let_def}] THEN
          resolve_tac ctxt [@{thm refl}] 1)
    val (_, lthy'') =
      Local_Theory.note
        ((Binding.suffix_name "_conformance" binding, []), [conformance]) lthy'
  in lthy'' end

fun define_urust_with_check (binding, source) =
  define_urust_with_frontend_check (binding, source, old_frontend_source source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr\<close>
          "Parse a uRust expression and define it as a HOL constant"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check\<close>
          "Define a uRust expression and check it against the existing frontend by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) >>
            define_urust_with_check)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_with_check'\<close>
          "Define a uRust expression and check it against an explicit existing-frontend term by refl"
          (Parse.binding --
            (Parse.token Parse.cartouche >>
              Parser_Lex_Util.cartouche_source) --
            Parse.term >>
            (fn ((binding, new_source), old_frontend_source) =>
              define_urust_with_frontend_check (binding, new_source, old_frontend_source)))
\<close>

end
