(* Rejection tests for the custom uRust parser. Each row runs `elab_urust` and requires a stable error
   substring. [FIDELITY] means the frontend also rejects; [DIVERGENT] records an under-acceptance. *)

theory Micro_Rust_Parser_Negative_Conformance
  imports Micro_Rust_Parser
  keywords
    "urust_expr_rejects" :: thy_decl
begin

section\<open> The command \<close>

text\<open> \<open>urust_expr_rejects <src> <expected>\<close> requires rejection containing \<open>expected\<close>. \<close>
ML\<open>
fun urust_rejects (source, expected) lthy =
  let
    val pos      = Input.pos_of source
    (* trim: the cartouche-spacing convention pads content with a blank on each side *)
    val expected = Symbol.trim_blanks (Input.string_of expected)
    fun fail msg = error ("urust_expr_rejects: " ^ msg ^ Position.here pos)
  in
    (* Preserve interrupts; lexer, parser, elaborator, and type errors are all valid rejections. *)
    (case Exn.result (fn () => elab_urust lthy source) () of
       Exn.Res t =>
         fail ("expected a REJECTION, but the source was ACCEPTED and elaborated to: " ^
               Syntax.string_of_term lthy t)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val msg = Runtime.exn_message exn in
             if String.isSubstring expected msg
             (* the caught message goes to PIDE / the session log, so a reader sees WHY it was rejected *)
             then (writeln ("rejected as expected: " ^ msg); lthy)
             else fail ("rejected, but not for the expected reason.\n  expected substring: " ^
                        quote expected ^ "\n  actual message: " ^ msg)
           end)
  end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
          "Assert that the uRust parser rejects a source, with the expected reason"
          (Parse.input Parse.cartouche -- Parse.input Parse.cartouche >> urust_rejects)
\<close>

section\<open> Non-associative operators \<close>

text\<open>
Grammar \<open>%nonassoc\<close> rejects chained comparisons, matching Rust and the frontend.
\<close>

urust_expr_rejects \<open> 1 == 2 == 3 \<close> \<open> syntax error found at TEQEQ \<close>
  \<comment> \<open> [FIDELITY] chained \<open>==\<close>; the frontend rejects it with an inner-syntax error. \<close>

urust_expr_rejects \<open> 1 < 2 < 3 \<close> \<open> syntax error found at TLT \<close>
  \<comment> \<open> [FIDELITY] chained \<open><\<close>; same on both sides. \<close>

section\<open> Control-flow stratification (D25 / divergence D-1) \<close>

text\<open>
Because \<open>uif\<close> is not a bare \<open>uexp\<close>, an unparenthesized \<open>if\<close>
cannot be a binary operand. The positive \<open>d1_paren_operand\<close> row covers the
parenthesized form.
\<close>

urust_expr_rejects
  \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } + \<llangle>3 :: 32 word\<rrangle> \<close>
  \<open> syntax error found at TPLUS \<close>
  \<comment> \<open> [FIDELITY] \<open>if\<close> as a \<open>+\<close> operand; the frontend rejects it too (priority mismatch). \<close>

urust_expr_rejects \<open> match_switch \<llangle>0 :: nat\<rrangle> { _ \<Rightarrow> () } () \<close>
  \<open> syntax error found at LPAR \<close>
  \<comment> \<open> [FIDELITY] a \<open>match\<close> in statement position without a \<open>;\<close>; the frontend has no such
       production either (unlike \<open>{ .. }\<close> / \<open>if\<close>, which D25 added -- rows \<open>d2_*\<close>). \<close>

section\<open> Integer literals \<close>

urust_expr_rejects \<open> 1_u7 \<close> \<open> unsupported integer-literal suffix "_u7" \<close>
  \<comment> \<open> [FIDELITY] unknown width suffix, from the single \<open>int_suffix_typ\<close> table (D29); the frontend's
       numeral-ascription syntax rejects it too. Adding \<open>u7\<close> would break this row -- deliberately. \<close>

section\<open> Patterns \<close>

urust_expr_rejects \<open> let Some(x) = \<llangle>Some (0 :: nat)\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] the site gate on the ONE pattern language (D28). The frontend rejects it as well,
       though less cleanly -- an uncaught \<open>TERM\<close> exception out of \<open>abs_tr _shallow_let_pattern\<close>. \<close>

urust_expr_rejects \<open> match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> literal patterns are not yet supported in `match_case` \<close>
  \<comment> \<open> [FIDELITY] a numeral belongs to \<open>match_switch\<close>; the frontend agrees ("Error in shallow match
       translation: numeric pattern in match_case: 0"). \<close>

urust_expr_rejects \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { NoSuchCtor(x) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> `NoSuchCtor` is not a known constructor \<close>
  \<comment> \<open> [FIDELITY] \<open>Code.is_constr\<close> decides ctor-vs-binder; the frontend agrees ("Error in case
       expression: Not a datatype constructor"). \<close>

urust_expr_rejects \<open> match_switch \<llangle>0 :: nat\<rrangle> { x \<Rightarrow> () } \<close>
  \<open> unsupported match_switch key "x" \<close>
  \<comment> \<open> [DIVERGENT] the frontend accepts a binding key under \<open>match_switch\<close>; here switch keys are
       numeral / \<open>_\<close> only (binding patterns need \<open>match_case\<close>). \<close>

urust_expr_rejects \<open> match_case \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> nested constructor pattern not yet supported \<close>
  \<comment> \<open> [DIVERGENT] frontend accepts (guarded compilation path); parser is Tier-0. Divergence D-7. \<close>

urust_expr_rejects \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { None | None \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> or-patterns are not yet supported in `match_case` \<close>
  \<comment> \<open> [DIVERGENT] frontend accepts case-pattern disjunction (\<open>match_switch\<close> keys may be or-lists here,
       \<open>match_case\<close> arms may not). Divergence D-7. \<close>

urust_expr_rejects
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { 0 \<Rightarrow> (), Some(x) \<Rightarrow> () } \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [FIDELITY] bare-match routing cannot select one lowering for numeral and constructor heads;
       the frontend reports the same mixed-match category. \<close>

urust_expr_rejects
  \<open> match \<llangle>Some (Some (0 :: nat))\<rrangle> { Some(Some(y)) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> nested constructor pattern not yet supported \<close>
  \<comment> \<open> [DIVERGENT] bare \<open>match\<close> correctly routes constructor heads to case, then reaches the
       existing Tier-0 nested-pattern diagnostic. Divergence D-7. \<close>

urust_expr_rejects
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { None | None \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> or-patterns are not yet supported in `match_case` \<close>
  \<comment> \<open> [DIVERGENT] a disjunction head is case-compatible, so bare \<open>match\<close> reaches the existing
       Tier-0 case-disjunction diagnostic. Divergence D-7. \<close>

section\<open> Calls \<close>

definition ncf1 :: \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> ncf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>

urust_expr_rejects \<open> zz(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] the arity cap is ONE policy number derived from the frontend's surface lowering (D29);
       the frontend rejects 15 args too ("Undefined constant: _urust_shallow_fun_with_args"). \<close>

urust_expr_rejects \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)(\<llangle>2 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at LPAR \<close>
  \<comment> \<open> [FIDELITY] curried application \<open>f(a)(b)\<close>: rejected by both (a call result is not a callee). \<close>

urust_expr_rejects \<open> (ncf1)(\<llangle>1 :: 64 word\<rrangle>) \<close> \<open> syntax error found at LPAR \<close>
  \<comment> \<open> [FIDELITY] parenthesised callee \<open>(g)(x)\<close>: rejected by both (\<open>urust_callable\<close> has no paren form). \<close>

section\<open> Lexer and whole-input failures \<close>

urust_expr_rejects \<open> 1 @ 2 \<close> \<open> unexpected input "@" \<close>
  \<comment> \<open> [FIDELITY] the lexer's \<open><INITIAL>.\<close> catch-all aborts with a POSITIONED error
       (\<open>URust_Err.lex_error\<close>) rather than looping or silently dropping the character; the frontend
       rejects \<open>@\<close> too. This row is what keeps that catch-all honest. \<close>

urust_expr_rejects \<open> { () \<close> \<open> syntax error found at EOF \<close>
  \<comment> \<open> [FIDELITY] unbalanced brace -- input must be consumed to EOF by a complete derivation. \<close>

urust_expr_rejects \<open> {} \<close> \<open> syntax error found at TRBRACE \<close>
  \<comment> \<open> [FIDELITY] the current frontend also rejects an empty block; real Rust permits it. \<close>

urust_expr_rejects \<open> \<close> \<open> empty expression \<close>
  \<comment> \<open> [FIDELITY] \<open>parse_source\<close> returns NONE on blank input; the frontend's empty bracket is an
       inner-syntax error. \<close>

section\<open> Under-accepted constructs (frontend accepts) \<close>

text\<open>
These rows pin current rejections of frontend-accepted syntax. Move each to positive
conformance when implemented.
\<close>

urust_expr_rejects \<open> \<llangle>0 :: nat\<rrangle>.f \<close> \<open> syntax error found at EOF \<close>
  \<comment> \<open> [DIVERGENT] D-6: \<open>.\<close> must be followed by a method call (\<open>TDOT IDENT LPAR\<close>), so a bare field
       access is a parse error. The frontend PARSES it (lowering to a lens focus \<open>focus_lens_const f\<close>)
       and here fails only later, for the unrelated reason that no field notation \<open>f\<close> is registered. \<close>

end
