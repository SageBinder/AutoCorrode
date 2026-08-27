(* Rejection tests for the custom uRust parser. Normal rows require both `elab_urust` and the existing
   frontend to reject; the new parser's error must contain a stable substring. [DIVERGENT] rows use the
   parser-only command to record an intentional acceptance-boundary difference. *)

theory Micro_Rust_Parser_Negative_Conformance
  imports Struct_Ambiguity_Left Struct_Ambiguity_Right
  keywords
    "urust_expr_rejects" :: thy_decl
    and "urust_expr_rejects_parser_only" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr_rejects source expected\<close> requires both frontends to reject and
checks the new parser's reason. The parser-only variant is reserved for documented
acceptance-boundary differences.
\<close>
ML\<open>
fun negative_frontend_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (negative_frontend_source "()")

fun urust_rejects check_frontend (source, expected) lthy =
  let
    val pos      = Input.pos_of source
    (* trim: the cartouche-spacing convention pads content with a blank on each side *)
    val expected = Symbol.trim_blanks (Input.string_of expected)
    fun fail msg = error ("urust_expr_rejects: " ^ msg ^ Position.here pos)

    fun check_parser_rejection () =
      (* Lexer, parser, elaborator, and type errors are all valid new-parser rejections. *)
      (case Exn.result (fn () => elab_urust lthy source) () of
         Exn.Res t =>
           fail ("expected the new parser to reject, but it accepted and elaborated to: " ^
                 Syntax.string_of_term lthy t)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val msg = Runtime.exn_message exn in
               if String.isSubstring expected msg
               then writeln ("new parser rejected as expected: " ^ msg)
               else fail ("new parser rejected, but not for the expected reason.\n" ^
                          "  expected substring: " ^ quote expected ^
                          "\n  actual message: " ^ msg)
             end)

    fun check_frontend_rejection () =
      (case Exn.result (Syntax.read_term lthy)
              (negative_frontend_source (Input.string_of source)) of
         Exn.Res t =>
           fail ("expected the existing frontend to reject, but it accepted and elaborated to: " ^
                 Syntax.string_of_term lthy t)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else writeln ("existing frontend rejected as expected: " ^ Runtime.exn_message exn))

    val _ = check_parser_rejection ()
    val _ = if check_frontend then check_frontend_rejection () else ()
  in
    lthy
  end

val rejection_args = Parse.input Parse.cartouche -- Parse.input Parse.cartouche

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
          "Assert that both uRust frontends reject; check the new parser's reason"
          (rejection_args >> urust_rejects true)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects_parser_only\<close>
          "Assert that the new uRust parser rejects without checking the existing frontend"
          (rejection_args >> urust_rejects false)
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

datatype negative_struct_fixture =
  NegativeStruct (negative_left: nat) (negative_right: nat)

urust_expr_rejects \<open> let Some(x) = \<llangle>Some (0 :: nat)\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] the site gate on the ONE pattern language (D28). The frontend rejects it as well,
       though less cleanly -- an uncaught \<open>TERM\<close> exception out of \<open>abs_tr _shallow_let_pattern\<close>. \<close>

urust_expr_rejects
  \<open> let (Some(x), y) = \<llangle>(Some (0 :: nat), (True, TNil))\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] tuple binders recurse through the irrefutability gate, so the constructor component
       is rejected at its own source position. \<close>

urust_expr_rejects \<open> let true = true; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] boolean value patterns are refutable. \<close>

urust_expr_rejects \<open> const "ok" = "ok"; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] string value patterns are refutable. \<close>

urust_expr_rejects
  \<open> let \<llangle>2 :: nat\<rrangle> = \<llangle>2 :: nat\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns are refutable. \<close>

urust_expr_rejects
  \<open> let &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] borrow-pattern stripping is a case-pattern translation in the frontend, not an
       irrefutable let/const rule. \<close>

urust_expr_rejects
  \<open> match \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> numeric pattern in match_case: 1 \<close>
  \<comment> \<open> [FIDELITY] bare-match routing unwraps groups but not borrow patterns, so this selects case
       lowering and reaches the frontend's numeric-case rejection. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>(0 :: nat, (True, TNil))\<rrangle> { (x, y) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] tuple patterns require case lowering; explicit \<open>match_switch\<close> remains
       first-order and rejects them with its stable positioned diagnostic. \<close>

urust_expr_rejects \<open> match_switch true { true \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] boolean patterns require equality-guard case lowering. \<close>

urust_expr_rejects \<open> match_switch "ok" { "ok" \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] string patterns require equality-guard case lowering. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { \<llangle>2 :: nat\<rrangle> \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns require equality-guard case lowering. \<close>

urust_expr_rejects \<open> (\<llangle>1 :: nat\<rrangle>,) \<close> \<open> syntax error found at RPAR \<close>
  \<comment> \<open> [FIDELITY] singleton tuples are outside the current frontend tuple grammar. \<close>

urust_expr_rejects
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>,) \<close>
  \<open> syntax error found at RPAR \<close>
  \<comment> \<open> [FIDELITY] trailing-comma tuples are outside the current frontend tuple grammar. \<close>

urust_expr_rejects \<open> let () = (); () \<close> \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] unit is an expression but not a pattern in the current frontend. \<close>

urust_expr_rejects \<open> match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric pattern in match_case: 0 \<close>
  \<comment> \<open> [FIDELITY] a numeral belongs to \<open>match_switch\<close>; the frontend agrees ("Error in shallow match
       translation: numeric pattern in match_case: 0"). \<close>

urust_expr_rejects \<open> match_case \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric pattern in match_case: 1 \<close>
  \<comment> \<open> [FIDELITY] literal \<open>1\<close> has the same dedicated case-pattern node and rejection boundary as
       literal \<open>0\<close>. \<close>

urust_expr_rejects \<open> match_case \<llangle>2 :: nat\<rrangle> { 2 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric pattern in match_case: 2 \<close>
  \<comment> \<open> [FIDELITY] the frontend's attempted guarded lowering retains the raw token and rejects with
       \<open>Undefined constant: "2"\<close>; the parser gives the same accept-set boundary a positioned diagnostic. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(2) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric pattern in match_case: 2 \<close>
  \<comment> \<open> [FIDELITY] constructor-nested numerals hit the same frontend raw-token rejection. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { 2 if True \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> guards are not supported in explicit `match_switch` \<close>
  \<comment> \<open> [FIDELITY] guards force bare \<open>match\<close> to case lowering, but the explicit switch form rejects
       them rather than changing lowering. \<close>

urust_expr_rejects \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { NoSuchCtor(x) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> `NoSuchCtor` is not a known constructor \<close>
  \<comment> \<open> [FIDELITY] \<open>Code.is_constr\<close> decides ctor-vs-binder; the frontend agrees ("Error in case
       expression: Not a datatype constructor"). \<close>

urust_expr_rejects_parser_only \<open> match_switch \<llangle>0 :: nat\<rrangle> { x \<Rightarrow> () } \<close>
  \<open> unsupported match_switch key "x" \<close>
  \<comment> \<open> [DIVERGENT] the frontend accepts a binding key under \<open>match_switch\<close>; here switch keys are
       numeral / \<open>_\<close> only (binding patterns need \<open>match_case\<close>). \<close>

urust_expr_rejects
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { 0 \<Rightarrow> (), Some(x) \<Rightarrow> () } \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [FIDELITY] bare-match routing cannot select one lowering for numeral and constructor heads;
       the frontend reports the same mixed-match category. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(1..2..3) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> range patterns are non-associative \<close>
  \<comment> \<open> [FIDELITY] range patterns are non-associative. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>[1 :: nat]\<rrangle> { [.., ..] \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> slice pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a slice has at most one rest marker. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, negative_left: y, .. } \<Rightarrow> x } \<close>
  \<open> has duplicate field "negative_left" \<close>
  \<comment> \<open> [FIDELITY] duplicate struct fields reject at the repeated field. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x } \<Rightarrow> x } \<close>
  \<open> is missing field(s): negative_right \<close>
  \<comment> \<open> [FIDELITY] omitted fields require a struct rest marker. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { unknown: x, .. } \<Rightarrow> x } \<close>
  \<open> has unknown field "unknown" \<close>
  \<comment> \<open> [FIDELITY] selector metadata validates struct field names. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NoSuchStruct { field: x, .. } \<Rightarrow> x } \<close>
  \<open> no matching constructor or single-constructor record/datatype found \<close>
  \<comment> \<open> [FIDELITY] struct heads must resolve through constructor/type metadata. \<close>

urust_expr_rejects
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { .., .. } \<Rightarrow> () } \<close>
  \<open> struct pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a struct has at most one rest entry. \<close>

urust_expr_rejects
  \<open> let whole @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] aliases remain outside irrefutable let binders. \<close>

urust_expr_rejects
  \<open> const (1..=2) = \<llangle>1 :: nat\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] ranges remain outside irrefutable const binders. \<close>

urust_expr_rejects
  \<open> let [x, ..] = \<llangle>[1 :: nat]\<rrangle>; x \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] slices remain outside irrefutable let binders. \<close>

urust_expr_rejects
  \<open> const NegativeStruct { negative_left: x, .. } = \<llangle>NegativeStruct 1 2\<rrangle>; () \<close>
  \<open> refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] structs remain outside irrefutable const binders. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>Some (1 :: nat)\<rrangle> { whole @ Some(x) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] aliases require case lowering. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1..=2 \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] ranges require case lowering. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>[1 :: nat]\<rrangle> { [x, ..] \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] slices require case lowering. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, .. } \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] struct patterns require case lowering. \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] explicit switch conversion accepts grouped numeric keys but has no borrow-pattern
       conversion rule. \<close>

urust_expr_rejects_parser_only
  \<open> match_case \<llangle>undefined\<rrangle> { AmbiguousStruct { ambiguous_field: x } \<Rightarrow> x } \<close>
  \<open> Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct \<close>
  \<comment> \<open> [DIVERGENT] the existing frontend silently picks one of two same-basename constructors.
       The new parser rejects and reports their qualified identities instead. \<close>

section\<open> Calls \<close>

definition ncf1 :: \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> ncf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>

urust_expr_rejects \<open> zz(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] the arity cap is ONE policy number derived from the frontend's surface lowering (D29);
       the frontend rejects 15 args too ("Undefined constant: _urust_shallow_fun_with_args"). \<close>

urust_expr_rejects
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] 14 explicit method arguments plus the prepended receiver exceed
       the inclusive \<open>funcall14\<close> limit by one. \<close>

urust_expr_rejects
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>
  \<comment> \<open> [FIDELITY] the 15-explicit-argument boundary lowers to 16 total arguments. \<close>

urust_expr_rejects \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)(\<llangle>2 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at LPAR \<close>
  \<comment> \<open> [FIDELITY] curried application \<open>f(a)(b)\<close>: rejected by both (a call result is not a callee). \<close>

urust_expr_rejects \<open> (ncf1)(\<llangle>1 :: 64 word\<rrangle>) \<close> \<open> syntax error found at LPAR \<close>
  \<comment> \<open> [FIDELITY] parenthesised callee \<open>(g)(x)\<close>: rejected by both (\<open>urust_callable\<close> has no paren form). \<close>

section\<open> Lexer and whole-input failures \<close>

urust_expr_rejects \<open> "bad\q" \<close> \<open> bad escape character in string \<close>
  \<comment> \<open> [FIDELITY] malformed escapes are rejected by the same Isabelle string decoder. \<close>

urust_expr_rejects \<open> "unterminated \<close> \<open> malformed or unterminated string literal \<close>
  \<comment> \<open> [FIDELITY] the opening quote receives a positioned lexer diagnostic. \<close>

urust_expr_rejects
  \<open> match_case true { \<epsilon>\<open>Bool_Type.true\<close> \<Rightarrow> () } \<close>
  \<open> EXPRAQ TARROW \<close>
  \<comment> \<open> [FIDELITY] expression antiquotation remains expression-only. \<close>

urust_expr_rejects \<open> 1 @ 2 \<close> \<open> syntax error found at TAT \<close>
  \<comment> \<open> [FIDELITY] \<open>@\<close> is pattern-only; expression position rejects it after lexing. \<close>

urust_expr_rejects \<open> { () \<close> \<open> syntax error found at EOF \<close>
  \<comment> \<open> [FIDELITY] unbalanced brace -- input must be consumed to EOF by a complete derivation. \<close>

urust_expr_rejects \<open> {} \<close> \<open> syntax error found at TRBRACE \<close>
  \<comment> \<open> [FIDELITY] the current frontend also rejects an empty block; real Rust permits it. \<close>

urust_expr_rejects \<open> \<close> \<open> empty expression \<close>
  \<comment> \<open> [FIDELITY] \<open>parse_source\<close> returns NONE on blank input; the frontend's empty bracket is an
       inner-syntax error. \<close>

end
