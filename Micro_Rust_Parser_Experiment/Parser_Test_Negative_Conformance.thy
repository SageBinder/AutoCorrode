(* Rejection tests for the custom uRust parser. Normal rows require both `elab_urust` and the existing
   frontend to reject; the new parser's error must contain a stable substring. [DIVERGENT] rows use the
   new-parser-only command to record an intentional acceptance-boundary difference. *)

theory Parser_Test_Negative_Conformance
  imports Struct_Ambiguity_Left Struct_Ambiguity_Right
  keywords
    "urust_expr_rejects" :: thy_decl
    and "new_urust_rejects" :: thy_decl
begin

section\<open> The command \<close>

text\<open>
\<open>urust_expr_rejects fidelity source expected\<close> requires both frontends to reject and
checks the new parser's reason. The new-parser-only variant requires either the executable
\<open>divergent\<close> tag for an acceptance-boundary difference or \<open>audit\<close> for a custom-parser
invariant whose old-frontend behavior is deliberately not part of the row. The tags are validated
locally by this negative-test command; bracketed comment labels remain explanatory only.
\<close>
ML\<open>
fun negative_frontend_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (negative_frontend_source "()")

datatype rejection_tag = Fidelity | Divergent | Audit

fun validate_rejection_tag check_frontend tag =
  (case (check_frontend, tag) of
     (true, Fidelity) => ()
   | (true, _) =>
       error "urust_expr_rejects requires the `fidelity` tag"
   | (false, Fidelity) =>
       error "new_urust_rejects requires the `divergent` or `audit` tag"
   | (false, _) => ())

fun parse_rejection_tag (name, pos) =
  (case name of
     "fidelity" => Fidelity
   | "divergent" => Divergent
   | "audit" => Audit
   | _ =>
       error
         ("unknown rejection tag " ^ quote name ^
           "; expected `fidelity`, `divergent`, or `audit`" ^
           Position.here pos))

fun urust_rejects check_frontend ((tag, source), expected) lthy =
  let
    val _ = validate_rejection_tag check_frontend tag
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
  in lthy end

val rejection_args =
  (Parse.name_position >> parse_rejection_tag) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source) --
    (Parse.token Parse.cartouche >>
      Parser_Lex_Util.cartouche_source)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>urust_expr_rejects\<close>
          "Assert that both uRust frontends reject; check the new parser's reason"
          (rejection_args >> urust_rejects true)

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>new_urust_rejects\<close>
          "Assert that the new uRust parser rejects without checking the existing frontend"
          (rejection_args >> urust_rejects false)
\<close>

section\<open> Non-associative operators \<close>

text\<open>
Grammar \<open>%nonassoc\<close> rejects chained comparisons, matching Rust and the frontend.
\<close>

urust_expr_rejects fidelity \<open> 1 == 2 == 3 \<close> \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] chained \<open>==\<close>; the frontend rejects it with an inner-syntax error. \<close>

urust_expr_rejects fidelity \<open> 1 < 2 < 3 \<close> \<open> syntax error found at < \<close>
  \<comment> \<open> [FIDELITY] chained \<open><\<close>; same on both sides. \<close>

section\<open> Reference-prefix precedence \<close>

text\<open>
The frontend gives \<open>!\<close> a tighter prefix tier than borrow and dereference.
Parentheses make the converse composition explicit; its positive row is
\<open>ref_not_grouped_deref\<close>.
\<close>

urust_expr_rejects fidelity \<open> ! *r \<close> \<open> syntax error found at * \<close>
  \<comment> \<open> [FIDELITY] an unparenthesized dereference cannot be the operand of tighter \<open>!\<close>. \<close>

urust_expr_rejects fidelity \<open> ! &r \<close> \<open> syntax error found at & \<close>
  \<comment> \<open> [FIDELITY] borrow has the same boundary relative to \<open>!\<close>. \<close>

section\<open> Control-flow stratification (D25 / divergence D-1) \<close>

text\<open>
Because \<open>uif\<close> is not a bare \<open>uexp\<close>, an unparenthesized \<open>if\<close>
cannot be a binary operand. The positive \<open>d1_paren_operand\<close> row covers the
parenthesized form.
\<close>

urust_expr_rejects fidelity
  \<open> if \<llangle>True\<rrangle> { \<llangle>1 :: 32 word\<rrangle> } else { \<llangle>2 :: 32 word\<rrangle> } + \<llangle>3 :: 32 word\<rrangle> \<close>
  \<open> syntax error found at + \<close>
  \<comment> \<open> [FIDELITY] \<open>if\<close> as a \<open>+\<close> operand; the frontend rejects it too (priority mismatch). \<close>

urust_expr_rejects fidelity \<open> match_switch \<llangle>0 :: nat\<rrangle> { _ \<Rightarrow> () } () \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] a \<open>match\<close> in statement position without a \<open>;\<close>; the frontend has no such
       production either (unlike \<open>{ .. }\<close> / \<open>if\<close>, which D25 added -- rows \<open>d2_*\<close>). \<close>

section\<open> Integer literals \<close>

urust_expr_rejects fidelity \<open> 1_u7 \<close> \<open> unsupported integer-literal suffix "_u7" \<close>
  \<comment> \<open> [FIDELITY] unknown width suffix, from the single term-layer suffix table (D29); the frontend's
       numeral-ascription syntax rejects it too. Adding \<open>u7\<close> would break this row -- deliberately. \<close>

section\<open> Comments \<close>

urust_expr_rejects fidelity \<open> /* block comments remain unsupported */ () \<close>
  \<open> / \<close>
  \<comment> \<open> [FIDELITY] this increment adds only Rust line comments; neither frontend accepts block
       comments. \<close>

section\<open> Unsupported Rust-compatible integer suffixes \<close>

urust_expr_rejects fidelity \<open> 1u128 \<close> \<open> unsupported integer-literal suffix "u128" \<close>
  \<comment> \<open> [FIDELITY] a glued unsupported decimal width is one numeric token and is rejected at its
       suffix by the sole term-layer table. \<close>

urust_expr_rejects fidelity \<open> 0xffu128 \<close> \<open> unsupported integer-literal suffix "u128" \<close>
  \<comment> \<open> [FIDELITY] the same longest-match and positioned suffix diagnostic apply after hex digits. \<close>

urust_expr_rejects fidelity \<open> 1i32 \<close> \<open> unsupported integer-literal suffix "i32" \<close>
  \<comment> \<open> [FIDELITY] signed integer types are not added by the glued-suffix syntax improvement. \<close>

urust_expr_rejects fidelity \<open> 0xffi32 \<close> \<open> unsupported integer-literal suffix "i32" \<close>
  \<comment> \<open> [FIDELITY] unsupported signed suffixes also stay intact after a hex literal. \<close>

urust_expr_rejects fidelity \<open> 1u32tail \<close> \<open> unsupported integer-literal suffix "u32tail" \<close>
  \<comment> \<open> [FIDELITY] lexical longest-match must not accept the supported prefix and leave an identifier. \<close>

urust_expr_rejects fidelity \<open> 0xffu8tail \<close> \<open> unsupported integer-literal suffix "u8tail" \<close>
  \<comment> \<open> [FIDELITY] hexadecimal suffix candidates obey the same whole-token boundary. \<close>

urust_expr_rejects fidelity \<open> 1foo \<close> \<open> unsupported integer-literal suffix "foo" \<close>
  \<comment> \<open> [FIDELITY] immediate identifier adjacency is a suffix candidate, not a second token. \<close>

urust_expr_rejects fidelity \<open> 0xffvalue \<close> \<open> unsupported integer-literal suffix "value" \<close>
  \<comment> \<open> [FIDELITY] a non-hex identifier start establishes the corresponding hex suffix boundary. \<close>

urust_expr_rejects fidelity \<open> 1 foo \<close> \<open> syntax error found at <identifier> \<close>
  \<comment> \<open> [FIDELITY] whitespace terminates the numeric token; the following identifier is not swallowed. \<close>

urust_expr_rejects fidelity \<open> 1_000 \<close> \<open> unsupported integer-literal suffix "_000" \<close>
  \<comment> \<open> [FIDELITY] numeric separators remain out of scope and do not become decimal digits. \<close>

urust_expr_rejects fidelity \<open> 0xff_00 \<close> \<open> unsupported integer-literal suffix "_00" \<close>
  \<comment> \<open> [FIDELITY] numeric separators remain out of scope for hexadecimal literals too. \<close>

urust_expr_rejects fidelity \<open> 1_ \<close> \<open> unsupported integer-literal suffix "_" \<close>
  \<comment> \<open> [FIDELITY] a compatibility underscore must introduce one of the supported suffixes. \<close>

urust_expr_rejects fidelity \<open> 0xff_ \<close> \<open> unsupported integer-literal suffix "_" \<close>
  \<comment> \<open> [FIDELITY] a trailing underscore is not an empty hexadecimal suffix. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1u8 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> <integer> => \<close>
  \<comment> \<open> [FIDELITY] suffixed decimal literals remain outside the pattern grammar. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 0xffu8 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> <integer> => \<close>
  \<comment> \<open> [FIDELITY] suffixed hexadecimal literals preserve the same pattern boundary. \<close>

section\<open> Patterns \<close>

datatype negative_struct_fixture =
  NegativeStruct (negative_left: nat) (negative_right: nat)

datatype negative_more_selector_fixture =
  NegativeMoreSelector (negative_more_required: nat) (more: nat)

record negative_record_fixture =
  negative_record_left :: nat
  negative_record_right :: nat

subsection\<open> Cycle 1 atomic binder validation (C1-I1--C1-I3) \<close>

text\<open>
Every alternative is validated before Resolution allocates any local. These rows pin duplicate
diagnostics across the recursive shapes and binding sites that currently consume patterns.
\<close>

new_urust_rejects divergent
  \<open> let (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [DIVERGENT] the custom parser rejects the duplicate before allocating either binder. \<close>

new_urust_rejects audit
  \<open> const x @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] aliases participate in the same atomic duplicate-binder validation. \<close>

new_urust_rejects audit
  \<open> for (x, x) in \<llangle>[(1 :: nat, (2 :: nat, TNil))]\<rrangle> { () } \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] loop binders validate recursively before allocating locals. \<close>

new_urust_rejects audit
  \<open> let mut (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] mutable tuple binders retain the atomic validation boundary. \<close>

new_urust_rejects audit
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some((x, x)) =
      \<llangle>Some (1 :: nat, (2 :: nat, TNil))\<rrangle> { () }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] while-let validates nested constructor payloads atomically. \<close>

new_urust_rejects audit
  \<open> match_case \<llangle>[1 :: nat, 2]\<rrangle> { [x, x] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] slice children share the source arm's single validation pass. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct(x, x) \<Rightarrow> x
    }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] positional constructor children share the atomic binder set. \<close>

new_urust_rejects audit
  \<open>
    match_case \<llangle>NegativeStruct 1 2\<rrangle> {
      NegativeStruct { negative_left: x, negative_right: x } \<Rightarrow> x
    }
  \<close>
  \<open> duplicate pattern binder "x" \<close>
  \<comment> \<open> [AUDIT] struct-field children share the atomic binder set. \<close>

urust_expr_rejects fidelity \<open> let Some(x) = \<llangle>Some (0 :: nat)\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] the site gate on the ONE pattern language (D28). The frontend rejects it as well,
       though less cleanly -- an uncaught \<open>TERM\<close> exception out of \<open>abs_tr _shallow_let_pattern\<close>. \<close>

urust_expr_rejects fidelity
  \<open> let (Some(x), y) = \<llangle>(Some (0 :: nat), (True, TNil))\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] tuple binders recurse through the irrefutability gate, so the constructor component
       is rejected at its own source position. \<close>

urust_expr_rejects fidelity \<open> let true = true; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] boolean value patterns are refutable. \<close>

urust_expr_rejects fidelity \<open> const "ok" = "ok"; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] string value patterns are refutable. \<close>

urust_expr_rejects fidelity
  \<open> let \<llangle>2 :: nat\<rrangle> = \<llangle>2 :: nat\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns are refutable. \<close>

urust_expr_rejects fidelity
  \<open> let mut (x) = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] the frontend accepts a scalar mutable identifier or an actual top-level tuple,
       not a grouped scalar. The diagnostic is positioned at the grouped pattern. \<close>

urust_expr_rejects fidelity
  \<open> let mut Some(x) = \<llangle>Some (1 :: nat)\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] constructor patterns are not mutable binding heads. \<close>

urust_expr_rejects fidelity
  \<open> let mut &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current binding semantics. \<close>

urust_expr_rejects fidelity
  \<open> let mut whole @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] aliases are rejected by the mutable-site gate. \<close>

urust_expr_rejects fidelity
  \<open> let mut [x, ..] = \<llangle>[1 :: nat]\<rrangle>; x \<close>
  \<open> invalid mutable binding pattern \<close>
  \<comment> \<open> [FIDELITY] slice patterns are rejected by the mutable-site gate. \<close>

urust_expr_rejects fidelity
  \<open> let mut (Some(x), y) = \<llangle>(Some (1 :: nat), (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] top-level tuple \<open>mut\<close> is erased, after which the ordinary recursive
       irrefutability gate rejects a constructor component at its own position. \<close>

urust_expr_rejects fidelity
  \<open> let &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current binding semantics. \<close>

new_urust_rejects divergent
  \<open> const &x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] const bindings share the same non-erasing reference-pattern gate. \<close>

new_urust_rejects divergent
  \<open> match \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] the old frontend erases this reference-pattern syntax. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(&x) \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] nested case reference patterns are rejected before lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>(0 :: nat, (True, TNil))\<rrangle> { (x, y) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] tuple patterns require case lowering; explicit \<open>match_switch\<close> remains
       first-order and rejects them with its stable positioned diagnostic. \<close>

urust_expr_rejects fidelity \<open> match_switch true { true \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] boolean patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity \<open> match_switch "ok" { "ok" \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] string patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { \<llangle>2 :: nat\<rrangle> \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] value-antiquotation patterns require equality-guard case lowering. \<close>

urust_expr_rejects fidelity \<open> (\<llangle>1 :: nat\<rrangle>,) \<close> \<open> syntax error found at ) \<close>
  \<comment> \<open> [FIDELITY] singleton tuples are outside the current frontend tuple grammar. \<close>

urust_expr_rejects fidelity
  \<open> let (x,) = \<llangle>(1 :: nat, TNil)\<rrangle>; x \<close>
  \<open> syntax error: deleting  ) = \<close>
  \<comment> \<open> [FIDELITY] a terminal comma does not turn a grouped singleton pattern into a tuple. \<close>

urust_expr_rejects fidelity
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>,,) \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] a trailing comma is one separator, not an empty tuple element. \<close>

urust_expr_rejects fidelity
  \<open> let (x, y,,) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x \<close>
  \<open> syntax error: deleting  , ) = \<close>
  \<comment> \<open> [FIDELITY] tuple-pattern lists likewise reject an empty element after the terminal comma. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x,,) \<Rightarrow> x, None \<Rightarrow> 0 } \<close>
  \<open> syntax error: deleting  , ) => \<close>
  \<comment> \<open> [FIDELITY] constructor argument lists reject doubled terminal commas. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> 0,, } \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] match-arm lists reject an empty arm after the terminal comma. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, y,,] \<Rightarrow> x, _ \<Rightarrow> 0 } \<close>
  \<open> syntax error: deleting  , ] => \<close>
  \<comment> \<open> [FIDELITY] slice-pattern lists reject doubled terminal commas. \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, negative_right: y,, } \<Rightarrow> x } \<close>
  \<open> syntax error: deleting  , } => \<close>
  \<comment> \<open> [FIDELITY] struct-field lists reject an empty field after the terminal comma. \<close>

urust_expr_rejects fidelity \<open> let () = (); () \<close> \<open> syntax error \<close>
  \<comment> \<open> [FIDELITY] unit is an expression but not a pattern in the current frontend. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] a numeral belongs to \<open>match_switch\<close>; source validation rejects it before
       generated case clauses are constructed. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>1 :: nat\<rrangle> { 1 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] literal \<open>1\<close> has the same dedicated case-pattern node and rejection boundary as
       literal \<open>0\<close>. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>2 :: nat\<rrangle> { 2 \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] the frontend's attempted guarded lowering retains the raw token and rejects with
       \<open>Undefined constant: "2"\<close>; the parser gives the same accept-set boundary a positioned diagnostic. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(2) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] constructor-nested numerals hit the same frontend raw-token rejection. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>2 :: nat\<rrangle> { 2 if True \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> guards are not supported in explicit `match_switch` \<close>
  \<comment> \<open> [FIDELITY] guards force bare \<open>match\<close> to case lowering, but the explicit switch form rejects
       them rather than changing lowering. \<close>

urust_expr_rejects fidelity \<open> match_case \<llangle>Some (0 :: nat)\<rrangle> { NoSuchCtor(x) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> `NoSuchCtor` is not a known constructor \<close>
  \<comment> \<open> [FIDELITY] \<open>Code.is_constr\<close> decides ctor-vs-binder; the frontend agrees ("Error in case
       expression: Not a datatype constructor"). \<close>

new_urust_rejects divergent \<open> match_switch \<llangle>0 :: nat\<rrangle> { x \<Rightarrow> () } \<close>
  \<open> unsupported match_switch key "x" \<close>
  \<comment> \<open> [DIVERGENT] the frontend accepts a binding key under \<open>match_switch\<close>; here switch keys are
       numeral / \<open>_\<close> only (binding patterns need \<open>match_case\<close>). \<close>

urust_expr_rejects fidelity
  \<open> match \<llangle>Some (0 :: nat)\<rrangle> { 0 \<Rightarrow> (), Some(x) \<Rightarrow> () } \<close>
  \<open> mixed numeral and constructor patterns in bare `match` \<close>
  \<comment> \<open> [FIDELITY] bare-match routing cannot select one lowering for numeral and constructor heads;
       the frontend reports the same mixed-match category. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>Some (2 :: nat)\<rrangle> { Some(1..2..3) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> range patterns are non-associative \<close>
  \<comment> \<open> [FIDELITY] range patterns are non-associative. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>[1 :: nat]\<rrangle> { [.., ..] \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> slice pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a slice has at most one rest marker. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, negative_left: y, .. } \<Rightarrow> x } \<close>
  \<open> has duplicate field "negative_left" \<close>
  \<comment> \<open> [FIDELITY] duplicate struct fields reject at the repeated field. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x } \<Rightarrow> x } \<close>
  \<open> is missing field(s): negative_right \<close>
  \<comment> \<open> [FIDELITY] omitted fields require a struct rest marker. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>NegativeMoreSelector 1 2\<rrangle> { NegativeMoreSelector { negative_more_required: x } \<Rightarrow> x } \<close>
  \<open> is missing field(s): more \<close>
  \<comment> \<open> [DIVERGENT] an ordinary datatype selector named \<open>more\<close> is required. The frontend
       mistakes its basename for HOL record-extension metadata and accepts the omission. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>\<lparr>negative_record_left = 1, negative_record_right = 2\<rparr>\<rrangle> { negative_record_fixture { negative_record_left: x, negative_record_right: _ } \<Rightarrow> x } \<close>
  \<open> HOL record pattern "negative_record_fixture" requires selector-based lowering \<close>
  \<comment> \<open> [FIDELITY] both frontends reject HOL record extension constructors. The custom parser
       exposes the explicit boundary for future selector-based lowering (T-29). \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { unknown: x, .. } \<Rightarrow> x } \<close>
  \<open> has unknown field "unknown" \<close>
  \<comment> \<open> [FIDELITY] selector metadata validates struct field names. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NoSuchStruct { field: x, .. } \<Rightarrow> x } \<close>
  \<open> no matching constructor or single-constructor record/datatype found \<close>
  \<comment> \<open> [FIDELITY] struct heads must resolve through constructor/type metadata. \<close>

urust_expr_rejects fidelity
  \<open> match_case \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { .., .. } \<Rightarrow> () } \<close>
  \<open> struct pattern has multiple `..` rest entries \<close>
  \<comment> \<open> [FIDELITY] a struct has at most one rest entry. \<close>

urust_expr_rejects fidelity
  \<open> let whole @ x = \<llangle>1 :: nat\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] aliases remain outside irrefutable let binders. \<close>

urust_expr_rejects fidelity
  \<open> const (1..=2) = \<llangle>1 :: nat\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] ranges remain outside irrefutable const binders. \<close>

urust_expr_rejects fidelity
  \<open> let [x, ..] = \<llangle>[1 :: nat]\<rrangle>; x \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] slices remain outside irrefutable let binders. \<close>

urust_expr_rejects fidelity
  \<open> const NegativeStruct { negative_left: x, .. } = \<llangle>NegativeStruct 1 2\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>
  \<comment> \<open> [FIDELITY] structs remain outside irrefutable const binders. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>Some (1 :: nat)\<rrangle> { whole @ Some(x) \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] aliases require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { 1..=2 \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] ranges require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>[1 :: nat]\<rrangle> { [x, ..] \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] slices require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>NegativeStruct 1 2\<rrangle> { NegativeStruct { negative_left: x, .. } \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>
  \<comment> \<open> [FIDELITY] struct patterns require case lowering. \<close>

urust_expr_rejects fidelity
  \<open> match_switch \<llangle>1 :: nat\<rrangle> { &1 \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] explicit switch conversion rejects reference syntax before key lowering. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>undefined\<rrangle> { AmbiguousStruct { ambiguous_field: x } \<Rightarrow> x } \<close>
  \<open> Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct \<close>
  \<comment> \<open> [DIVERGENT] the existing frontend silently picks one of two same-basename constructors.
       The new parser rejects and reports their qualified identities instead. \<close>

ML\<open>
local
  val left_struct =
    "Struct_Ambiguity_Left.struct_ambiguity_left.AmbiguousStruct"
  val right_struct =
    "Struct_Ambiguity_Right.struct_ambiguity_right.AmbiguousStruct"
  val left_nullary =
    "Struct_Ambiguity_Left.nullary_ambiguity_left.AmbiguousNullary"
  val right_nullary =
    "Struct_Ambiguity_Right.nullary_ambiguity_right.AmbiguousNullary"

  fun assert message condition =
    if condition then () else error message

  fun expect_ambiguity label source identities =
    (case Exn.result
        (fn () =>
          elab_urust \<^context>
            (Parser_Lex_Util.text_source source)) () of
       Exn.Res _ =>
         error (label ^ " unexpectedly resolved an ambiguous constructor")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn in
             assert (label ^ " did not report ambiguity")
               (String.isSubstring "is ambiguous; candidates:" message);
             List.app
               (fn identity =>
                 assert
                   (label ^ " omitted candidate " ^ quote identity)
                   (String.isSubstring identity message))
               identities
           end)

  val resolver =
    URust_Resolution.make_constructor_resolver
      \<^context> Position.none

  fun qualified identity =
    (case URust_Resolution.resolve_constructor resolver
        (identity, Position.none) of
       SOME info => info
     | NONE =>
         error
           ("qualified constructor did not resolve: " ^
             quote identity))

  val struct_info = qualified left_struct
  val nullary_info = qualified left_nullary

  val _ =
    assert "qualified positional constructor arity changed"
      (URust_Resolution.constructor_arity struct_info = 1)
  val _ =
    assert "qualified nullary constructor arity changed"
      (URust_Resolution.constructor_arity nullary_info = 0)
  val _ =
    (case URust_Resolution.constructor_family struct_info of
       SOME (family, members) =>
         (assert "qualified constructor family changed"
            (family =
              "Struct_Ambiguity_Left.struct_ambiguity_left");
          assert "qualified constructor family members changed"
            (map_filter
              (fn Const (name, _) => SOME name | _ => NONE)
              members = [left_struct]))
     | NONE =>
         error "qualified constructor lost family metadata")

  val _ =
    expect_ambiguity "positional constructor ambiguity"
      "match_case \<llangle>undefined\<rrangle> { AmbiguousStruct(x) \<Rightarrow> x }"
      [left_struct, right_struct]
  val _ =
    expect_ambiguity "nullary constructor ambiguity"
      "match_case \<llangle>undefined\<rrangle> { AmbiguousNullary \<Rightarrow> \<llangle>True\<rrangle> }"
      [left_nullary, right_nullary]
in
end
\<close>

subsection\<open> Cycle 1 source-diagnostic isolation (C1-I7/C1-I8) \<close>

text\<open>
Representative source failures must be raised before generated HOL reaches type checking. In
particular, diagnostics may not expose administrative names, generated case clauses, old internal
numeric-pattern wording, or synthetic positionless fallbacks.
\<close>

ML\<open>
local
  val forbidden =
    ["_urust_local_", "_urust_case_", "case_elem", "case_abs",
     "clauses are redundant", "numeric pattern in match_case", "Position.none"]

  fun expect_clean_rejection source required =
    (case Exn.result
        (fn () =>
          elab_urust \<^context>
            (Parser_Lex_Util.text_source source)) () of
       Exn.Res term =>
         error ("Cycle 1 diagnostic audit expected rejection, but got " ^
           Syntax.string_of_term \<^context> term)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let
             val message = Runtime.exn_message exn
             val _ =
               List.app
                 (fn expected =>
                   if String.isSubstring expected message then ()
                   else
                     error ("Cycle 1 diagnostic audit expected " ^
                       quote expected ^ ", but got " ^ quote message))
                 required
             val _ =
               List.app
                 (fn leaked =>
                   if String.isSubstring leaked message
                   then
                     error ("Cycle 1 diagnostic audit leaked " ^
                       quote leaked ^ " in " ^ quote message)
                   else ())
                 forbidden
           in () end)

  val _ =
    expect_clean_rejection
      "let (x, x) = \<llangle>(1 :: nat, (2 :: nat, TNil))\<rrangle>; x"
      ["duplicate pattern binder \"x\"", "The original binder is here"]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x }"
      ["or-pattern alternative is missing binder \"x\""]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(&x) \<Rightarrow> x, _ \<Rightarrow> 0 }"
      ["reference patterns are not implemented"]
  val _ =
    expect_clean_rejection
      "match_case \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> True, _ \<Rightarrow> False }"
      ["numeric patterns are not supported in case patterns"]
  val _ =
    expect_clean_rejection
      "for None in \<llangle>[None :: nat option]\<rrangle> { () }"
      ["unsupported or refutable pattern in a `for` binder position"]
in end
\<close>

section\<open> Calls \<close>

definition ncf1 :: \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> ncf1 \<equiv> lift_fun1 (\<lambda>x. x) \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>,,) \<close>
  \<open> syntax error found at , \<close>
  \<comment> \<open> [FIDELITY] call argument lists reject an empty argument after the terminal comma. \<close>

urust_expr_rejects fidelity \<open> zz(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] the arity cap is ONE policy number derived from the frontend's surface lowering (D29);
       the frontend rejects 15 args too ("Undefined constant: _urust_shallow_fun_with_args"). \<close>

urust_expr_rejects fidelity
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14) \<close>
  \<open> unsupported call arity 15 \<close>
  \<comment> \<open> [FIDELITY] 14 explicit method arguments plus the prepended receiver exceed
       the inclusive \<open>funcall14\<close> limit by one. \<close>

urust_expr_rejects fidelity
  \<open> 0.zz(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15) \<close>
  \<open> unsupported call arity 16 \<close>
  \<comment> \<open> [FIDELITY] the 15-explicit-argument boundary lowers to 16 total arguments. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)(\<llangle>2 :: 64 word\<rrangle>) \<close>
  \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] curried application \<open>f(a)(b)\<close>: rejected by both (a call result is not a callee). \<close>

urust_expr_rejects fidelity \<open> (ncf1)(\<llangle>1 :: 64 word\<rrangle>) \<close> \<open> syntax error found at ( \<close>
  \<comment> \<open> [FIDELITY] parenthesised callee \<open>(g)(x)\<close>: rejected by both (\<open>urust_callable\<close> has no paren form). \<close>

section\<open> Legacy macros \<close>

definition negative_macro_shout ::
  \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> negative_macro_shout \<equiv> lift_fun1 id \<close>

micro_rust_notation (call) negative_macro_shout ("negativeshout!")

consts
  negative_macro_raw_ref :: \<open>('a, 'b) Global_Store.gref\<close>
  negative_macro_read_only_ref :: \<open>('a, 'b, 'v) Global_Store.ro_ref\<close>

subsection\<open> Arity and raw-message policy \<close>

urust_expr_rejects fidelity \<open> assert!() \<close>
  \<open> macro "assert!" expects at least 1 argument(s), but got 0 \<close>

urust_expr_rejects fidelity \<open> assert_eq!(true) \<close>
  \<open> macro "assert_eq!" expects at least 2 argument(s), but got 1 \<close>

urust_expr_rejects fidelity \<open> assert_ne![true] \<close>
  \<open> macro "assert_ne!" expects at least 2 argument(s), but got 1 \<close>

urust_expr_rejects fidelity \<open> addr_of!() \<close>
  \<open> macro "addr_of!" expects exactly 1 argument(s), but got 0 \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(r, other) \<close>
  \<open> macro "addr_of_mut!" expects exactly 1 argument(s), but got 2 \<close>

urust_expr_rejects fidelity \<open> addr_of!(negative_macro_raw_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(negative_macro_raw_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of!(negative_macro_read_only_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> addr_of_mut!(negative_macro_read_only_ref) \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> panic!((message)) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> fatal!(if true { "left" } else { "right" }) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> unimplemented!(1_u32) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

urust_expr_rejects fidelity \<open> todo!(true) \<close>
  \<open> macro message must be an identifier, quoted string, or value antiquotation \<close>

subsection\<open> Names, registration precedence, and delimiters \<close>

urust_expr_rejects fidelity \<open> unknown_macro!(true) \<close>
  \<open> unknown macro "unknown_macro!" \<close>

urust_expr_rejects fidelity \<open> negativeshout ! (true) \<close>
  \<open> unknown macro "negativeshout!" \<close>

urust_expr_rejects fidelity \<open> negativeshout!() \<close>
  \<open> no backend matches the use-site type \<close>

urust_expr_rejects fidelity \<open> negativeshout!(1_u32) \<close>
  \<open> no backend matches the use-site type \<close>

urust_expr_rejects fidelity \<open> assert!(true,) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> vec![1_u32,] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity \<open> panic!("message",) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(true] \<close>
  \<open> syntax error found at ] \<close>

urust_expr_rejects fidelity \<open> vec![1_u32) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> assert!(true \<close>
  \<open> syntax error found at end of input \<close>

subsection\<open> Matches shape and case-compiler boundaries \<close>

urust_expr_rejects fidelity \<open> matches!() \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32)) \<close>
  \<open> syntax error found at ) \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_), ignored) \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches!(true, true && false) \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(,)) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> matches![Some(1_u32), Some(_)] \<close>
  \<open> syntax error: deleting \<close>

urust_expr_rejects fidelity \<open> matches !(Some(1_u32), Some(_)) \<close>
  \<open> unknown macro "matches!" \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_),) \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), _) \<close>
  \<open> clauses are redundant \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), binder) \<close>
  \<open> clauses are redundant \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(1..=3)) \<close>
  \<open> range patterns are not supported by legacy matches! \<close>

subsection\<open> Borrow and assignment-result boundaries \<close>

urust_expr_rejects fidelity \<open> &vec![r] \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> & mut vec![r] \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects fidelity \<open> vec![] = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> assert!(true) = rhs \<close>
  \<open> invalid assignment target \<close>

urust_expr_rejects fidelity \<open> matches!(Some(1_u32), Some(_)) = rhs \<close>
  \<open> invalid assignment target \<close>

section\<open> Assignment right-hand control-flow precedence \<close>

text\<open>
The frontend's priority-40 assignment accepts block expressions directly, but
priority-20/21 control-flow expressions require parentheses on the right-hand
side. Assignment remains right-associative by recursing through its own tier.
\<close>

urust_expr_rejects fidelity
  \<open> r = match flag { true \<Rightarrow> lhs, false \<Rightarrow> rhs } \<close>
  \<open> syntax error: deleting  match \<close>
  \<comment> \<open> [FIDELITY] bare match forms have the same assignment-RHS boundary as \<open>if\<close>. \<close>

urust_expr_rejects fidelity
  \<open> r = if flag { lhs } else { rhs } \<close>
  \<open> syntax error: deleting  if \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>if\<close> is too weak to be an assignment RHS; the grouped form is positive. \<close>

urust_expr_rejects fidelity
  \<open> r += match flag { true \<Rightarrow> lhs, false \<Rightarrow> rhs } \<close>
  \<open> syntax error: deleting  match \<close>
  \<comment> \<open> [FIDELITY] compound assignment has the same bare-match RHS boundary. \<close>

urust_expr_rejects fidelity
  \<open> r += if flag { lhs } else { rhs } \<close>
  \<open> syntax error: deleting  if \<close>
  \<comment> \<open> [FIDELITY] compound assignment recurses through \<open>uassign\<close>, not lower-priority control flow. \<close>

urust_expr_rejects fidelity \<open> r /= rhs \<close> \<open> = \<close>
  \<comment> \<open> [FIDELITY] the current frontend has no \<open>/=\<close> production; this remains a post-parity
       Rust-facing extension. \<close>

section\<open> Invalid assignment targets \<close>

text\<open>
Assignment parses below pure operators, then one \<open>expr_to_place\<close> conversion rejects
every non-place expression with the same positioned diagnostic.
\<close>

urust_expr_rejects fidelity \<open> 0 = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] numeric literals are values, not places. \<close>

urust_expr_rejects fidelity \<open> true = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] boolean literals are not places. \<close>

urust_expr_rejects fidelity \<open> \<llangle>r\<rrangle> = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] value antiquotations are values; only expression antiquotations can be places. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>) = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] call results are not assignment targets. \<close>

urust_expr_rejects fidelity \<open> receiver.ncf1() = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] method-call results are not assignment targets. \<close>

urust_expr_rejects fidelity \<open> opt? = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] propagation is value-only. \<close>

urust_expr_rejects fidelity \<open> &r = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] borrowing produces a value and cannot head a place. \<close>

urust_expr_rejects fidelity \<open> !r = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] unary negation is not a place. \<close>

urust_expr_rejects fidelity \<open> r + other = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] assignment is below pure operators, so the full binary expression is rejected. \<close>

urust_expr_rejects fidelity \<open> (r, other) = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] tuple values are not destructuring assignment targets. \<close>

urust_expr_rejects fidelity \<open> { r } = rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] blocks remain value expressions, not places. \<close>

urust_expr_rejects fidelity
  \<open> (if true { r } else { other }) = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] grouping admits the control-flow expression to operand position but does not
       make it a place. \<close>

urust_expr_rejects fidelity \<open> (r = rhs) = other \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] an assignment result cannot itself be assigned through. \<close>

urust_expr_rejects fidelity \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>).field = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] field-place validation recursively rejects an invalid call-result base. \<close>

urust_expr_rejects fidelity \<open> 0 += rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] compound assignment uses the same literal-target rejection path. \<close>

urust_expr_rejects fidelity \<open> r + other *= rhs \<close> \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] pure operators bind above every assignment operator, so the complete binary LHS
       reaches the shared place validator. \<close>

urust_expr_rejects fidelity
  \<open> ncf1(\<llangle>1 :: 64 word\<rrangle>)[0] = rhs \<close>
  \<open> invalid assignment target \<close>
  \<comment> \<open> [FIDELITY] indexed places recursively require a valid place base. \<close>

section\<open> Bounded ranges, arrays, and indexing \<close>

urust_expr_rejects fidelity \<open> 1..2..3 \<close>
  \<open> syntax error found at .. \<close>
  \<comment> \<open> [FIDELITY] expression ranges are non-associative. \<close>

urust_expr_rejects fidelity \<open> 1.. \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] open-ended ranges are outside the frontend syntax and parser scope. \<close>

urust_expr_rejects fidelity \<open> ..2 \<close>
  \<open> syntax error found at .. \<close>
  \<comment> \<open> [FIDELITY] a bounded range requires its lower endpoint. \<close>

urust_expr_rejects fidelity \<open> [1,,2] \<close>
  \<open> syntax error: deleting  , <integer> ] \<close>
  \<comment> \<open> [FIDELITY] array literals reject empty elements. \<close>

urust_expr_rejects fidelity \<open> [1 2] \<close>
  \<open> syntax error found at <integer> \<close>
  \<comment> \<open> [FIDELITY] array elements require commas. \<close>

urust_expr_rejects fidelity \<open> [1, 2 \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] array literals require a closing bracket. \<close>

urust_expr_rejects fidelity \<open> xs[] \<close>
  \<open> syntax error found at ] \<close>
  \<comment> \<open> [FIDELITY] indexing requires a subscript expression. \<close>

urust_expr_rejects fidelity \<open> xs[0 \<close>
  \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] indexing requires a closing bracket. \<close>

urust_expr_rejects fidelity \<open> xs[0, 1] \<close>
  \<open> syntax error: deleting  , <integer> ] \<close>
  \<comment> \<open> [FIDELITY] one indexing postfix contains exactly one expression. \<close>

section\<open> Fueled loops \<close>

urust_expr_rejects fidelity
  \<open> for Some(value) in \<llangle>[Some (1 :: nat)]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] \<open>for\<close> uses the frontend's irrefutable binder shape. \<close>

urust_expr_rejects fidelity
  \<open> for true in \<llangle>[True]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] literal loop binders are rejected at the pattern site. \<close>

urust_expr_rejects fidelity
  \<open> for whole @ value in \<llangle>[1 :: nat]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [FIDELITY] aliases remain unsupported in \<open>for\<close> binders. \<close>

urust_expr_rejects fidelity
  \<open> for &value in \<llangle>[1 :: nat]\<rrangle> { () } \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [FIDELITY] reference-pattern syntax has no current loop-binding semantics. \<close>

new_urust_rejects divergent
  \<open> for None in \<llangle>[None :: nat option]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>
  \<comment> \<open> [DIVERGENT] a known nullary constructor is resolved before binder classification. \<close>

new_urust_rejects divergent
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x } \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [DIVERGENT] all alternatives of one source arm must bind the same names and modes. \<close>

new_urust_rejects divergent
  \<open> match \<llangle>[1 :: nat, 2]\<rrangle> { [x, ..] | [] if True \<Rightarrow> True, _ \<Rightarrow> False } \<close>
  \<open> or-pattern alternative is missing binder "x" \<close>
  \<comment> \<open> [DIVERGENT] nested slice alternatives obey the same exact binder-set rule. \<close>

new_urust_rejects divergent
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let &Some(value) =
      \<llangle>Some (1 :: nat)\<rrangle> { () }
  \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] nested while-let reference patterns are rejected before case lowering. \<close>

new_urust_rejects divergent
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(&value) =
      \<llangle>Some (1 :: nat)\<rrangle> { () }
  \<close>
  \<open> reference patterns are not implemented \<close>
  \<comment> \<open> [DIVERGENT] recursive while-let traversal rejects a borrow below a constructor. \<close>

urust_expr_rejects fidelity \<open> while (true) { () } \<close>
  \<open> while \<close>
  \<comment> \<open> [FIDELITY] \<open>while\<close> requires the existing frontend's fuel annotation. \<close>

urust_expr_rejects fidelity \<open> while let Some(value) = Some(1) { () } \<close>
  \<open> while \<close>
  \<comment> \<open> [FIDELITY] \<open>while let\<close> also requires a fuel annotation. \<close>

urust_expr_rejects fidelity \<open> loop { () } \<close>
  \<open> loop \<close>
  \<comment> \<open> [FIDELITY] unconditional \<open>loop\<close> also requires fuel. \<close>

urust_expr_rejects fidelity \<open> #[fuel(1)] loop { () } \<close>
  \<open> <integer> \<close>
  \<comment> \<open> [FIDELITY] fuel must use an expression antiquotation, not a numeral. \<close>

urust_expr_rejects fidelity \<open> #[fuel(\<llangle>1 :: nat\<rrangle>)] loop { () } \<close>
  \<open> <value antiquotation> \<close>
  \<comment> \<open> [FIDELITY] a value antiquotation is not a fuel payload. \<close>

new_urust_rejects divergent
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while true { () } \<close>
  \<open> true \<close>
  \<comment> \<open> [DIVERGENT] the dedicated parser requires Rust's condition parentheses; Isabelle's
       mixfix parser accepts this spelling despite displaying parentheses on pretty-print. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a fueled loop needs parentheses in binary operand position. \<close>

urust_expr_rejects fidelity
  \<open> for value in \<llangle>[1 :: nat]\<rrangle> { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>for\<close> loop is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) =
    \<llangle>Some (1 :: nat)\<rrangle> { () } == () \<close>
  \<open> syntax error found at == \<close>
  \<comment> \<open> [FIDELITY] a bare \<open>while let\<close> loop is not a binary operand. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value)
    \<llangle>Some (1 :: nat)\<rrangle> { () } \<close>
  \<open> <value antiquotation> \<close>
  \<comment> \<open> [FIDELITY] the pattern and scrutinee require an equals delimiter. \<close>

urust_expr_rejects fidelity
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 0 =
    \<llangle>0 :: nat\<rrangle> { () } \<close>
  \<open> numeric patterns are not supported in case patterns \<close>
  \<comment> \<open> [FIDELITY] case numerals retain the existing frontend rejection. \<close>

urust_expr_rejects fidelity
  \<open> for value in \<llangle>[1 :: nat]\<rrangle> { () } 1 2 \<close>
  \<open> syntax error found at <integer> \<close>
  \<comment> \<open> [FIDELITY] semicolon-free sequencing does not admit value juxtaposition. \<close>

section\<open> Lexer and whole-input failures \<close>

urust_expr_rejects fidelity \<open> "bad\q" \<close> \<open> bad escape character in string \<close>
  \<comment> \<open> [FIDELITY] malformed escapes are rejected by the same Isabelle string decoder. \<close>

urust_expr_rejects fidelity \<open> "unterminated \<close> \<open> malformed or unterminated string literal \<close>
  \<comment> \<open> [FIDELITY] the opening quote receives a positioned lexer diagnostic. \<close>

urust_expr_rejects fidelity \<open> \<llangle>1 :: nat \<close> \<open> unterminated value antiquotation \<close>
  \<comment> \<open> [FIDELITY] EOF in a value antiquotation is diagnosed at its opening delimiter. \<close>

ML\<open>
local
  fun expect_rejection text expected =
    (case Exn.result
        (fn () =>
          elab_urust \<^context>
            (Parser_Lex_Util.text_source text)) () of
       Exn.Res _ => error ("expected direct parser rejection containing " ^ quote expected)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn
           in
             if String.isSubstring expected message then ()
             else error ("expected direct parser rejection containing " ^ quote expected ^
               ", but got " ^ quote message)
           end)
  val _ =
    expect_rejection ("\<epsilon>" ^ Symbol.open_ ^ "True")
      "unterminated expression antiquotation"
  val _ =
    ignore
      (elab_urust \<^context>
        (Parser_Lex_Util.text_source "()"))
in end
\<close>

urust_expr_rejects fidelity
  \<open> match_case true { \<epsilon>\<open>Bool_Type.true\<close> \<Rightarrow> () } \<close>
  \<open> <expression antiquotation> => \<close>
  \<comment> \<open> [FIDELITY] expression antiquotation remains expression-only. \<close>

urust_expr_rejects fidelity \<open> 1 @ 2 \<close> \<open> syntax error found at @ \<close>
  \<comment> \<open> [FIDELITY] \<open>@\<close> is pattern-only; expression position rejects it after lexing. \<close>

urust_expr_rejects fidelity
  \<open> match true { true => => () } \<close>
  \<open> syntax error: deleting  => ( ) \<close>
  \<comment> \<open> [FIDELITY] generated ML-Yacc arrow names are rendered as their source spelling. \<close>

urust_expr_rejects fidelity \<open> { () \<close> \<open> syntax error found at end of input \<close>
  \<comment> \<open> [FIDELITY] unbalanced brace -- input must be consumed to EOF by a complete derivation. \<close>

urust_expr_rejects fidelity \<open> { ; } \<close> \<open> syntax error found at ; \<close>
  \<comment> \<open> [FIDELITY] a block cannot begin with a standalone semicolon. \<close>

urust_expr_rejects fidelity \<open> \<close> \<open> empty expression \<close>
  \<comment> \<open> [FIDELITY] \<open>parse_source\<close> returns NONE on blank input; the frontend's empty bracket is an
       inner-syntax error. \<close>

end
