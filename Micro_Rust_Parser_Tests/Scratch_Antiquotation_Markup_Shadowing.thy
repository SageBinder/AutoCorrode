theory Scratch_Antiquotation_Markup_Shadowing
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

section\<open> Scratch witness for HOL-internal antiquotation shadowing markup \<close>

text\<open>
This theory demonstrates the editor-only limitation of
\<^ML>\<open>Parser_Utils.mark_bound\<close>. The outer micro-Rust \<open>let x\<close> is in scope at
the value antiquotation, but both occurrences of \<open>x\<close> inside
\<^verbatim>\<open>\<lambda>x :: nat. x\<close> belong to the inner HOL lambda.

Term semantics are correct: HOL parsing produces an abstraction whose body contains
\<^ML>\<open>Bound 0\<close>. The lexical markup overlay does not parse HOL binding structure,
however, so it reports both the HOL binder declaration and its bound use as references
to the outer micro-Rust \<open>x\<close>. In jEdit, ctrl-clicking either inner \<open>x\<close> therefore
navigates to the micro-Rust \<open>let x\<close>.

This file is intentionally a scratch theory and is not listed in
\<^file>\<open>ROOT\<close>. The ML witness below succeeds while the bug is present; a future
semantic-markup fix should make its final two reference assertions fail.
\<close>

urust_expr scratch_hol_lambda_shadowing
  \<open>
    let x = \<llangle>1 :: nat\<rrangle>;
    \<llangle>(\<lambda>x :: nat. x) 2\<rrangle>
  \<close>

lemma scratch_hol_lambda_shadowing_semantics:
  \<open>
    scratch_hol_lambda_shadowing =
      \<lbrakk>
        let x = \<llangle>1 :: nat\<rrangle>;
        \<llangle>(\<lambda>x :: nat. x) 2\<rrangle>
      \<rbrakk>
  \<close>
  unfolding scratch_hol_lambda_shadowing_def
  by (rule refl)

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("antiquotation markup shadowing scratch: " ^ message)

    val ctxt = \<^context>
    val file = "urust-antiquotation-markup-shadowing"
    val document_id = "urust-antiquotation-markup-shadowing"
    val body_text =
      "let x = \<llangle>1 :: nat\<rrangle>; " ^
      "\<llangle>(\<lambda>x :: nat. x) 2\<rrangle>"
    val body_start =
      Position.make0 7 100 0 "" file document_id
    val body_source =
      Parser_Lex_Util.positioned_content_source body_text body_start
    val expected =
      Syntax.parse_term ctxt
        ("\<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; " ^
         "\<llangle>(\<lambda>x :: nat. x) 2\<rrangle> \<rbrakk>")
      |> Syntax.check_term ctxt

    val captured =
      Synchronized.var "urust_antiquotation_markup_shadowing"
        ([]: string list)
    val report_lock =
      Synchronized.var "urust_antiquotation_markup_shadowing_lock" ()
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)
    fun with_report_lock action =
      Synchronized.change_result report_lock
        (fn () => (action (), ()))

    val actual =
      with_report_lock (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                URust_Command.elaborate ctxt
                  {kind = URust_Command.Expression,
                   source = body_source,
                   arguments = [],
                   arguments_pos = #2 (Input.range_of body_source),
                   declared_type = NONE}) ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)
    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value captured)) []

    fun find_from needle offset =
      if offset + size needle > size body_text then
        error
          ("antiquotation markup shadowing scratch: missing " ^
            quote needle)
      else if String.substring (body_text, offset, size needle) = needle
      then offset
      else find_from needle (offset + 1)

    fun token_position needle offset =
      let
        val raw = find_from needle offset
        val start =
          Position.symbol_explode
            (String.substring (body_text, 0, raw)) body_start
      in
        (raw,
         Position.range_position
           (Position.range
             (start, Position.symbol_explode needle start)))
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               ("antiquotation markup shadowing scratch: expected one " ^
                 quote property ^ " entity at" ^
                 Position.here position ^ ", found [" ^
                 commas_quote ids ^ "]"))
      end

    val (outer_offset, outer_definition) =
      token_position "x" 0
    val (hol_binder_offset, hol_binder) =
      token_position "x" (outer_offset + 1)
    val (_, hol_bound_use) =
      token_position "x" (hol_binder_offset + 1)

    val outer_id = entity_id Markup.defN outer_definition
    val hol_binder_overlay = entity_id Markup.refN hol_binder
    val hol_use_overlay = entity_id Markup.refN hol_bound_use

    val _ =
      assert "checked term differs from the legacy frontend"
        (Term.aconv (actual, expected))
    val _ =
      assert
        "HOL lambda binder is no longer incorrectly linked to the micro-Rust binder"
        (hol_binder_overlay = outer_id)
    val _ =
      assert
        "HOL bound use is no longer incorrectly linked to the micro-Rust binder"
        (hol_use_overlay = outer_id)

    val _ =
      writeln
        ("Confirmed editor-only bug: the checked term is alpha-identical to " ^
         "the legacy frontend, but both HOL-lambda x tokens carry urust_var " ^
         "references to the outer micro-Rust let binder.")
  in
    val _ = ()
  end
\<close>

end
