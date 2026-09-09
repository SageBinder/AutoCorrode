theory Parser_Test_Term_Hook
  imports Parser_Test_Utils
begin

section\<open> Experimental term-position parser hook \<close>

text\<open>
This theory demonstrates a term-level entry point for the dedicated parser without changing the
production parser facade. The tagged cartouche \<open>\<mu>\<open> SOURCE \<close>\<close> is parsed and lowered to an
unchecked HOL term during parse translation. The enclosing Isabelle term then performs the sole
type check, so its expected type and surrounding binders remain available.

The parser and resolver produce the post-parse internal type constraints expected by
\<open>Syntax.check_term\<close>. A parse translation is itself still upstream of Isabelle's term decoder,
so the local boundary adapter below re-embeds those constraints as ordinary pre-decode
\<open>_constrain\<close> syntax while preserving their types and source positions.
\<close>

ML\<open>
local
  fun source_of_cartouche args =
    let
      fun bad () = raise TERM ("urust_term_source", args)
    in
      (case args of
         [(Const (\<^syntax_const>\<open>_constrain\<close>, _) $ Free (raw, _) $ encoded_pos)] =>
           (case Term_Position.decode_position1 encoded_pos of
              SOME {pos, ...} =>
                let
                  val all_symbols = Symbol_Pos.explode (raw, pos)
                  val cartouche_pos =
                    Position.range_position
                      (Position.range
                        (pos, Position.symbol_explode raw pos))
                  val symbols =
                    all_symbols
                    |> Symbol_Pos.cartouche_content
                  val content_pos = Position.symbol Symbol.open_ pos
                  val range =
                    if null symbols
                    then Position.range (content_pos, content_pos)
                    else Symbol_Pos.range symbols
                  val (text, _) = Symbol_Pos.implode_range range symbols
                in (Input.source true text range, cartouche_pos) end
            | NONE => bad ())
       | _ => bad ())
    end

  fun reembed_constraints ctxt
      (Const (\<^syntax_const>\<open>_type_constraint_\<close>,
          Type (\<^type_name>\<open>fun\<close>, [T, _])) $ term) =
        Syntax.const \<^syntax_const>\<open>_constrain\<close> $
          reembed_constraints ctxt term $
          Syntax_Phases.term_of_typ ctxt T
    | reembed_constraints ctxt (term $ argument) =
        reembed_constraints ctxt term $
          reembed_constraints ctxt argument
    | reembed_constraints ctxt (Abs (name, T, body)) =
        Abs (name, T, reembed_constraints ctxt body)
    | reembed_constraints ctxt (constant as Const (name, T)) =
        if Lexicon.is_const name orelse Proof_Context.is_syntax_const ctxt name
        then constant
        else Const (Lexicon.mark_const name, T)
    | reembed_constraints _ atom = atom

  fun urust_term_tr ctxt args =
    let
      val (source, cartouche_pos) = source_of_cartouche args
      (* Inner syntax reports the complete token as an orange inner cartouche before invoking this
         translation. Restore the ordinary command-cartouche baseline first, then let the dedicated
         parser's lexical and semantic reports override it token by token. *)
      val _ =
        Context_Position.report ctxt cartouche_pos Markup.cartouche
      val ast =
        (case URust_Diagnostics.parse_source ctxt source of
           SOME expression => expression
         | NONE =>
             error
               ("urust term: empty expression" ^
                 Position.here (Input.pos_of source)))
    in
      URust_Translate.mk_expression ctxt [] ast
      |> reembed_constraints ctxt
    end
in
  val urust_term_translation = urust_term_tr
end
\<close>

syntax
  "_urust_term_hook" :: "cartouche_position \<Rightarrow> logic" ("\<mu>_")

parse_translation \<open>
  [(\<^syntax_const>\<open>_urust_term_hook\<close>, urust_term_translation)]
\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("term-hook markup normalization: " ^ message)

    val source_text = "\<mu>\<open> let _ = 1; True \<close>"
    val source_start =
      Position.make0 7 100 0 "" "urust-term-hook-markup"
        "urust-term-hook-markup"
    val source =
      Input.source false source_text
        (Position.range
          (source_start,
           Position.symbol_explode source_text source_start))
    val captured =
      Synchronized.var "urust_term_hook_markup" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Syntax.parse_term \<^context>
                    (Syntax.implode_input source))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup

    fun has_entity kind position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties position)
        markup

    fun find_from needle offset =
      if offset + size needle > size source_text then
        error ("term-hook markup normalization: missing " ^ quote needle)
      else if String.substring (source_text, offset, size needle) = needle
      then offset
      else find_from needle (offset + 1)

    fun token_position needle offset =
      let
        val raw = find_from needle offset
        val start =
          Position.symbol_explode
            (String.substring (source_text, 0, raw)) source_start
      in
        (raw,
         Position.range_position
           (Position.range
             (start, Position.symbol_explode needle start)))
      end

    val cartouche_start =
      Position.symbol_explode "\<mu>" source_start
    val cartouche_pos =
      Position.range_position
        (Position.range
          (cartouche_start,
           Position.symbol_explode
             "\<open> let _ = 1; True \<close>" cartouche_start))
    val (_, underscore_pos) =
      token_position "_" 0
    val (numeral_offset, numeral_pos) =
      token_position "1" 0
    val (_, constant_pos) =
      token_position "True" (numeral_offset + 1)

    val _ =
      assert "inner-syntax cartouche classification disappeared"
        (has_markup Markup.inner_cartoucheN cartouche_pos)
    val _ =
      assert "ordinary cartouche normalization is absent or has the wrong range"
        (has_markup Markup.cartoucheN cartouche_pos)
    val _ =
      assert "numeral markup was lost"
        (has_markup Markup.numeralN numeral_pos)
    val _ =
      assert "wildcard typing markup was lost"
        (has_markup Markup.typingN underscore_pos)
    val _ =
      assert "constant entity markup was lost"
        (has_entity Markup.constantN constant_pos)
  in
    val _ = ()
  end
\<close>

lemma closed_conformance:
  "\<mu>\<open> 1 + 2 \<close> = \<lbrakk> 1 + 2 \<rbrakk>"
  by (rule refl)

lemma expected_result_type:
  "(\<mu>\<open> 0 \<close> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression) =
   (\<lbrakk> 0 \<rbrakk> ::
      ('s, nat, 'r, 'abort, 'input, 'output) expression)"
  by (rule refl)

lemma outer_lambda_plain_identifier:
  "(\<lambda>x :: nat. \<mu>\<open> x \<close>) =
   (\<lambda>x :: nat. \<lbrakk> x \<rbrakk>)"
  by (rule refl)

lemma outer_lambda_antiquotation:
  "(\<lambda>x :: nat. \<mu>\<open> \<llangle>x\<rrangle> \<close>) =
   (\<lambda>x :: nat. \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>)"
  by (rule refl)

lemma outer_let_antiquotation:
  "(\<lambda>x :: nat. let y = x in \<mu>\<open> \<llangle>y\<rrangle> \<close>) =
   (\<lambda>x :: nat. let y = x in \<lbrakk> \<llangle>y\<rrangle> \<rbrakk>)"
  by (rule refl)

lemma outer_case_antiquotation:
  "(\<lambda>x :: nat option.
      case x of
        Some y \<Rightarrow> \<mu>\<open> \<llangle>y\<rrangle> \<close>
      | None \<Rightarrow> \<mu>\<open> 0 \<close>) =
   (\<lambda>x :: nat option.
      case x of
        Some y \<Rightarrow> \<lbrakk> \<llangle>y\<rrangle> \<rbrakk>
      | None \<Rightarrow> \<lbrakk> 0 \<rbrakk>)"
  by (rule refl)

lemma parser_local_binder:
  "\<mu>\<open> let x = 1; \<llangle>x\<rrangle> \<close> =
   \<lbrakk> let x = 1; \<llangle>x\<rrangle> \<rbrakk>"
  by (rule refl)

context
begin

private definition private_term_hook_value :: nat where
  \<open>private_term_hook_value = 7\<close>

lemma private_constant_not_captured:
  "(\<lambda>private_term_hook_value :: nat.
      \<mu>\<open> \<llangle>CONST private_term_hook_value\<rrangle> \<close>) =
   (\<lambda>private_term_hook_value :: nat.
      \<lbrakk> \<llangle>CONST private_term_hook_value\<rrangle> \<rbrakk>)"
  by (rule refl)

end

context
  fixes x :: nat
begin

lemma fixed_context_antiquotation:
  "\<mu>\<open> \<llangle>x\<rrangle> \<close> = \<lbrakk> \<llangle>x\<rrangle> \<rbrakk>"
  by (rule refl)

end

lemma nested_term_hook:
  "\<mu>\<open> \<epsilon>\<open> \<mu>\<open> 1 \<close> \<close> \<close> =
   \<lbrakk> \<epsilon>\<open> \<lbrakk> 1 \<rbrakk> \<close> \<rbrakk>"
  by (rule refl)

end
