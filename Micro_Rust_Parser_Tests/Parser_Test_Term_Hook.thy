theory Parser_Test_Term_Hook
  imports
    Parser_Test_Utils
    Micro_Rust_Parser_Impl.Parser_Term_Hook
begin

section\<open> Experimental term-position parser hook \<close>

text\<open>
The reusable hook is defined by \<open>Micro_Rust_Parser_Impl.Parser_Term_Hook\<close>. This theory covers its
markup, contextual elaboration, binder hygiene, nesting, scoped conformance configuration, positioned
failures, marker erasure, and detached legacy reporting.
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
    fun capture enabled =
      let
        val captured =
          Synchronized.var
            ("urust_term_hook_markup_" ^
              Bool.toString enabled)
            ([]: string list)
        fun capture_reports chunks =
          Synchronized.change captured (append chunks)
        val ctxt =
          Config.put urust_term_hook_conformance_check
            enabled \<^context>
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn
              capture_reports
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    ignore
                      (Syntax.parse_term ctxt
                        (Syntax.implode_input source))) ())
              ())
      in Synchronized.value captured end

    val disabled_reports = capture false
    val enabled_reports = capture true

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val disabled_markup =
      fold collect_markup
        (maps YXML.parse_body disabled_reports) []
    val enabled_markup =
      fold collect_markup
        (maps YXML.parse_body enabled_reports) []
    val markup = disabled_markup

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

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

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
    val _ =
      assert "detached legacy parsing duplicated numeral reports"
        (count_markup Markup.numeralN numeral_pos enabled_markup =
          count_markup Markup.numeralN numeral_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated wildcard typing reports"
        (count_markup Markup.typingN underscore_pos enabled_markup =
          count_markup Markup.typingN underscore_pos disabled_markup)
    val _ =
      assert "detached legacy parsing duplicated constant reports"
        (count_entity Markup.constantN constant_pos enabled_markup =
          count_entity Markup.constantN constant_pos disabled_markup)
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

lemma nested_hol_shadowing_antiquotation:
  "(\<lambda>x :: nat.
      \<mu>\<open>
        let x = \<llangle>x\<rrangle>;
        \<llangle>(\<lambda>x :: nat. x) x\<rrangle>
      \<close>) =
   (\<lambda>x :: nat.
      \<lbrakk>
        let x = \<llangle>x\<rrangle>;
        \<llangle>(\<lambda>x :: nat. x) x\<rrangle>
      \<rbrakk>)"
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


section\<open> Scoped delayed conformance \<close>

lemma disabled_accepts_parser_only_source:
  "\<mu>\<open>
      // accepted only by the dedicated parser
      ()
    \<close> =
   \<lbrakk> () \<rbrakk>"
  by (rule refl)

declare [[urust_term_hook_conformance_check = true]]

term
  "(\<mu>\<open> 0 \<close> ::
    ('s, nat, 'r, 'abort, 'input, 'output) expression)"

declare [[urust_term_hook_conformance_check = false]]

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("term-hook delayed conformance: " ^ message)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int
          (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int
          (Position.end_offset_of position)

    fun has_diagnostic_position body position =
      fold collect_markup body []
      |> exists
          (fn (name, properties) =>
            name = Markup.positionN andalso
              has_position properties position)

    fun positioned_source text start =
      Input.source false text
        (Position.range
          (start, Position.symbol_explode text start))

    fun cartouche_position text start =
      let
        val cartouche_text =
          String.extract (text, size "\<mu>", NONE)
        val cartouche_start =
          Position.symbol_explode "\<mu>" start
      in
        Position.range_position
          (Position.range
            (cartouche_start,
             Position.symbol_explode
               cartouche_text cartouche_start))
      end

    fun expect_positioned_failure
        label expected position action =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("term-hook delayed conformance: " ^ label ^
              " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body =
                 YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               assert (label ^ " diagnostic changed")
                 (String.isSubstring expected message);
               assert (label ^ " diagnostic range changed")
                 (has_diagnostic_position body position)
             end)

    fun expect_failure label expected action =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("term-hook delayed conformance: " ^ label ^
              " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             assert (label ^ " diagnostic changed")
               (String.isSubstring expected
                 (XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn)))))

    val disabled_ctxt =
      Config.put urust_term_hook_conformance_check
        false \<^context>
    val enabled_ctxt =
      Config.put urust_term_hook_conformance_check
        true \<^context>

    val shared_text = "\<mu>\<open> 1 \<close>"
    val shared_start =
      Position.make0 11 500 0 "" ""
        "term-hook-shared-source"
    val shared_source =
      positioned_source shared_text shared_start
    val shared_input = Syntax.implode_input shared_source
    val shared_position =
      cartouche_position shared_text shared_start
    val unchecked_marker =
      Syntax.parse_term enabled_ctxt shared_input
    val checked_enabled =
      Syntax.check_term enabled_ctxt unchecked_marker
    val checked_disabled =
      Syntax.read_term disabled_ctxt shared_input
    val _ =
      assert "enabled checking changed the parser term"
        (Term.aconv (checked_enabled, checked_disabled))

    val (marker_head, marker_arguments) =
      Term.strip_comb unchecked_marker
    val marker_name =
      (case marker_head of
         Const (name, _) => name
       | _ =>
           error
             "term-hook delayed conformance: missing marker head")
    val position_payload =
      (case marker_arguments of
         [_, _, payload] => payload
       | _ =>
           error
             "term-hook delayed conformance: malformed generated marker")

    fun contains_marker
        (Const (name, _)) = name = marker_name
      | contains_marker (function $ argument) =
          contains_marker function orelse
            contains_marker argument
      | contains_marker (Abs (_, _, body)) =
          contains_marker body
      | contains_marker _ = false

    val _ =
      assert "a conformance marker survived checking"
        (not (contains_marker checked_enabled))

    val structural_mismatch =
      Term.list_comb
        (marker_head,
         [\<^term>\<open>True\<close>,
          \<^term>\<open>False\<close>,
          position_payload])
    val _ =
      expect_positioned_failure "structural mismatch"
        "different untyped terms" shared_position
        (fn () =>
          Syntax.check_term enabled_ctxt
            structural_mismatch)

    val type_mismatch =
      Term.list_comb
        (marker_head,
         [HOLogic.mk_eq
            (Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>nat\<close>, \<^term>\<open>True\<close>)),
          HOLogic.mk_eq
            (Abs ("x", \<^typ>\<open>bool\<close>, \<^term>\<open>True\<close>),
             Abs ("x", \<^typ>\<open>bool\<close>, \<^term>\<open>True\<close>)),
          position_payload])
    val _ =
      expect_positioned_failure "type mismatch"
        "types do not agree" shared_position
        (fn () =>
          Syntax.check_term enabled_ctxt type_mismatch)

    val malformed_marker =
      marker_head $ \<^term>\<open>True\<close>
    val _ =
      expect_failure "malformed marker"
        "malformed internal marker"
        (fn () =>
          Syntax.check_term enabled_ctxt
            malformed_marker)

    val rejected_text =
      "\<mu>\<open> () // legacy rejects this source \<close>"
    val rejected_start =
      Position.make0 13 700 0 "" ""
        "term-hook-legacy-rejection"
    val rejected_source =
      positioned_source rejected_text rejected_start
    val rejected_position =
      cartouche_position rejected_text rejected_start
    val _ =
      expect_positioned_failure "legacy rejection"
        "legacy frontend rejected the source"
        rejected_position
        (fn () =>
          Syntax.read_term enabled_ctxt
            (Syntax.implode_input rejected_source))
  in
    val _ = ()
  end
\<close>

end
