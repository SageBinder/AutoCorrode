(* ML audits for Rust datatypes and types, followed by the generic datatype and type mapping
   suites, whose examples interleave with audits of the state before later declarations. The
   readable examples are in Parser_Datatype_Examples. *)

theory Parser_Datatype_ML_Tests
  imports
    Parser_Datatype_Examples
begin

chapter\<open> Simple word enum clauses \<close>

section\<open> Clause registrations without the chunk command \<close>

declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 0, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

ML_val\<open>
  local
    val keywords = Thy_Header.get_keywords' \<^context>
    fun backend name =
      (case Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NLiteral ("ClauseKind::" ^ name) of
         [{hol_term, ...}] => hol_term
       | entries =>
           error ("clause registration audit: " ^ name ^ " has " ^
             string_of_int (length entries) ^ " backends"))
  in
    val _ =
      if Keyword.is_command keywords "urust"
      then error "clause registration audit: urust is a command keyword without the chunk theory"
      else ()
    val _ = @{assert} (backend "CLK_First" aconv @{term CLK_First})
    val _ = @{assert} (backend "CLK_Second" aconv @{term CLK_Second})
  end
\<close>

chapter\<open> Rust datatypes \<close>

section\<open> Rust datatype declarations \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]

ML_val \<open>
  val SOME packet = URust_Item_Scope.lookup_constructor \<^context> "RenamedPacket"
  val _ =
    if map (apsnd dest_Const_name) (URust_Item_Scope.constructor_fields packet) =
      [("renameSampleValue", \<^const_name>\<open>sample\<close>),
       ("valid", \<^const_name>\<open>renamed_packet_valid\<close>)]
    then () else error "renamed record lost selector identities or source field order"
  val [alias] = Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "renameSampleValue"
  val _ =
    if dest_Const_name (#hol_term alias) = \<^const_name>\<open>renamed_packet_sample_lens\<close>
    then () else error "renamed selector lost its original Rust alias"
  val SOME ready = URust_Item_Scope.lookup_constructor \<^context> "RenamedChoice::Ready"
  val _ =
    if dest_Const_name (URust_Item_Scope.constructor_term ready) =
      \<^const_name>\<open>ModelReady\<close> andalso
      map (apsnd dest_Const_name) (URust_Item_Scope.constructor_fields ready) =
        [("value", \<^const_name>\<open>renamed_choice_hol_ready_value\<close>),
         ("active", \<^const_name>\<open>renamed_choice_hol_ready_active\<close>)]
    then () else error "renamed constructor changed payload selectors or source metadata"
\<close>

context
begin

urust_datatype [renames = ["value" \<rightarrow> "context_sample"]] \<open>
  struct ContextRename { value: u32 }
\<close>
urust_datatype \<open> struct ContextDefault { value: bool } \<close>

ML_val \<open>
  val SOME entry = URust_Item_Scope.lookup_constructor \<^context> "ContextDefault"
  val _ =
    if map (apsnd dest_Const_name) (URust_Item_Scope.constructor_fields entry) =
      [("value", \<^const_name>\<open>context_default_value\<close>)]
    then () else error "a rename map escaped its declaration"
\<close>

end

ML_val \<open>
  val _ =
    List.app
      (fn field =>
        if null (Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField field)
        then () else error ("disabled declaration registered " ^ quote field))
      ["sampleValue", "HTTP2Code"]
  val SOME entry = URust_Item_Scope.lookup_constructor \<^context> "NotationPacket"
  val _ =
    if map fst (URust_Item_Scope.constructor_fields entry) = ["sampleValue", "HTTP2Code"]
    then () else error "disabled declaration lost source field metadata"
\<close>

thm notation_packet_notation_packet_sample_value_lens_valid
    notation_packet_notation_packet_sample_value_lens_view_update_modify
    notation_packet_notation_packet_sample_value_update_explicit
    notation_packet_notation_packet_http2_code_lens_valid

urust_notation (field) notation_packet_notation_packet_sample_value_lens ("sampleValue")

urust_expr notation_packet_manual_field \<open>
  (NotationPacket { sampleValue: 7u32, HTTP2Code: true }).sampleValue
\<close>

lemma notation_packet_manual_field_eq:
  \<open>notation_packet_manual_field =
    bind notation_packet_construction
      (\<lambda>packet. literal (lens_view notation_packet_notation_packet_sample_value_lens packet))\<close>
  unfolding notation_packet_manual_field_def notation_packet_construction_def
  by (simp add: bindlift1_def bind1_def lift_exp1_def deep_compose1_def)

context notes [[urust_register_notation = false]]
begin

urust_datatype \<open> struct NotationScopedOff { scopedAlias: u32 } \<close>
urust_datatype [register_notation] \<open> struct NotationScopedOn { scopedAlias: bool } \<close>
urust_datatype \<open> struct NotationStillOff { scopedAlias: u64 } \<close>

context notes [[urust_register_notation = true]]
begin

urust_datatype [register_notation = false] \<open> struct NotationNestedOff { scopedAlias: u16 } \<close>
urust_datatype \<open> struct NotationNestedOn { scopedAlias: u8 } \<close>

ML_val \<open>
  val backends =
    Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "scopedAlias"
    |> map (dest_Const_name o #hol_term)
  val _ =
    if sort_strings backends =
      sort_strings
        [\<^const_name>\<open>notation_scoped_on_notation_scoped_on_scoped_alias_lens\<close>,
         \<^const_name>\<open>notation_nested_on_notation_nested_on_scoped_alias_lens\<close>]
    then () else error "nested registration configuration or inline precedence changed"
\<close>

end

urust_datatype \<open> struct NotationRestoredOff { scopedAlias: i32 } \<close>

ML_val \<open>
  val backends =
    Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "scopedAlias"
    |> map (dest_Const_name o #hol_term)
  val _ =
    if sort_strings backends =
      sort_strings
        [\<^const_name>\<open>notation_scoped_on_notation_scoped_on_scoped_alias_lens\<close>,
         \<^const_name>\<open>notation_nested_on_notation_nested_on_scoped_alias_lens\<close>]
    then () else error "nested registration configuration or inline precedence changed"
\<close>

end

locale notation_disabled_locale
begin

declare [[urust_register_notation = false]]
urust_datatype \<open> struct NotationLocaleOff { localeAlias: u32 } \<close>
urust_datatype [register_notation = true] \<open> struct NotationLocaleOn { localeAlias: bool } \<close>
urust_datatype \<open> struct NotationLocaleStillOff { localeAlias: u64 } \<close>

ML_val \<open>
  val [entry] = Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "localeAlias"
  val _ =
    if dest_Const_name (#hol_term entry) =
      \<^const_name>\<open>notation_locale_on_notation_locale_on_locale_alias_lens\<close>
    then () else error "locale registration configuration changed"
\<close>

end

ML_val \<open>
  val [] = Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "localeAlias"
  val [entry] = Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NField "restoredAlias"
  val _ =
    if dest_Const_name (#hol_term entry) =
      \<^const_name>\<open>notation_restored_on_notation_restored_on_restored_alias_lens\<close>
    then () else error "registration configuration escaped its context"
\<close>

locale datatype_scope_left =
  fixes marker_left :: nat
begin

urust_datatype scoped_packet \<open>
  struct ScopedPacket {
    value: u32,
  }
\<close>

urust_expr scoped_packet_left_value \<open>
  ScopedPacket { value: 23u32 }
\<close>

ML_val \<open>
  val SOME scoped_type =
    URust_Item_Scope.lookup_type \<^context> "ScopedPacket"
  val SOME scoped_constructor =
    URust_Item_Scope.lookup_constructor \<^context> "ScopedPacket"
  val _ =
    if URust_Item_Scope.type_hol_name scoped_type =
        URust_Item_Scope.constructor_hol_type scoped_constructor
    then ()
    else error "left locale datatype scope identities disagree"
\<close>

end

locale datatype_scope_right =
  fixes marker_right :: nat
begin

urust_datatype scoped_packet \<open>
  struct ScopedPacket {
    value: bool,
  }
\<close>

urust_expr scoped_packet_right_value \<open>
  ScopedPacket { value: false }
\<close>

ML_val \<open>
  val SOME scoped_type =
    URust_Item_Scope.lookup_type \<^context> "ScopedPacket"
  val SOME scoped_constructor =
    URust_Item_Scope.lookup_constructor \<^context> "ScopedPacket"
  val _ =
    if URust_Item_Scope.type_hol_name scoped_type =
        URust_Item_Scope.constructor_hol_type scoped_constructor
    then ()
    else error "right locale datatype scope identities disagree"
\<close>

end

ML_val \<open>
  val NONE =
    URust_Item_Scope.lookup_type \<^context> "ScopedPacket"
  val NONE =
    URust_Item_Scope.lookup_constructor \<^context> "ScopedPacket"
\<close>

ML_val \<open>
  local
    fun find_from text needle offset =
      if offset + size needle > size text
      then error ("missing datatype markup token " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle =
      let
        val raw = find_from text needle 0
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start,
           Position.symbol_explode needle token_start)
      end

    val source_text =
      " struct TauMarkup(" ^
        "u8, u16, u32, u64, usize, i32, i64, bool, (), " ^
        "\<tau>" ^ Symbol.open_ ^ "nat option" ^
        Symbol.close ^ ",); "
    val source_start =
      Position.make0 5 20 200 "" "" "datatype-tau-markup"
    val captured_reports =
      Synchronized.var
        "urust_datatype_tau_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (URust_Parser.parse_datatype_source
                    \<^context>
                    (Parser_Lex_Util.positioned_content_source
                      source_text source_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body
          (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int
          (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int
          (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup

    val tau_position =
      token_position source_text source_start "\<tau>"
    val opener_position =
      token_position source_text source_start Symbol.open_
    val closer_position =
      token_position source_text source_start Symbol.close
    val _ =
      if has_markup Markup.literalN tau_position
      then ()
      else error "\<tau> type-cartouche prefix lacks literal markup"
    val _ =
      if has_markup Markup.delimiterN opener_position
      then ()
      else error "\<tau> type-cartouche opener lacks delimiter markup"
    val _ =
      if has_markup Markup.delimiterN closer_position
      then ()
      else error "\<tau> type-cartouche closer lacks delimiter markup"
    val _ =
      List.app
        (fn primitive =>
          let
            val position =
              token_position source_text source_start primitive
          in
            if has_markup Markup.keyword1N position andalso
                has_markup Markup.typingN position
            then ()
            else
              error
                ("datatype primitive " ^ quote primitive ^
                  " lacks keyword/typing markup")
          end)
        ["u8", "u16", "u32", "u64", "usize",
         "i32", "i64", "bool"]
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    val semantic_ctxt =
      Context_Position.set_visible true \<^context>

    fun find_from text needle offset =
      if offset + size needle > size text
      then error ("missing datatype semantic-markup token " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun capture_markup label action =
      let
        val captured =
          Synchronized.var
            ("urust_datatype_semantic_" ^ label)
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  action ()) ())
        fun collect (XML.Text _) result = result
          | collect (XML.Elem (markup, tree)) result =
              fold collect tree (markup :: result)
      in
        fold collect
          (maps YXML.parse_body
            (Synchronized.value captured)) []
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int
          (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int
          (Position.end_offset_of position)

    fun has_markup markup_name position markup =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup

    fun has_constant position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN =
              SOME Markup.constantN andalso
            has_position properties position)
        markup

    fun has_any_entity position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            has_position properties position)
        markup

    fun assert_selector label position markup =
      if has_constant position markup andalso
          not (has_markup Markup.freeN position markup)
      then ()
      else
        let
          val actual =
            markup
            |> filter
                (fn (_, properties) =>
                  has_position properties position)
            |> map
                (fn (name, properties) =>
                  name ^ ":" ^
                    the_default ""
                      (Properties.get properties
                        Markup.kindN))
        in
          error
            (label ^
              " is not marked as a selector constant; actual markup: " ^
              commas_quote actual)
        end

    fun assert_constructor label position markup =
      if has_constant position markup andalso
          has_markup Markup.keyword3N position markup andalso
          not (has_markup Markup.freeN position markup)
      then ()
      else error (label ^ " lacks constructor identity/styling markup")

    fun assert_type_qualifier label position markup =
      if has_any_entity position markup andalso
          has_markup Markup.keyword3N position markup andalso
          not (has_markup Markup.freeN position markup)
      then ()
      else error (label ^ " lacks datatype identity/styling markup")

    fun expression_markup_in ctxt label text start =
      capture_markup label
        (fn () =>
          ignore
            (Parser_Test_Elaboration.expression
              ctxt
              (Parser_Lex_Util.positioned_content_source
                text start)))

    fun expression_markup label text start =
      expression_markup_in semantic_ctxt label text start

    val construction_text =
      "ParserPoint { x: 1u32, history: " ^
        "\<llangle>[] :: 32 word list\<rrangle>, }"
    val construction_start =
      Position.make0 8 30 300 "" ""
        "datatype-construction-markup"
    val construction_markup =
      expression_markup "construction"
        construction_text construction_start
    val (_, construction_head) =
      token_position construction_text construction_start
        "ParserPoint" 0
    val (_, construction_x) =
      token_position construction_text construction_start
        "x" 0
    val (_, construction_history) =
      token_position construction_text construction_start
        "history" 0
    val _ =
      assert_constructor "named-struct construction head"
        construction_head construction_markup
    val _ =
      assert_selector "constructed field x"
        construction_x construction_markup
    val _ =
      assert_selector "constructed field history"
        construction_history construction_markup

    val pattern_text =
      "match \<llangle>undefined :: parser_message\<rrangle> { " ^
        "ParserMessage::Named { code, payload: _ } \<Rightarrow> code, " ^
        "_ \<Rightarrow> 0u32, }"
    val pattern_start =
      Position.make0 12 40 500 "" ""
        "datatype-pattern-markup"
    val pattern_markup =
      expression_markup "pattern" pattern_text pattern_start
    val (qualifier_raw, qualifier_position) =
      token_position pattern_text pattern_start
        "ParserMessage" 0
    val (named_raw, named_position) =
      token_position pattern_text pattern_start
        "Named" (qualifier_raw + size "ParserMessage")
    val (_, pattern_code) =
      token_position pattern_text pattern_start
        "code" (named_raw + size "Named")
    val (_, pattern_payload) =
      token_position pattern_text pattern_start
        "payload" (named_raw + size "Named")
    val _ =
      assert_type_qualifier "qualified enum datatype"
        qualifier_position pattern_markup
    val _ =
      assert_constructor "qualified enum variant"
        named_position pattern_markup
    val _ =
      assert_selector "named-variant field code"
        pattern_code pattern_markup
    val _ =
      assert_selector "named-variant field payload"
        pattern_payload pattern_markup

    val call_text =
      "ParserMessage::Data(2u32, None)"
    val call_start =
      Position.make0 16 50 700 "" ""
        "datatype-call-markup"
    val call_markup =
      expression_markup "call" call_text call_start
    val (call_qualifier_raw, call_qualifier_position) =
      token_position call_text call_start "ParserMessage" 0
    val (_, call_constructor_position) =
      token_position call_text call_start "Data"
        (call_qualifier_raw + size "ParserMessage")
    val _ =
      assert_type_qualifier "tuple-variant call datatype"
        call_qualifier_position call_markup
    val _ =
      assert_constructor "tuple-variant call constructor"
        call_constructor_position call_markup

    val bool_text = "bool"
    val bool_start =
      Position.make0 20 60 900 "" ""
        "datatype-contextual-bool-markup"
    val (_, bool_ctxt) =
      Variable.add_fixes ["bool"] semantic_ctxt
    val bool_markup =
      expression_markup_in bool_ctxt "contextual-bool"
        bool_text bool_start
    val (_, bool_position) =
      token_position bool_text bool_start "bool" 0
    val _ =
      if has_markup Markup.keyword1N bool_position bool_markup
      then
        error
          "expression identifier bool inherited datatype keyword markup"
      else ()
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    fun require_sugar name =
      (case Ctr_Sugar.ctr_sugar_of \<^context> name of
         SOME sugar => sugar
       | NONE => error ("missing datatype metadata for " ^ quote name))

    fun constructor_names sugar =
      map (Long_Name.base_name o dest_Const_name) (#ctrs sugar)

    fun constructor_argument_types sugar =
      (case #ctrs sugar of
         [Const (name, _)] =>
           binder_types
             (Consts.the_constraint
               (Proof_Context.consts_of \<^context>) name)
       | _ => error "expected one generated constructor")

    val point = require_sugar \<^type_name>\<open>parser_point\<close>
    val tuple = require_sugar \<^type_name>\<open>parser_tuple\<close>
    val marker = require_sugar \<^type_name>\<open>parser_marker\<close>
    val acronym = require_sugar \<^type_name>\<open>http_server_status\<close>
    val primitives = require_sugar \<^type_name>\<open>parser_primitives\<close>
    val message = require_sugar \<^type_name>\<open>parser_message\<close>
    val wire = require_sugar \<^type_name>\<open>wire_packet_hol\<close>
    val number_box =
      require_sugar \<^type_name>\<open>parser_number_box\<close>
    val flag_box =
      require_sugar \<^type_name>\<open>parser_flag_box\<close>
    val first_shared =
      require_sugar \<^type_name>\<open>first_shared_choice\<close>
    val second_shared =
      require_sugar \<^type_name>\<open>second_shared_choice\<close>
    val composite =
      require_sugar \<^type_name>\<open>parser_composite\<close>
    val arity14 =
      require_sugar \<^type_name>\<open>parser_arity14\<close>
    val commented =
      require_sugar \<^type_name>\<open>parser_commented\<close>
    val acronym_digit =
      require_sugar \<^type_name>\<open>http2_server_state\<close>
    val acronym_mixed =
      require_sugar \<^type_name>\<open>xml_http_request\<close>

    val _ =
      if constructor_names point = ["make_parser_point"] andalso
         constructor_names tuple = ["make_parser_tuple"] andalso
         constructor_names marker = ["make_parser_marker"] andalso
         constructor_names acronym = ["make_http_server_status"] andalso
         constructor_names message = ["Empty", "Data", "Named"] andalso
         constructor_names wire = ["make_wire_packet_hol"] andalso
         constructor_names number_box = ["make_parser_number_box"] andalso
         constructor_names flag_box = ["make_parser_flag_box"] andalso
         constructor_names first_shared =
           ["SharedIdle", "SharedPayload", "SharedNamed"] andalso
         constructor_names second_shared =
           ["SharedIdle", "SharedPayload", "SharedNamed"] andalso
         constructor_names composite = ["make_parser_composite"] andalso
         constructor_names arity14 = ["make_parser_arity14"] andalso
         constructor_names commented = ["make_parser_commented"] andalso
         constructor_names acronym_digit =
           ["make_http2_server_state"] andalso
         constructor_names acronym_mixed =
           ["make_xml_http_request"]
      then ()
      else error "urust_datatype generated unexpected constructors"

    val primitive_types = constructor_argument_types primitives

    val _ =
      if primitive_types =
          [\<^typ>\<open>8 word\<close>, \<^typ>\<open>16 word\<close>,
           \<^typ>\<open>32 word\<close>, \<^typ>\<open>64 word\<close>,
           \<^typ>\<open>64 word\<close>, \<^typ>\<open>32 word\<close>,
           \<^typ>\<open>64 word\<close>, \<^typ>\<open>bool\<close>,
           \<^typ>\<open>unit\<close>]
      then ()
      else error "urust_datatype primitive type mapping changed"

    val _ =
      if constructor_argument_types composite =
          [\<^typ>\<open>parser_point\<close>,
           \<^typ>\<open>parser_message list\<close>,
           \<^typ>\<open>nat \<times> bool option\<close>]
      then ()
      else error "nested generated/user HOL type mapping changed"
    val _ =
      if length (constructor_argument_types arity14) = 14
      then ()
      else error "maximum supported constructor arity changed"

    val SOME point_type =
      URust_Item_Scope.lookup_type \<^context> "ParserPoint"
    val SOME point_constructor =
      URust_Item_Scope.lookup_constructor \<^context> "ParserPoint"
    val SOME data_constructor =
      URust_Item_Scope.lookup_constructor
        \<^context> "ParserMessage::Data"
    val SOME named_constructor =
      URust_Item_Scope.lookup_constructor
        \<^context> "ParserMessage::Named"
    val SOME wire_type =
      URust_Item_Scope.lookup_type \<^context> "WirePacket"
    val SOME wire_constructor =
      URust_Item_Scope.lookup_constructor \<^context> "WirePacket"
    val SOME number_box_constructor =
      URust_Item_Scope.lookup_constructor
        \<^context> "ParserNumberBox"
    val SOME flag_box_constructor =
      URust_Item_Scope.lookup_constructor
        \<^context> "ParserFlagBox"
    val SOME first_shared_payload =
      URust_Item_Scope.lookup_constructor
        \<^context> "FirstSharedChoice::SharedPayload"
    val SOME second_shared_payload =
      URust_Item_Scope.lookup_constructor
        \<^context> "SecondSharedChoice::SharedPayload"
    val SOME first_shared_named =
      URust_Item_Scope.lookup_constructor
        \<^context> "FirstSharedChoice::SharedNamed"
    val SOME second_shared_named =
      URust_Item_Scope.lookup_constructor
        \<^context> "SecondSharedChoice::SharedNamed"
    val NONE =
      URust_Item_Scope.lookup_constructor \<^context> "Data"
    val NONE =
      URust_Item_Scope.lookup_constructor \<^context> "SharedPayload"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "wirepacket"

    val _ =
      if URust_Item_Scope.type_hol_name point_type =
          \<^type_name>\<open>parser_point\<close> andalso
         URust_Item_Scope.constructor_shape point_constructor =
          URust_Item_Scope.Named_Constructor andalso
         URust_Item_Scope.constructor_shape data_constructor =
          URust_Item_Scope.Tuple_Constructor andalso
         map fst
           (URust_Item_Scope.constructor_fields named_constructor) =
          ["code", "payload"] andalso
         URust_Item_Scope.type_hol_name wire_type =
           \<^type_name>\<open>wire_packet_hol\<close> andalso
         URust_Item_Scope.constructor_hol_type wire_constructor =
           \<^type_name>\<open>wire_packet_hol\<close> andalso
         URust_Item_Scope.constructor_origin first_shared_payload =
           URust_Item_Scope.Enum_Variant andalso
         URust_Item_Scope.constructor_shape first_shared_payload =
           URust_Item_Scope.Tuple_Constructor andalso
         URust_Item_Scope.constructor_shape first_shared_named =
           URust_Item_Scope.Named_Constructor andalso
         map fst
           (URust_Item_Scope.constructor_fields
             second_shared_named) = ["value"]
      then ()
      else error "urust_datatype item scope metadata changed"

    val _ =
      if Term.aconv_untyped
          (URust_Item_Scope.constructor_term first_shared_payload,
           URust_Item_Scope.constructor_term second_shared_payload)
      then error "shared enum variant spellings collapsed to one backend"
      else ()

    val value_field_backends =
      Micro_Rust_Names.lookups
        \<^context> Micro_Rust_Names.NField "value"
      |> map #hol_term
    val value_field_backend_names =
      value_field_backends
      |> map_filter
          (fn Const (name, _) => SOME name
            | _ => NONE)
    val _ =
      if exists
          (String.isSubstring "parser_number_box")
          value_field_backend_names andalso
         exists
          (String.isSubstring "parser_flag_box")
          value_field_backend_names
      then ()
      else error "generated same-name field aliases stopped overloading"

    val rust_type_names =
      URust_Item_Scope.dump_types \<^context>
      |> map URust_Item_Scope.type_rust_name
    val _ =
      if length rust_type_names =
          length (distinct (op =) rust_type_names)
      then ()
      else error "generated Rust item scope contains duplicate type keys"
    val _ =
      List.app
        (fn name =>
          if member (op =) rust_type_names name then ()
          else error ("generated Rust item scope lost " ^ quote name))
        ["ParserPoint", "WirePacket", "FirstSharedChoice",
         "SecondSharedChoice", "ParserArity14"]

    val constructor_constants =
      maps #ctrs
        [point, tuple, marker, primitives, message, wire,
         number_box, flag_box, first_shared, second_shared,
         composite, arity14, commented, acronym_digit,
         acronym_mixed]
      |> map dest_Const_name
    val theory = Proof_Context.theory_of \<^context>
    val _ =
      if forall (Code.is_constr theory) constructor_constants
      then ()
      else error "generated constructor is missing Code.is_constr metadata"

    val _ =
      List.app
        (fn constructor =>
          if is_some
              (Case_Translation.lookup_by_constr_permissive
                \<^context> (dest_Const constructor))
          then ()
          else error "generated constructor is missing case metadata")
        (maps #ctrs [message, first_shared, second_shared])
  in
    val _ = ()
  end
\<close>

section\<open> Generated source navigation markup \<close>

ML_val \<open>
  local
    structure I = URust_Item_Scope

    val ctxt = Context_Position.set_visible true \<^context>
    val item_kind = "urust_item"
    val constructor_kind = "urust_constructor"
    val field_kind = "urust_field"

    fun audit_assert message condition =
      if condition then ()
      else error ("generated source navigation audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text
      then error ("missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun collect_markup_order (XML.Text _) = []
      | collect_markup_order (XML.Elem (markup, body)) =
          markup :: maps collect_markup_order body

    fun capture_reports label action =
      let
        val captured =
          Synchronized.var
            ("generated_source_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured
            (fn current => current @ chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () => Exn.result action ()) ())
              ())
      in
        (result,
         Synchronized.value captured
         |> maps YXML.parse_body
         |> maps collect_markup_order)
      end

    fun capture serial label text declared_type =
      let
        val start =
          Position.make0
            (120 + serial) (12000 + serial * 1200) 0
            "" "" ("generated-source-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (result, markup) =
          capture_reports label
            (fn () =>
              URust_Command.elaborate ctxt
                {kind = URust_Command.Expression,
                 source = source,
                 arguments = [],
                 arguments_pos = #2 (Input.range_of source),
                 declared_type =
                   Option.map
                     (fn typ => (typ, Position.none))
                     declared_type})
      in (start, result, markup) end

    fun require_success label (Exn.Res term) = term
      | require_success label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn
          else
            error
              (label ^ " failed: " ^
                Runtime.exn_message exn)

    fun require_failure label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn
          else ()
      | require_failure label (Exn.Res _) =
          error (label ^ " unexpectedly succeeded")

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int
          (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int
          (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_events position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                has_position properties position
            then
              SOME
                (Properties.get properties Markup.kindN,
                 Properties.get properties Markup.nameN,
                 Properties.get properties Markup.defN,
                 Properties.get properties Markup.refN)
            else NONE)

    fun definition_id kind name position markup =
      (case
        entity_events position markup
        |> map_filter
            (fn (SOME actual_kind, SOME actual_name,
                 definition, _) =>
                  if actual_kind = kind andalso
                      actual_name = name
                  then definition
                  else NONE
              | _ => NONE)
        |> distinct (op =)
       of
         [identity] => identity
       | identities =>
           error
             ("expected one definition identity for " ^
               quote (kind ^ ":" ^ name) ^ ", found [" ^
               commas_quote identities ^ "]"))

    fun source_reference kind name position markup =
      entity_events position markup
      |> map_filter
          (fn (SOME actual_kind, SOME actual_name, _, reference) =>
                if actual_kind = kind andalso
                    actual_name = name
                then reference
                else NONE
            | _ => NONE)

    fun print_option NONE = "-"
      | print_option (SOME value) = value

    fun print_event (kind, name, definition, reference) =
      "(" ^ print_option kind ^ "," ^ print_option name ^
        ",def=" ^ print_option definition ^
        ",ref=" ^ print_option reference ^ ")"

    fun assert_source_final label source_kind source_name
        source_identity backend_kind backend_name position markup =
      let
        val events = entity_events position markup
        val final_event =
          if null events then NONE else SOME (List.last events)
        val source_refs =
          source_reference source_kind source_name position markup
      in
        audit_assert (label ^ " lost backend navigation")
          (exists
            (fn (SOME kind, SOME name, _, _) =>
                  kind = backend_kind andalso
                    name = backend_name
              | _ => false)
            events);
        audit_assert (label ^ " source reference changed")
          (source_refs = [source_identity]);
        if final_event =
            SOME
              (SOME source_kind, SOME source_name,
               NONE, SOME source_identity)
        then ()
        else
          error
            ("generated source navigation audit: " ^ label ^
              " source declaration was not final; events = " ^
              commas_quote (map print_event events));
        audit_assert (label ^ " acquired notation ownership")
          (not
            (exists
              (fn (SOME kind, _, _, _) =>
                    kind = Micro_Rust_Names.notationN
                | _ => false)
              events))
      end

    fun assert_no_semantic label position markup =
      let
        fun semantic_kind kind =
          member (op =)
            [item_kind, constructor_kind, field_kind,
             Micro_Rust_Names.notationN,
             Markup.constantN, Markup.type_nameN]
            kind
      in
        audit_assert (label ^ " emitted premature semantic entity")
          (not
            (exists
              (fn (SOME kind, _, _, _) => semantic_kind kind
                | _ => false)
              (entity_events position markup)))
      end

    fun constructor_name entry =
      (case I.constructor_term entry of
         Const (name, _) => name
       | _ => error "generated constructor has no constant identity")

    fun selector_name field =
      (case I.field_selector field of
         Const (name, _) => name
       | _ => error "generated field has no selector identity")

    fun source_field entry name =
      (case
        I.constructor_field_entries entry
        |> filter (fn field => I.field_rust_name field = name)
       of
         [field] => field
       | fields =>
           error
             ("expected one stored source field " ^ quote name ^
               ", found " ^ string_of_int (length fields)))

    val SOME point_type =
      I.lookup_type ctxt "ParserPoint"
    val SOME message_type =
      I.lookup_type ctxt "ParserMessage"
    val SOME marker_constructor =
      I.lookup_constructor ctxt "ParserMarker"
    val SOME tuple_constructor =
      I.lookup_constructor ctxt "ParserTuple"
    val SOME point_constructor =
      I.lookup_constructor ctxt "ParserPoint"
    val SOME empty_constructor =
      I.lookup_constructor ctxt "ParserMessage::Empty"
    val SOME data_constructor =
      I.lookup_constructor ctxt "ParserMessage::Data"
    val SOME named_constructor =
      I.lookup_constructor ctxt "ParserMessage::Named"
    val SOME renamed_packet_constructor =
      I.lookup_constructor ctxt "RenamedPacket"
    val SOME renamed_data_constructor =
      I.lookup_constructor ctxt "RenamedChoice::Data"
    val SOME renamed_ready_constructor =
      I.lookup_constructor ctxt "RenamedChoice::Ready"

    val point_x = source_field point_constructor "x"
    val point_history = source_field point_constructor "history"
    val named_code = source_field named_constructor "code"
    val named_payload = source_field named_constructor "payload"
    val renamed_sample = source_field renamed_packet_constructor "renameSampleValue"

    val (definition_result, definition_markup) =
      capture_reports "definitions"
        (fn () =>
          (I.report_type_definition point_type;
           I.report_type_definition message_type;
           List.app I.report_constructor_definition
             [marker_constructor, tuple_constructor,
              point_constructor, empty_constructor,
              data_constructor, named_constructor,
              renamed_packet_constructor, renamed_data_constructor,
              renamed_ready_constructor];
           List.app I.report_field_definition
             [point_x, point_history, named_code, named_payload, renamed_sample]))
    val _ = ignore (require_success "definition replay" definition_result)

    fun type_definition entry =
      definition_id item_kind (I.type_rust_name entry)
        (I.type_position entry) definition_markup
    fun constructor_definition entry =
      definition_id constructor_kind
        (I.constructor_rust_path entry)
        (I.constructor_position entry) definition_markup
    fun field_definition entry =
      definition_id field_kind
        (I.field_rust_path entry ^
          "." ^ I.field_rust_name entry)
        (I.field_position entry) definition_markup

    val point_type_id = type_definition point_type
    val message_type_id = type_definition message_type
    val marker_constructor_id =
      constructor_definition marker_constructor
    val tuple_constructor_id =
      constructor_definition tuple_constructor
    val point_constructor_id =
      constructor_definition point_constructor
    val empty_constructor_id =
      constructor_definition empty_constructor
    val data_constructor_id =
      constructor_definition data_constructor
    val named_constructor_id =
      constructor_definition named_constructor
    val point_x_id = field_definition point_x
    val point_history_id = field_definition point_history
    val named_code_id = field_definition named_code
    val named_payload_id = field_definition named_payload

    val renamed_struct_text =
      "RenamedPacket { renameSampleValue: 1u32, valid: true }"
    val (renamed_struct_start, renamed_struct_result, renamed_struct_markup) =
      capture 18 "renamed-struct" renamed_struct_text NONE
    val _ = ignore (require_success "renamed struct navigation" renamed_struct_result)
    val (_, renamed_sample_position) =
      token_position renamed_struct_text renamed_struct_start "renameSampleValue" 0
    val _ =
      assert_source_final "renamed selector source"
        field_kind "RenamedPacket.renameSampleValue"
        (field_definition renamed_sample) Markup.constantN
        \<^const_name>\<open>sample\<close>
        renamed_sample_position renamed_struct_markup

    val renamed_call_text = "RenamedChoice::Data(1u32, true)"
    val (renamed_call_start, renamed_call_result, renamed_call_markup) =
      capture 19 "renamed-call" renamed_call_text NONE
    val _ = ignore (require_success "renamed constructor navigation" renamed_call_result)
    val (_, renamed_data_position) =
      token_position renamed_call_text renamed_call_start "Data" 0
    val _ =
      assert_source_final "renamed constructor source"
        constructor_kind "RenamedChoice::Data"
        (constructor_definition renamed_data_constructor) Markup.constantN
        \<^const_name>\<open>ModelData\<close>
        renamed_data_position renamed_call_markup

    val renamed_pattern_text =
      "match \<llangle>undefined :: renamed_choice_hol\<rrangle> { " ^
      "RenamedChoice::Ready { value, active: _ } \<Rightarrow> value, _ \<Rightarrow> 0u32 }"
    val (renamed_pattern_start, renamed_pattern_result, renamed_pattern_markup) =
      capture 20 "renamed-pattern" renamed_pattern_text NONE
    val _ = ignore (require_success "renamed pattern navigation" renamed_pattern_result)
    val (_, renamed_ready_position) =
      token_position renamed_pattern_text renamed_pattern_start "Ready" 0
    val _ =
      assert_source_final "renamed pattern source"
        constructor_kind "RenamedChoice::Ready"
        (constructor_definition renamed_ready_constructor) Markup.constantN
        \<^const_name>\<open>ModelReady\<close>
        renamed_ready_position renamed_pattern_markup

    val marker_text = "ParserMarker"
    val (marker_start, marker_result, marker_markup) =
      capture 1 "struct-value" marker_text NONE
    val _ = ignore (require_success "generated struct value" marker_result)
    val (_, marker_position) =
      token_position marker_text marker_start "ParserMarker" 0
    val _ =
      assert_source_final "generated struct value"
        constructor_kind "ParserMarker"
        marker_constructor_id Markup.constantN
        (constructor_name marker_constructor)
        marker_position marker_markup

    val tuple_text = "ParserTuple(1u32, true, None)"
    val (tuple_start, tuple_result, tuple_markup) =
      capture 2 "struct-call" tuple_text NONE
    val _ = ignore (require_success "generated struct call" tuple_result)
    val (_, tuple_position) =
      token_position tuple_text tuple_start "ParserTuple" 0
    val _ =
      assert_source_final "generated struct call"
        constructor_kind "ParserTuple"
        tuple_constructor_id Markup.constantN
        (constructor_name tuple_constructor)
        tuple_position tuple_markup

    val struct_text =
      "ParserPoint { x: 1u32, history: " ^
        "\<llangle>[] :: 32 word list\<rrangle>, }"
    val (struct_start, struct_result, struct_markup) =
      capture 3 "struct-expression" struct_text NONE
    val _ =
      ignore
        (require_success "generated struct expression" struct_result)
    val (_, struct_head) =
      token_position struct_text struct_start "ParserPoint" 0
    val (struct_x_raw, struct_x_position) =
      token_position struct_text struct_start "x" 0
    val (_, struct_history_position) =
      token_position struct_text struct_start "history"
        (struct_x_raw + size "x")
    val _ =
      assert_source_final "generated struct-expression head"
        constructor_kind "ParserPoint"
        point_constructor_id Markup.constantN
        (constructor_name point_constructor)
        struct_head struct_markup
    val _ =
      assert_source_final "generated struct-expression field x"
        field_kind "ParserPoint.x"
        point_x_id Markup.constantN
        (selector_name point_x)
        struct_x_position struct_markup
    val _ =
      assert_source_final "generated struct-expression field history"
        field_kind "ParserPoint.history"
        point_history_id Markup.constantN
        (selector_name point_history)
        struct_history_position struct_markup

    val empty_text = "ParserMessage::Empty"
    val (empty_start, empty_result, empty_markup) =
      capture 4 "enum-value" empty_text NONE
    val _ = ignore (require_success "generated enum value" empty_result)
    val (empty_qualifier_raw, empty_qualifier) =
      token_position empty_text empty_start "ParserMessage" 0
    val (_, empty_terminal) =
      token_position empty_text empty_start "Empty"
        (empty_qualifier_raw + size "ParserMessage::")
    val _ =
      assert_source_final "generated enum value qualifier"
        item_kind "ParserMessage"
        message_type_id Markup.type_nameN
        (I.type_hol_name message_type)
        empty_qualifier empty_markup
    val _ =
      assert_source_final "generated enum value terminal"
        constructor_kind "ParserMessage::Empty"
        empty_constructor_id Markup.constantN
        (constructor_name empty_constructor)
        empty_terminal empty_markup

    val call_text = "ParserMessage::Data(2u32, None)"
    val (call_start, call_result, call_markup) =
      capture 5 "enum-call" call_text NONE
    val _ = ignore (require_success "generated enum call" call_result)
    val (call_qualifier_raw, call_qualifier) =
      token_position call_text call_start "ParserMessage" 0
    val (_, call_terminal) =
      token_position call_text call_start "Data"
        (call_qualifier_raw + size "ParserMessage::")
    val _ =
      assert_source_final "generated enum call qualifier"
        item_kind "ParserMessage"
        message_type_id Markup.type_nameN
        (I.type_hol_name message_type)
        call_qualifier call_markup
    val _ =
      assert_source_final "generated enum call terminal"
        constructor_kind "ParserMessage::Data"
        data_constructor_id Markup.constantN
        (constructor_name data_constructor)
        call_terminal call_markup

    val pattern_text =
      "match \<llangle>undefined :: parser_message\<rrangle> { " ^
        "ParserMessage::Named { code, payload: _ } \<Rightarrow> code, " ^
        "_ \<Rightarrow> 0u32, }"
    val (pattern_start, pattern_result, pattern_markup) =
      capture 6 "enum-pattern" pattern_text NONE
    val _ =
      ignore
        (require_success "generated enum pattern" pattern_result)
    val (pattern_qualifier_raw, pattern_qualifier) =
      token_position pattern_text pattern_start "ParserMessage" 0
    val (pattern_terminal_raw, pattern_terminal) =
      token_position pattern_text pattern_start "Named"
        (pattern_qualifier_raw + size "ParserMessage::")
    val (pattern_code_raw, pattern_code) =
      token_position pattern_text pattern_start "code"
        (pattern_terminal_raw + size "Named")
    val (_, pattern_payload) =
      token_position pattern_text pattern_start "payload"
        (pattern_code_raw + size "code")
    val _ =
      assert_source_final "generated enum pattern qualifier"
        item_kind "ParserMessage"
        message_type_id Markup.type_nameN
        (I.type_hol_name message_type)
        pattern_qualifier pattern_markup
    val _ =
      assert_source_final "generated enum pattern terminal"
        constructor_kind "ParserMessage::Named"
        named_constructor_id Markup.constantN
        (constructor_name named_constructor)
        pattern_terminal pattern_markup
    val _ =
      assert_source_final "generated enum pattern field code"
        field_kind "ParserMessage::Named.code"
        named_code_id Markup.constantN
        (selector_name named_code)
        pattern_code pattern_markup
    val _ =
      assert_source_final "generated enum pattern field payload"
        field_kind "ParserMessage::Named.payload"
        named_payload_id Markup.constantN
        (selector_name named_payload)
        pattern_payload pattern_markup

    val native_text = "None"
    val (native_start, native_result, native_markup) =
      capture 7 "native-constructor" native_text
        (SOME
          "(unit, 32 word option, unit, unit, unit, unit) expression")
    val _ =
      ignore
        (require_success "native constructor control" native_result)
    val (_, native_position) =
      token_position native_text native_start "None" 0
    val native_events = entity_events native_position native_markup
    val _ =
      audit_assert "native constructor lost HOL navigation"
        (exists
          (fn (SOME kind, SOME name, _, _) =>
                kind = Markup.constantN andalso
                  name = \<^const_name>\<open>None\<close>
            | _ => false)
          native_events)
    val _ =
      audit_assert "native constructor acquired generated ownership"
        (not
          (exists
            (fn (SOME kind, _, _, _) =>
                  member (op =)
                    [item_kind, constructor_kind, field_kind,
                     Micro_Rust_Names.notationN]
                    kind
              | _ => false)
            native_events))

    val lifted_text = "Some(3u32)"
    val (lifted_start, lifted_result, lifted_markup) =
      capture 8 "lifted-backend" lifted_text NONE
    val _ =
      ignore
        (require_success "lifted backend control" lifted_result)
    val (_, lifted_position) =
      token_position lifted_text lifted_start "Some" 0
    val lifted_events =
      entity_events lifted_position lifted_markup
    val some_entry =
      (case
        Micro_Rust_Names.lookups
          ctxt Micro_Rust_Names.NFunction "Some"
       of
         [entry] => entry
       | entries =>
           error
             ("expected one Some registration, found " ^
               string_of_int (length entries)))
    val some_ref = Value.print_int (#serial some_entry)
    val _ =
      audit_assert "lifted backend lost wrapped constructor navigation"
        (exists
          (fn (SOME kind, SOME name, _, _) =>
                kind = Markup.constantN andalso
                  name = \<^const_name>\<open>Some\<close>
            | _ => false)
          lifted_events)
    val _ =
      audit_assert "lifted backend retained wrapper navigation"
        (not
          (exists
            (fn (SOME kind, SOME name, _, _) =>
                  kind = Markup.constantN andalso
                    name = \<^const_name>\<open>lift_fun1\<close>
              | _ => false)
            lifted_events))
    val _ =
      audit_assert "selected notation declaration was not final"
        (List.last lifted_events =
          (SOME Micro_Rust_Names.notationN, SOME "Some",
           NONE, SOME some_ref))

    fun failure_case serial label text token_specs =
      let
        val (start, result, markup) =
          capture serial label text NONE
        val _ = require_failure label result
        val _ =
          List.app
            (fn (token, offset) =>
              let
                val (_, position) =
                  token_position text start token offset
              in
                assert_no_semantic
                  (label ^ " " ^ quote token)
                  position markup
              end)
            token_specs
      in () end

    val wrong_arity_text =
      "ParserMessage::Data(1u32)"
    val wrong_arity_qualifier =
      find_from wrong_arity_text "ParserMessage" 0
    val _ =
      failure_case 9 "wrong-generated-arity"
        wrong_arity_text
        [("ParserMessage", wrong_arity_qualifier),
         ("Data",
          wrong_arity_qualifier + size "ParserMessage::")]

    val _ =
      failure_case 10 "unsupported-generated-generics"
        "ParserTuple::<1>(1u32, true, None)"
        [("ParserTuple", 0)]

    val _ =
      failure_case 11 "wrong-generated-value-shape"
        "ParserTuple"
        [("ParserTuple", 0)]

    val named_expression_text =
      "ParserMessage::Named { code: 1u32, payload: " ^
        "\<llangle>[] :: 8 word list\<rrangle>, }"
    val named_expression_qualifier =
      find_from named_expression_text "ParserMessage" 0
    val named_expression_terminal =
      find_from named_expression_text "Named"
        (named_expression_qualifier + size "ParserMessage::")
    val (named_expression_start, named_expression_result, named_expression_markup) =
      capture 12 "generated-named-construction" named_expression_text NONE
    val _ = ignore (require_success "generated named enum construction" named_expression_result)
    val (_, named_expression_type_pos) =
      token_position named_expression_text named_expression_start "ParserMessage" 0
    val (_, named_expression_constructor_pos) =
      token_position named_expression_text named_expression_start "Named" named_expression_terminal
    val _ =
      assert_source_final "named construction qualifier" item_kind "ParserMessage"
        message_type_id Markup.type_nameN (I.type_hol_name message_type)
        named_expression_type_pos named_expression_markup
    val _ =
      assert_source_final "named construction terminal" constructor_kind "ParserMessage::Named"
        named_constructor_id Markup.constantN (constructor_name named_constructor)
        named_expression_constructor_pos named_expression_markup
    val _ = List.app (fn (name, field, id) =>
      let
        val (_, position) = token_position named_expression_text named_expression_start name
          (named_expression_terminal + size "Named")
      in
        assert_source_final ("named construction field " ^ name) field_kind
          ("ParserMessage::Named." ^ name) id Markup.constantN (selector_name field)
          position named_expression_markup
      end) [("code", named_code, named_code_id), ("payload", named_payload, named_payload_id)]

    val _ = failure_case 18 "unknown-generated-initializer-field"
      ("ParserMessage::Named { unknown_code: 1u32, payload: " ^
        "\<llangle>[] :: 8 word list\<rrangle>, }")
      [("ParserMessage", 0), ("Named", size "ParserMessage::"),
       ("unknown_code", size "ParserMessage::Named { ")]

    val missing_field_text =
      "match \<llangle>undefined :: parser_point\<rrangle> { " ^
        "ParserPoint { x } \<Rightarrow> x, }"
    val missing_head =
      find_from missing_field_text "ParserPoint" 0
    val _ =
      failure_case 13 "missing-generated-pattern-field"
        missing_field_text
        [("ParserPoint", missing_head),
         ("x", missing_head + size "ParserPoint")]

    val unknown_field_text =
      "match \<llangle>undefined :: parser_point\<rrangle> { " ^
        "ParserPoint { unknown: _, .. } \<Rightarrow> 0u32, }"
    val unknown_head =
      find_from unknown_field_text "ParserPoint" 0
    val _ =
      failure_case 14 "unknown-generated-pattern-field"
        unknown_field_text
        [("ParserPoint", unknown_head),
         ("unknown", unknown_head + size "ParserPoint")]

    val duplicate_field_text =
      "match \<llangle>undefined :: parser_point\<rrangle> { " ^
        "ParserPoint { x: _, x: _, .. } \<Rightarrow> 0u32, }"
    val duplicate_head =
      find_from duplicate_field_text "ParserPoint" 0
    val duplicate_first =
      find_from duplicate_field_text "x"
        (duplicate_head + size "ParserPoint")
    val duplicate_second =
      find_from duplicate_field_text "x"
        (duplicate_first + size "x")
    val _ =
      failure_case 15 "duplicate-generated-pattern-field"
        duplicate_field_text
        [("ParserPoint", duplicate_head),
         ("x", duplicate_first),
         ("x", duplicate_second)]

    val malformed_nested_text =
      "match \<llangle>undefined :: parser_point\<rrangle> { " ^
        "ParserPoint { x: ParserMessage::Data(_, _, _), " ^
        "history: _ } \<Rightarrow> 0u32, }"
    val malformed_outer =
      find_from malformed_nested_text "ParserPoint" 0
    val malformed_x =
      find_from malformed_nested_text "x"
        (malformed_outer + size "ParserPoint")
    val malformed_inner =
      find_from malformed_nested_text "ParserMessage"
        (malformed_x + size "x")
    val malformed_data =
      find_from malformed_nested_text "Data"
        (malformed_inner + size "ParserMessage::")
    val _ =
      failure_case 16 "malformed-nested-generated-pattern"
        malformed_nested_text
        [("ParserPoint", malformed_outer),
         ("x", malformed_x),
         ("ParserMessage", malformed_inner),
         ("Data", malformed_data)]

    val _ =
      failure_case 17 "ambiguous-generated-basename"
        "SharedPayload(1u32)"
        [("SharedPayload", 0)]
  in
    val _ =
      writeln
        "Generated item, constructor, field, native, lifted, ordering, target, and delayed-failure navigation regressions passed"
  end
\<close>

section\<open> Command diagnostics and output \<close>

ML_val \<open>
  local
    fun run_command interactive source_name command_text () =
      let
        val thy = \<^theory>
        val quiet_baseline =
          "declare [[urust_pp_test = false, " ^
          "urust_pretty = false, urust_verbosity = 0]]\n"
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name)
            (quiet_baseline ^ command_text)
      in
        fold (Toplevel.command_exception interactive) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun plain_content body =
      XML.content_of body
      |> Symbol.explode
      |> filter_out Symbol.is_control
      |> implode

    fun capture_result interactive source_name command_text =
      let
        val captured =
          Synchronized.var
            ("urust_datatype_" ^ source_name) ([]: string list)
        fun capture chunks =
          if Position.file_of (Position.thread_data ()) =
              SOME source_name
          then Synchronized.change captured (append chunks)
          else ()
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.writeln_fn capture
              (fn () =>
                Exn.result
                  (run_command interactive source_name command_text)
                  ()) ())
        val body =
          YXML.parse_body
            (implode (Synchronized.value captured))
      in (result, body, plain_content body) end

    fun capture_full_result interactive source_name command_text =
      let
        val output =
          Synchronized.var
            ("urust_datatype_full_output_" ^ source_name)
            ([]: string list)
        val reports =
          Synchronized.var
            ("urust_datatype_full_reports_" ^ source_name)
            ([]: string list)
        fun collect target chunks =
          if Position.file_of (Position.thread_data ()) =
              SOME source_name
          then Synchronized.change target (append chunks)
          else ()
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn
              (collect reports)
              (fn () =>
                Unsynchronized.setmp Private_Output.writeln_fn
                  (collect output)
                  (fn () =>
                    Exn.result
                      (run_command interactive source_name command_text)
                      ()) ())
              ())
        val body =
          YXML.parse_body
            (implode (Synchronized.value output))
      in
        {result = result,
         body = body,
         plain = plain_content body,
         reports =
           maps YXML.parse_body
             (Synchronized.value reports)}
      end

    fun capture_warning source_name command_text =
      let
        val warnings =
          Synchronized.var
            ("urust_datatype_warnings_" ^ source_name)
            ([]: string list)
        fun collect chunks =
          if Position.file_of (Position.thread_data ()) =
              SOME source_name
          then Synchronized.change warnings (append chunks)
          else ()
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.warning_fn collect
              (fn () =>
                Exn.result
                  (run_command true source_name command_text)
                  ()) ())
      in
        (result,
         maps YXML.parse_body
           (Synchronized.value warnings)
         |> XML.content_of)
      end

    fun cartouche text =
      Symbol.open_ ^ text ^ Symbol.close

    fun type_cartouche text =
      "\<tau>" ^ cartouche text

    fun datatype_source name fields =
      cartouche
        (" struct " ^ name ^ " { " ^ fields ^ " } ")

    fun assert_contains label expected output =
      if String.isSubstring expected output then ()
      else
        error
          (label ^ " is missing " ^ quote expected ^
            ":\n" ^ output)

    fun assert_absent label unexpected output =
      if String.isSubstring unexpected output
      then
        error
          (label ^ " unexpectedly contains " ^ quote unexpected ^
            ":\n" ^ output)
      else ()

    fun assert_rejected_all label expected command_text =
      (case #1 (capture_result true label command_text) of
         Exn.Res _ =>
           error (label ^ " unexpectedly succeeded")
       | Exn.Exn exn =>
           let val message = Runtime.exn_message exn in
             if forall
                 (fn fragment =>
                   String.isSubstring fragment message)
                 expected
             then ()
             else
               error
                 (label ^ " produced the wrong diagnostic:\n" ^
                   message)
           end)

    fun assert_rejected label expected =
      assert_rejected_all label [expected]

    fun assert_succeeded label command_text =
      (case #1 (capture_result true label command_text) of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)

    fun assert_item_parser_rejected label expected text =
      let
        val position =
          Position.make0 1 1 0 "" ""
            ("datatype-parser-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source
            text position
      in
        (case Exn.result
            (fn () =>
              URust_Parser.parse_datatype_source
                \<^context> source) () of
           Exn.Res _ =>
             error (label ^ " item source unexpectedly parsed")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn
             then Exn.reraise exn
             else
               let val message = Runtime.exn_message exn in
                 if String.isSubstring expected message then ()
                 else
                   error
                     (label ^
                       " produced the wrong parser diagnostic:\n" ^
                       message)
               end)
      end

    fun assert_item_parser_succeeded label text =
      let
        val position =
          Position.make0 1 1 0 "" ""
            ("datatype-parser-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source
            text position
      in
        (case URust_Parser.parse_datatype_source \<^context> source of
           SOME _ => ()
         | NONE => error (label ^ " item source parsed as empty"))
      end

    fun tree_has_markup expected
          (XML.Elem ((actual, _), body)) =
          actual = expected orelse
            exists (tree_has_markup expected) body
      | tree_has_markup _ (XML.Text _) = false

    fun wrapped_markup_properties
          expected_markup expected_text tree =
      (case XML.unwrap_elem tree of
         SOME (((actual_markup, properties), _), body) =>
           (if actual_markup = expected_markup andalso
                XML.content_of body = expected_text
            then [properties]
            else []) @
           maps
             (wrapped_markup_properties
               expected_markup expected_text)
             body
       | NONE =>
           (case tree of
              XML.Elem (_, body) =>
                maps
                  (wrapped_markup_properties
                    expected_markup expected_text)
                  body
            | XML.Text _ => []))

    fun entity_kinds text body =
      maps
        (wrapped_markup_properties Markup.entityN text)
        body
      |> map_filter
          (fn properties =>
            Properties.get properties Markup.kindN)

    fun last_element label [] =
          error (label ^ " has no markup events")
      | last_element _ values = List.last values

    fun substring_index needle text =
      let
        val needle_size = size needle
        val text_size = size text
        fun search index =
          if index + needle_size > text_size
          then NONE
          else if String.substring
              (text, index, needle_size) = needle
          then SOME index
          else search (index + 1)
      in search 0 end

    fun result_context (Exn.Res state) = Toplevel.context_of state
      | result_context (Exn.Exn exn) = Exn.reraise exn

    fun registry_snapshot ctxt =
      Micro_Rust_Names.dump ctxt
      |> map (fn (kind, name, entry) =>
          (kind, name, #hol_term entry, #source_const entry, #serial entry,
           Position.properties_of (#reg_pos entry)))

    fun assert_registry_unchanged label earlier_ctxt later_ctxt =
      if registry_snapshot earlier_ctxt = registry_snapshot later_ctxt then ()
      else error (label ^ " changed the notation registry")

    fun assert_new_fields label ctxt expected =
      let
        val old_serials = Micro_Rust_Names.dump \<^context> |> map (#serial o #3)
        val added =
          Micro_Rust_Names.dump ctxt
          |> filter_out (fn (_, _, entry) => member (op =) old_serials (#serial entry))
        val actual =
          map (fn (kind, name, entry) =>
            (kind, name, dest_Const_name (#hol_term entry))) added
        val expected =
          map (fn (name, lens) =>
            (Micro_Rust_Names.NField, name,
             dest_Const_name
               (Proof_Context.read_const {proper = true, strict = false} ctxt lens)))
            expected
      in
        if length actual = length expected andalso
            forall (member (op =) actual) expected
        then () else error (label ^ " installed unexpected field backends")
      end

    fun rename_list entries =
      "[" ^ commas (map (fn (source, target) =>
        quote source ^ " \<rightarrow> " ^ quote target) entries) ^ "]"

    val _ =
      assert_succeeded "renamed-short-selectors"
        ("urust_datatype [renames = " ^
          rename_list [("first", "f"), ("second", "g"), ("third", "r"), ("fourth", "arg0")] ^
          "] " ^ datatype_source "ShortSelectors" "first: u32, second: bool, third: u64, fourth: u8" ^
          "\nthm short_selectors_f_lens_valid short_selectors_f_lens_view_update_modify " ^
          "short_selectors_f_update_explicit short_selectors_f_update_localI " ^
          "short_selectors_g_update_localI short_selectors_r_update_localI " ^
          "short_selectors_arg0_update_explicit\n" ^
          "lemma short_update_identity: " ^
          quote "update_f h (make_short_selectors n b m k) = make_short_selectors (h n) b m k" ^
          " by (rule short_selectors_f_update_explicit)")

    val _ =
      List.app (fn source =>
        assert_succeeded "empty-renames-shape"
          ("urust_datatype [pp_test, renames = []] " ^ cartouche source))
        ["struct EmptyRenameUnit;", "struct EmptyRenameTuple(u32);",
         "enum EmptyRenameEnum { First, Second(u32) }"]

    val _ =
      assert_succeeded "independent-renames"
        ("urust_datatype [renames = " ^ rename_list [("value", "shared")] ^ "] " ^
          datatype_source "RenameLeft" "value: u32" ^ "\n" ^
          "urust_datatype [renames = " ^ rename_list [("value", "shared")] ^ "] " ^
          datatype_source "RenameRight" "value: bool" ^ "\n" ^
          "lemma independent_lens_identities: " ^
          quote "lens_view rename_left_shared_lens = rename_left.shared" ^ " " ^
          quote "lens_view rename_right_shared_lens = rename_right.shared" ^
          " by (simp_all add: rename_left_shared_lens_view_update_modify " ^
          "rename_right_shared_lens_view_update_modify)")

    val _ =
      List.app
        (fn (label, options, binding, expected, enabled) =>
          let
            val (result, _, _) =
              capture_result true ("renames-" ^ label)
                ("urust_datatype " ^ options ^ " " ^ binding ^ " " ^
                  datatype_source "RenameFixture" "sourceValue: u32, otherValue: bool")
            val ctxt = result_context result
            val hol_name = if binding = "" then "rename_fixture" else binding
            val SOME entry = URust_Item_Scope.lookup_constructor ctxt "RenameFixture"
            val actual =
              URust_Item_Scope.constructor_fields entry
              |> map (apsnd (Long_Name.base_name o dest_Const_name))
            val _ =
              if actual = expected then ()
              else error (label ^ " changed selector identity or source field order")
            val lenses = map (apsnd (lens_name hol_name)) expected
            val _ =
              List.app (fn (_, lens) =>
                List.app (fn suffix =>
                  ignore (Proof_Context.get_thms ctxt (lens ^ suffix)))
                  ["_valid", "_view_update_modify"]) lenses
          in
            if enabled then assert_new_fields label ctxt lenses
            else assert_registry_unchanged label \<^context> ctxt
          end)
        [("default", "", "",
          [("sourceValue", "rename_fixture_source_value"),
           ("otherValue", "rename_fixture_other_value")], true),
         ("empty", "[renames = [], pp_test]", "",
          [("sourceValue", "rename_fixture_source_value"),
           ("otherValue", "rename_fixture_other_value")], true),
         ("partial", "[renames = " ^ rename_list [("sourceValue", "chosen")] ^ "]", "",
          [("sourceValue", "chosen"), ("otherValue", "rename_fixture_other_value")], true),
         ("explicit", "[pretty, pp_test, renames = " ^
           rename_list [("otherValue", "UpperCase"), ("sourceValue", "chosen")] ^
           ", register_notation, verbosity = 1]", "explicit_rename",
          [("sourceValue", "chosen"), ("otherValue", "UpperCase")], true),
         ("reordered", "[renames = " ^
           rename_list [("sourceValue", "chosen"), ("otherValue", "UpperCase")] ^
           ", pp_test]", "explicit_rename",
          [("sourceValue", "chosen"), ("otherValue", "UpperCase")], true),
         ("suppressed", "[register_notation = false, renames = " ^
           rename_list [("sourceValue", "chosen")] ^ ", pp_test, pretty, verbosity = 2]",
          "", [("sourceValue", "chosen"), ("otherValue", "rename_fixture_other_value")], false)]

    val _ =
      List.app
        (fn (label, entries, expected) =>
          let
            val ctxt =
              capture_result true ("enum-renames-" ^ label)
                ("urust_datatype [pp_test, pretty, verbosity = 1, renames = " ^
                  rename_list entries ^ "] " ^
                  cartouche "enum RenameEnumFixture { Unit, Tuple(u32, bool), Named { value: u32 } }")
              |> #1 |> result_context
            val actual =
              map (fn source =>
                URust_Item_Scope.lookup_constructor ctxt ("RenameEnumFixture::" ^ source)
                |> the |> URust_Item_Scope.constructor_term
                |> dest_Const_name |> Long_Name.base_name) ["Unit", "Tuple", "Named"]
            val _ =
              if actual = expected then ()
              else error "enum rename list changed constructor identity or argument order"
            val SOME named =
              URust_Item_Scope.lookup_constructor ctxt "RenameEnumFixture::Named"
            val _ =
              if map (apsnd (Long_Name.base_name o dest_Const_name))
                  (URust_Item_Scope.constructor_fields named) =
                  [("value", "rename_enum_fixture_named_value")]
              then () else error "enum renaming changed automatic payload selectors"
          in assert_registry_unchanged label \<^context> ctxt end)
        [("empty", [], ["Unit", "Tuple", "Named"]),
         ("partial", [("Tuple", "ModelTuple")], ["Unit", "ModelTuple", "Named"]),
         ("all", [("Named", "ModelNamed"), ("Unit", "ModelUnit"), ("Tuple", "ModelTuple")],
          ["ModelUnit", "ModelTuple", "ModelNamed"])]

    val _ =
      List.app
        (fn (label, options, item, diagnostic) =>
          assert_rejected_all ("rename-error-" ^ label) [diagnostic, label]
            ("urust_datatype [" ^ options ^ "] " ^ cartouche item))
        [("duplicate-key", "renames = " ^
            rename_list [("value", "a"), ("value", "b")],
          "struct RenameError { value: u32 }", "duplicate rename key"),
         ("unknown-field", "renames = " ^ rename_list [("missing", "a")],
          "struct RenameError { value: u32 }", "unknown rename key"),
         ("qualified-key", "renames = " ^ rename_list [("RenameError::value", "a")],
          "struct RenameError { value: u32 }", "unknown rename key"),
         ("enum-field-key", "renames = " ^ rename_list [("value", "a")],
          "enum RenameError { Named { value: u32 } }", "unknown rename key"),
         ("unknown-variant", "renames = " ^ rename_list [("Missing", "Chosen")],
          "enum RenameError { First }", "unknown rename key"),
         ("unit-struct", "renames = " ^ rename_list [("RenameError", "a")],
          "struct RenameError;", "unknown rename key"),
         ("tuple-struct", "renames = " ^ rename_list [("0", "a")],
          "struct RenameError(u32);", "unknown rename key"),
         ("duplicate-field-target", "renames = " ^
            rename_list [("value", "a"), ("other", "a")],
          "struct RenameError { value: u32, other: bool }", "duplicate generated HOL field"),
         ("default-field-target", "renames = " ^ rename_list [("value", "rename_error_other")],
          "struct RenameError { value: u32, other: bool }", "duplicate generated HOL field"),
         ("duplicate-variant-target", "renames = " ^
            rename_list [("First", "Chosen"), ("Second", "Chosen")],
          "enum RenameError { First, Second }", "duplicate generated HOL constructor"),
         ("default-variant-target", "renames = " ^ rename_list [("First", "Second")],
          "enum RenameError { First, Second }", "duplicate generated HOL constructor"),
         ("empty-target", "renames = " ^ rename_list [("value", "")],
          "struct RenameError { value: u32 }", "invalid HOL name binding"),
         ("qualified-target", "renames = " ^ rename_list [("value", "Model.field")],
          "struct RenameError { value: u32 }", "invalid HOL name binding"),
         ("space-target", "renames = " ^ rename_list [("value", "two words")],
          "struct RenameError { value: u32 }", "invalid HOL name binding"),
         ("reserved-target", "renames = " ^ rename_list [("value", "__")],
          "struct RenameError { value: u32 }", "invalid HOL name binding"),
         ("bare-option", "renames", "struct RenameError;", "expects a quoted rename list"),
         ("boolean-option", "renames = true", "struct RenameError;", "expects a quoted rename list"),
         ("integer-option", "renames = 1", "struct RenameError;", "expects a quoted rename list"),
         ("duplicate-option", "renames = [], renames = []",
          "struct RenameError;", "duplicate uRust command option"),
         ("unquoted-key", "renames = [value \<rightarrow> \"chosen\"]",
          "struct RenameError { value: u32 }", "Outer syntax error"),
         ("unquoted-target", "renames = [\"value\" \<rightarrow> chosen]",
          "struct RenameError { value: u32 }", "Outer syntax error"),
         ("equals-separator", "renames = [\"value\" = \"chosen\"]",
          "struct RenameError { value: u32 }", "Outer syntax error"),
         ("mapsto-separator", "renames = [\"value\" \<mapsto> \"chosen\"]",
          "struct RenameError { value: u32 }", "Outer syntax error"),
         ("missing-comma", "renames = [\"value\" \<rightarrow> \"a\" \"other\" \<rightarrow> \"b\"]",
          "struct RenameError { value: u32, other: bool }", "Outer syntax error"),
         ("trailing-comma", "renames = [\"value\" \<rightarrow> \"a\",]",
          "struct RenameError { value: u32 }", "Outer syntax error"),
         ("missing-close", "renames = [[\"value\" \<rightarrow> \"a\"]",
          "struct RenameError { value: u32 }", "Outer syntax error")]

    val _ =
      assert_rejected_all "rename-position-key" ["unknown rename key", "line 3"]
        ("urust_datatype [renames = [\n\"missing\" \<rightarrow> \"chosen\"]] " ^
          datatype_source "PositionRename" "value: u32")
    val _ =
      assert_rejected_all "rename-position-target" ["invalid HOL name binding", "line 3"]
        ("urust_datatype [renames = [\"value\" \<rightarrow>\n\"bad.name\"]] " ^
          datatype_source "PositionRename" "value: u32")
    val _ =
      assert_succeeded "renamed-named-construction"
        ("urust_expr _ " ^ cartouche "RenamedChoice::Ready { value: 7u32, active: true }")

    val _ =
      List.app (fn command =>
        assert_rejected ("renames-on-" ^ command)
          "unknown uRust command option \"renames\""
          (command ^ " [renames] _ " ^ cartouche "()"))
        ["urust_expr", "urust_fn"]

    val _ =
      assert_succeeded "rename-error-recovery"
        ("urust_datatype [renames = " ^ rename_list [("value", "recovered_selector")] ^
         "] " ^ datatype_source "RenameRecovery" "value: u32")

    val _ =
      List.app
        (fn level =>
          let
            val captured =
              capture_full_result true ("renamed-output-" ^ string_of_int level)
                ("urust_datatype [renames = " ^
                  rename_list [("sourceValue", "actual_selector")] ^
                  ", pp_test, pretty, verbosity = " ^ string_of_int level ^ "] output_rename " ^
                  datatype_source "OutputRename" "sourceValue: u32")
            val ctxt = result_context (#result captured)
            val _ =
              assert_new_fields "renamed pretty replay" ctxt
                [("sourceValue", "output_rename_actual_selector_lens")]
            val _ =
              if length (URust_Item_Scope.dump_types ctxt) =
                  length (URust_Item_Scope.dump_types \<^context>) + 1 andalso
                  length (URust_Item_Scope.dump_constructors ctxt) =
                  length (URust_Item_Scope.dump_constructors \<^context>) + 1
              then () else error "renamed pretty replay duplicated item registration"
            val _ =
              if level = 0 then assert_absent "quiet renamed output"
                "urust_datatype generated artifacts" (#plain captured)
              else
                (List.app (fn expected =>
                   assert_contains "renamed output" expected (#plain captured))
                   ["actual_selector", "output_rename_actual_selector_lens", "sourceValue"];
                 assert_absent "renamed output" "output_rename_source_value" (#plain captured);
                 if level = 2 then assert_contains "renamed HOL declaration"
                   "datatype_record" (#plain captured) else ())
          in () end)
        [0, 1, 2]

    val _ =
      List.app
        (fn (label, options, binding, enabled) =>
          let
            val (result, _, _) =
              capture_result true ("registration-" ^ label)
                ("urust_datatype " ^ options ^ binding ^ " " ^
                  datatype_source "OptionFixture" "freshAlias: u32,")
            val ctxt = result_context result
            val hol_name = if binding = "" then "option_fixture" else binding
            val lens = hol_name ^ "_" ^ hol_name ^ "_fresh_alias_lens"
            val _ =
              ignore (Proof_Context.get_thm ctxt (lens ^ "_valid"))
          in
            if enabled then assert_new_fields label ctxt [("freshAlias", lens)]
            else assert_registry_unchanged label \<^context> ctxt
          end)
        [("default-inferred", "", "", true),
         ("default-explicit", "", "explicit_option_fixture", true),
         ("bare-inferred", "[register_notation] ", "", true),
         ("bare-explicit", "[register_notation] ", "explicit_option_fixture", true),
         ("true-inferred", "[register_notation = true] ", "", true),
         ("true-explicit", "[register_notation = true] ", "explicit_option_fixture", true),
         ("false-inferred", "[register_notation = false] ", "", false),
         ("false-explicit", "[register_notation = false] ", "explicit_option_fixture", false),
         ("mixed-first", "[register_notation = false, pp_test, pretty, verbosity = 1] ", "", false),
         ("mixed-last", "[verbosity = 2, pretty, pp_test, register_notation] ", "", true)]

    val _ =
      List.app
        (fn enabled =>
          List.app
            (fn (label, source, fields) =>
              let
                val (result, _, _) =
                  capture_result true ("shape-" ^ label)
                    ("urust_datatype [pp_test, register_notation = " ^
                      Bool.toString enabled ^ "] option_shape " ^ cartouche source)
                val ctxt = result_context result
              in
                if enabled
                then assert_new_fields label ctxt
                  (map (fn field =>
                    (field, "option_shape_option_shape_" ^
                      URust_AST.rust_snake_case field ^ "_lens")) fields)
                else assert_registry_unchanged label \<^context> ctxt
              end)
            [("unit", "struct OptionShape;", []),
             ("tuple", "struct OptionShape(u32, bool);", []),
             ("enum", "enum OptionShape { Idle, Data(u32), Named { freshAlias: bool } }", []),
             ("named-one", "struct OptionShape { freshAlias: u32 }", ["freshAlias"]),
             ("named-fourteen",
              "struct OptionShape { " ^
                commas (map (fn n => "field" ^ string_of_int n ^ ": u32") (1 upto 14)) ^ " }",
              map (fn n => "field" ^ string_of_int n) (1 upto 14)),
             ("name-boundaries", "struct OptionShape { camelCase: u32, HTTP2Status: bool }",
              ["camelCase", "HTTP2Status"])])
        [false, true]

    val (inherited_result, _, _) =
      capture_result true "inherited-registration"
        ("urust_datatype [register_notation = false] inherited_aliases " ^
          datatype_source "InheritedAliases" "value: bool, sampleValue: u32," ^ "\n" ^
         "urust_expr _ " ^ cartouche " (ParserNumberBox { value: 1u32 }).value " ^ "\n" ^
         "urust_expr _ " ^
          cartouche " (NotationPacket { sampleValue: 1u32, HTTP2Code: true }).sampleValue ")
    val _ =
      assert_registry_unchanged "inherited and overloaded aliases"
        \<^context> (result_context inherited_result)

    val (fallback_result, _, _) =
      capture_result true "unregistered-field-fallback"
        ("urust_datatype [register_notation = false] fallback_packet " ^
          datatype_source "FallbackPacket" "fallbackAlias: u32,")
    val fallback_ctxt = result_context fallback_result
    (* An opted-out generated lens is neither registered nor a same-named constant, so the field
       name has no lens resolution rather than becoming a free variable. *)
    val _ =
      (case Exn.result (Parser_Test_Elaboration.expression fallback_ctxt)
          (Parser_Lex_Util.text_source
            "(FallbackPacket { fallbackAlias: 1u32 }).fallbackAlias") of
         Exn.Res term =>
           if Term.exists_subterm
               (fn Const (name, _) => String.isSuffix "_fallback_alias_lens" name | _ => false) term
           then error "opted-out generated lens was mistaken for an installed lens"
           else error "unregistered field name elaborated without a lens resolution"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring
               "unregistered field \"fallbackAlias\" has no fixed or HOL constant lens resolution"
               (XML.content_of (YXML.parse_body (Runtime.exn_message exn)))
           then ()
           else Exn.reraise exn)
    val (manual_result, _, _) =
      capture_result true "manual-registration"
        ("urust_datatype [register_notation = false] manual_packet " ^
          datatype_source "ManualPacket" "manualAlias: u32," ^ "\n" ^
         "urust_notation (field) manual_packet_manual_packet_manual_alias_lens (\"manualAlias\")")
    val manual_ctxt = result_context manual_result
    val _ =
      assert_new_fields "manual registration" manual_ctxt
        [("manualAlias", "manual_packet_manual_packet_manual_alias_lens")]
    val manual_term =
      Parser_Test_Elaboration.expression manual_ctxt
        (Parser_Lex_Util.text_source
          "(ManualPacket { manualAlias: 1u32 }).manualAlias")
    val manual_lens =
      dest_Const_name
        (Proof_Context.read_const {proper = true, strict = false} manual_ctxt
          "manual_packet_manual_packet_manual_alias_lens")
    val _ =
      if Term.exists_subterm
          (fn Const (name, _) => name = manual_lens | _ => false) manual_term
      then () else error "manual field registration did not resolve to the generated lens"

    val _ =
      List.app
        (fn level =>
          let
            val captured =
              capture_full_result true ("suppressed-output-" ^ string_of_int level)
                ("urust_datatype [register_notation = false, pp_test, pretty, verbosity = " ^
                  string_of_int level ^ "] suppressed_output " ^
                  datatype_source "SuppressedOutput" "outputAlias: u32,")
            val ctxt = result_context (#result captured)
            val _ = assert_registry_unchanged "pretty replay" \<^context> ctxt
          in
            if level = 0
            then assert_absent "quiet suppressed output"
              "urust_datatype generated artifacts" (#plain captured)
            else
              let
                val output = #plain captured
                val mapping_start =
                  the (substring_index "installed Rust mappings:" output)
                val after_mappings =
                  String.extract (output, mapping_start, NONE)
                val mapping_length =
                  the (substring_index "normalized uRust declaration" after_mappings)
                val mappings = String.substring (after_mappings, 0, mapping_length)
                val field_kinds = entity_kinds "outputAlias" (#body captured)
                val _ =
                  List.app (fn text => assert_contains "suppressed manifest" text output)
                    ["lenses:", "suppressed_output_suppressed_output_output_alias_lens",
                     "normalized uRust declaration"]
                val _ = assert_absent "suppressed mappings" "outputAlias" mappings
                val _ = assert_contains "retained constructor mapping" "SuppressedOutput" mappings
                val _ =
                  if member (op =) field_kinds Markup.constantN andalso
                      last_element "suppressed source field" field_kinds = "urust_field"
                  then () else error "suppressed registration lost source-field navigation"
              in
                if level = 2
                then assert_contains "suppressed lens definitions" "definition" output
                else assert_absent "compact suppressed output" "normalized generated declaration" output
              end
          end)
        [0, 1, 2]

    val _ =
      List.app
        (fn (label, options, diagnostic) =>
          assert_rejected_all ("registration-error-" ^ label)
            [diagnostic, "registration-error-" ^ label]
            ("urust_datatype [" ^ options ^ "] option_error " ^
              datatype_source "OptionError" "errorAlias: u32,"))
        [("duplicate", "register_notation, register_notation = false",
          "duplicate uRust command option \"register_notation\""),
         ("integer", "register_notation = 1", "expects true or false"),
         ("attributes", "register_notation = []", "expects true or false"),
         ("invalid", "register_notation = perhaps", "Outer syntax error"),
         ("missing-value", "register_notation =", "Outer syntax error"),
         ("missing-comma", "register_notation pretty", "Outer syntax error"),
         ("prefixed", "urust_register_notation = false",
          "unknown uRust command option \"urust_register_notation\"")]
    val _ =
      List.app
        (fn command =>
          assert_rejected ("registration-on-" ^ command)
            "unknown uRust command option \"register_notation\""
            (command ^ " [register_notation] option_wrong_command " ^ cartouche " () "))
        ["urust_expr"]

    val (function_option_result, _, _) =
      capture_result true "registration-on-urust-fn"
        ("urust_fn [register_notation = false] option_function " ^
          cartouche "fn OptionFunction() -> () { () }")
    val function_option_ctxt =
      (case function_option_result of
         Exn.Res state => Toplevel.context_of state
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      if can (Proof_Context.get_thm function_option_ctxt) "option_function_def"
      then ()
      else error "function registration option lost the definition"
    val _ =
      if is_none (Parser_Test_Calls.lookup function_option_ctxt "OptionFunction")
      then ()
      else error "disabled function registration installed a callable entry"

    fun assert_datatype_atomic options label prefix source diagnostic =
      let
        val (prefix_result, _, _) = capture_result true label prefix
        val before_state =
          (case prefix_result of Exn.Res state => state | Exn.Exn exn => Exn.reraise exn)
        val earlier_ctxt = Toplevel.context_of before_state
        val thy = Toplevel.theory_of before_state
        val [transition] =
          Outer_Syntax.parse_text thy (K thy) (Position.line_file 1 label)
            ("urust_datatype " ^ options ^ " atomic_packet " ^
              cartouche source)
        val _ =
          (case Exn.result (Toplevel.command_exception true transition) before_state of
             Exn.Res _ => error (label ^ " unexpectedly succeeded")
           | Exn.Exn exn =>
               assert_contains label diagnostic (Runtime.exn_message exn))
        val later_ctxt = Toplevel.context_of before_state
        val _ = assert_registry_unchanged label earlier_ctxt later_ctxt
        val NONE = URust_Item_Scope.lookup_type later_ctxt "AtomicPacket"
        val NONE = URust_Item_Scope.lookup_constructor later_ctxt "AtomicPacket"
        val NONE = URust_Type_Mappings.lookup later_ctxt "AtomicPacket"
        val NONE =
          Ctr_Sugar.ctr_sugar_of later_ctxt
            (Long_Name.qualify (Context.theory_name {long = false} thy) "atomic_packet")
        val [recovery] =
          Outer_Syntax.parse_text thy (K thy) (Position.line_file 1 label)
            ("urust_datatype [register_notation = false] atomic_packet " ^
              datatype_source "AtomicRecovery" "atomicAlias: u32,")
        val recovered = Toplevel.command_exception true recovery before_state |> Toplevel.context_of
      in assert_registry_unchanged (label ^ " recovery") earlier_ctxt recovered end

    val assert_registration_atomic =
      assert_datatype_atomic "[register_notation = false, verbosity = 2]"

    val _ =
      List.app
        (fn (label, entries, prefix, source, diagnostic) =>
          assert_datatype_atomic
            ("[renames = " ^ rename_list entries ^
              ", register_notation = false, pp_test, pretty, verbosity = 2]")
            label prefix source diagnostic)
        [("renamed-unknown-atomic", [("missing", "chosen")], "",
          "struct AtomicPacket { atomicAlias: u32 }", "unknown rename key"),
         ("renamed-collision-atomic", [("atomicAlias", "atomic_packet_other")], "",
          "struct AtomicPacket { atomicAlias: u32, other: bool }", "duplicate generated HOL field"),
         ("renamed-ownership-atomic", [("First", "AtomicChosen")],
          "urust_notation (literal) True (\"AtomicPacket::First\")",
          "enum AtomicPacket { First }", "conflicts with an existing micro_rust_notation")]

    val _ =
      List.app
        (fn (label, source, diagnostic) =>
          assert_registration_atomic label "" source diagnostic)
        [("suppressed-duplicate", "struct AtomicPacket { atomicAlias: u32, atomicAlias: bool }",
          "duplicate field"),
         ("suppressed-collision", "struct AtomicPacket { fooBar: u32, foo_bar: bool }",
          "duplicate generated HOL field"),
         ("suppressed-arity", "struct AtomicPacket { " ^
          commas (map (fn n => "f" ^ string_of_int n ^ ": u32") (1 upto 15)) ^ " }",
          "at most 14"),
         ("suppressed-tuple-arity", "struct AtomicPacket(" ^
          commas (replicate 15 "u32") ^ ");", "at most 14"),
         ("suppressed-duplicate-variant", "enum AtomicPacket { Repeated, Repeated }",
          "duplicate variant"),
         ("suppressed-variant-collision",
          "enum AtomicPacket { FooBar { value: u32 }, Foo_Bar { value: bool } }",
          "duplicate generated HOL selector"),
         ("suppressed-named-variant-arity", "enum AtomicPacket { Named { " ^
          commas (map (fn n => "f" ^ string_of_int n ^ ": u32") (1 upto 15)) ^ " } }",
          "at most 14"),
         ("suppressed-tuple-variant-arity", "enum AtomicPacket { Tuple(" ^
          commas (replicate 15 "u32") ^ ") }", "at most 14")]
    val _ =
      assert_registration_atomic "suppressed-late-conflict"
        "urust_notation (literal) True (\"AtomicPacket\")"
        "struct AtomicPacket { atomicAlias: u32 }"
        "conflicts with an existing micro_rust_notation"
    val _ =
      assert_succeeded "registration-diagnostic-recovery"
        ("urust_datatype [register_notation] " ^
          datatype_source "RegistrationRecovery" "recoveryAlias: u32,")

    val (_, _, quiet) =
      capture_result true "quiet"
        ("urust_datatype [verbosity = 0] output_quiet " ^
          datatype_source "OutputQuiet" "value: u32,")
    val _ =
      assert_absent "verbosity 0"
        "urust_datatype generated artifacts" quiet

    val (_, manifest_body, manifest) =
      capture_result true "manifest"
        ("urust_datatype [verbosity = 1] output_manifest " ^
          datatype_source "OutputManifest"
            "first: u32, second: bool,")
    val _ =
      List.app
        (fn expected =>
          assert_contains "verbosity 1" expected manifest)
        ["urust_datatype generated artifacts",
         "OutputManifest", "output_manifest",
         "make_output_manifest",
         "output_manifest_first", "output_manifest_second",
         "output_manifest_output_manifest_first_lens",
         "output_manifest_output_manifest_second_lens",
         "installed Rust mappings"]
    val _ =
      List.app
        (fn unexpected =>
          assert_absent "verbosity 1" unexpected manifest)
        ["normalized uRust declaration",
         "normalized generated declaration", "definition"]
    val _ =
      (case
          (substring_index "output_manifest_first" manifest,
           substring_index "output_manifest_second" manifest) of
         (SOME first, SOME second) =>
           if first < second then ()
           else error "verbosity 1 field order changed"
       | _ => error "verbosity 1 field names are missing")
    val _ =
      if exists (tree_has_markup Markup.entityN) manifest_body
      then ()
      else error "verbosity 1 output lacks PIDE entity markup"

    val (_, _, detailed) =
      capture_result true "detailed"
        ("urust_datatype [verbosity = 2] output_detailed " ^
          datatype_source "OutputDetailed" "value: u32,")
    val _ =
      List.app
        (fn expected =>
          assert_contains "verbosity 2" expected detailed)
        ["urust_datatype generated artifacts",
         "normalized generated declaration",
         "datatype_record", "definition",
         "output_detailed_output_detailed_value_lens",
         "\<equiv>"]
    val _ =
      List.app
        (fn internal =>
          assert_absent "verbosity 2" internal detailed)
        ["_induct", ".inject", ".distinct", ".case"]

    val enum_source =
      cartouche
        (" enum OutputEnum { " ^
         "First, Second(u32,), " ^
         "Third { left: u32, right: bool, }, } ")
    val (_, _, enum_manifest) =
      capture_result true "enum-manifest"
        ("urust_datatype [backend = hol, verbosity = 1] output_enum " ^
          enum_source)
    val _ =
      List.app
        (fn expected =>
          assert_contains "enum verbosity 1"
            expected enum_manifest)
        ["OutputEnum", "output_enum",
         "OutputEnum::First", "OutputEnum::Second",
         "OutputEnum::Third",
         "OutputEnum::Third.left",
         "OutputEnum::Third.right",
         "installed Rust mappings"]
    val _ =
      List.app
        (fn unexpected =>
          assert_absent "enum verbosity 1"
            unexpected enum_manifest)
        ["normalized generated declaration", "lenses:"]
    val _ =
      (case
          (substring_index "OutputEnum::First" enum_manifest,
           substring_index "OutputEnum::Second" enum_manifest,
           substring_index "OutputEnum::Third" enum_manifest,
           substring_index "OutputEnum::Third.left" enum_manifest,
           substring_index "OutputEnum::Third.right" enum_manifest) of
         (SOME first, SOME second, SOME third,
          SOME left, SOME right) =>
           if first < second andalso
              second < third andalso
              third < left andalso
              left < right
           then ()
           else error "enum verbosity 1 source order changed"
       | _ => error "enum verbosity 1 manifest is incomplete")

    val (_, _, enum_detailed) =
      capture_result true "enum-detailed"
        ("urust_datatype [backend = hol, verbosity = 2] output_enum_detailed " ^
          cartouche
            (" enum OutputEnumDetailed { " ^
             "Empty, Named { value: u32, }, } "))
    val _ =
      List.app
        (fn expected =>
          assert_contains "enum verbosity 2"
            expected enum_detailed)
        ["normalized generated declaration",
         "datatype", "OutputEnumDetailed::Empty",
         "OutputEnumDetailed::Named",
         "output_enum_detailed_named_value",
         "definition", "case"]
    val _ =
      List.app
        (fn internal =>
          assert_absent "enum verbosity 2"
            internal enum_detailed)
        ["_induct", ".inject", ".distinct", ".case",
         "_lens"]

    val (_, _, scoped) =
      capture_result true "scoped"
        ("declare [[urust_verbosity = 1]]\n" ^
         "urust_datatype " ^
           datatype_source "ScopedOutput" "value: u32,")
    val _ =
      assert_contains "scoped verbosity"
        "urust_datatype generated artifacts" scoped

    val _ =
      assert_succeeded "inline-pp-test"
        ("urust_datatype [pp_test] inline_pp_test " ^
          datatype_source "InlinePpTest" "value: u32,")
    val _ =
      assert_succeeded "scoped-pp-test"
        ("declare [[urust_pp_test = true]]\n" ^
         "urust_datatype scoped_pp_test " ^
          datatype_source "ScopedPpTest" "value: bool,")
    val _ =
      assert_succeeded "scoped-pp-false-override"
        ("declare [[urust_pp_test = true]]\n" ^
         "urust_datatype [pp_test = false] scoped_pp_false " ^
          datatype_source "ScopedPpFalse" "value: u64,")

    val pretty_replay =
      capture_full_result true "pretty-replay"
        ("urust_datatype [pretty, verbosity = 1] pretty_replay " ^
          cartouche
            (" enum PrettyReplay { Empty, " ^
             "Named { value: u32, raw: " ^
             type_cartouche "nat option" ^ ", }, } "))
    val pretty_replay_state =
      (case #result pretty_replay of
         Exn.Res state => state
       | Exn.Exn exn => Exn.reraise exn)
    val pretty_replay_ctxt =
      Toplevel.context_of pretty_replay_state
    val _ =
      List.app
        (fn expected =>
          assert_contains "pretty datatype output" expected
            (#plain pretty_replay))
        ["urust_datatype generated artifacts",
         "normalized uRust declaration",
         "enum PrettyReplay {",
         "Named {",
         "value: u32",
         "raw: " ^ type_cartouche "nat option"]
    val _ =
      assert_absent "verbosity 1 pretty datatype"
        "normalized generated declaration"
        (#plain pretty_replay)
    val type_kinds =
      entity_kinds "PrettyReplay" (#body pretty_replay)
    val constructor_kinds =
      entity_kinds "Named" (#body pretty_replay)
    val field_kinds =
      entity_kinds "value" (#body pretty_replay)
    val _ =
      if member (op =) type_kinds Markup.type_nameN andalso
          last_element "pretty datatype type" type_kinds =
            "urust_item"
      then ()
      else
        error
          ("pretty datatype type target order changed: " ^
            commas_quote type_kinds)
    val _ =
      if member (op =) constructor_kinds Markup.constantN andalso
          last_element "pretty datatype constructor"
            constructor_kinds = "urust_constructor"
      then ()
      else
        error
          ("pretty datatype constructor target order changed: " ^
            commas_quote constructor_kinds)
    val _ =
      if member (op =) field_kinds Markup.constantN andalso
          last_element "pretty datatype field" field_kinds =
            "urust_field"
      then ()
      else
        error
          ("pretty datatype field target order changed: " ^
            commas_quote field_kinds)
    val _ =
      if exists
          (fn tree =>
            tree_has_markup Markup.keyword1N tree)
          (#body pretty_replay)
      then ()
      else error "pretty datatype output lost lexical keyword markup"
    val _ =
      if not
          (null
            (maps
              (wrapped_markup_properties
                Markup.tconstN "nat")
              (#body pretty_replay)))
      then ()
      else error "pretty datatype output lost embedded HOL type markup"
    val replay_probe_item =
      (case
          URust_Parser.parse_datatype_source \<^context>
            (Parser_Lex_Util.text_source
              "struct PrettyReplayProbe;") of
         SOME item => item
       | NONE => error "datatype replay probe parsed as empty input")
    val replay_probe_reports =
      Synchronized.var
        "urust_datatype_replay_probe_reports"
        ([]: string list)
    val replay_probe_called =
      Unsynchronized.ref false
    val replay_external_start =
      Position.make0 1 1 0 "" ""
        "urust-datatype-pretty-replay-external"
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn
          (fn chunks =>
            Synchronized.change replay_probe_reports
              (append chunks))
          (fn () =>
            ignore
              (URust_Printer_Output.pretty_human_datatype_with_reparse
                (fn source =>
                  (replay_probe_called := true;
                   ignore
                     (URust_Parser.parse_datatype_source
                       \<^context> source);
                   Position.report replay_external_start
                     Markup.keyword1))
                replay_probe_item)) ())
    val _ =
      if ! replay_probe_called then ()
      else error "datatype pretty replay callback was not invoked"
    val _ =
      if null (Synchronized.value replay_probe_reports) then ()
      else
        error
          "datatype pretty replay forwarded synthetic or unrelated reports"
    val pretty_types =
      URust_Item_Scope.dump_types pretty_replay_ctxt
      |> filter
          (fn entry =>
            URust_Item_Scope.type_rust_name entry =
              "PrettyReplay")
    val pretty_constructors =
      URust_Item_Scope.dump_constructors pretty_replay_ctxt
      |> filter
          (fn entry =>
            String.isPrefix "PrettyReplay"
              (URust_Item_Scope.constructor_rust_path entry))
    val _ =
      if length pretty_types = 1 andalso
          length pretty_constructors = 2
      then ()
      else
        error
          "pretty datatype replay generated or registered artifacts more than once"

    val (_, _, pretty_detailed) =
      capture_result true "pretty-detailed"
        ("urust_datatype [pretty, verbosity = 2] pretty_detailed " ^
          datatype_source "PrettyDetailed" "value: u32,")
    val _ =
      List.app
        (fn expected =>
          assert_contains "verbosity 2 pretty datatype"
            expected pretty_detailed)
        ["urust_datatype generated artifacts",
         "normalized uRust declaration",
         "struct PrettyDetailed",
         "normalized generated declaration",
         "datatype_record", "definition"]
    val _ =
      (case
          (substring_index
             "normalized uRust declaration" pretty_detailed,
           substring_index
             "normalized generated declaration" pretty_detailed) of
         (SOME human, SOME generated) =>
           if human < generated then ()
           else
             error
               "human datatype declaration no longer precedes generated HOL details"
       | _ =>
           error "verbosity 2 pretty datatype output is incomplete")

    val (_, _, scoped_pretty) =
      capture_result true "scoped-pretty"
        ("declare [[urust_pretty = true, urust_verbosity = 1]]\n" ^
         "urust_datatype scoped_pretty_datatype " ^
          datatype_source "ScopedPrettyDatatype" "value: u32,")
    val _ =
      assert_contains "scoped datatype pretty"
        "normalized uRust declaration" scoped_pretty
    val (_, _, pretty_false) =
      capture_result true "pretty-false"
        ("declare [[urust_pretty = true, urust_verbosity = 1]]\n" ^
         "urust_datatype [pretty = false] pretty_false_datatype " ^
          datatype_source "PrettyFalseDatatype" "value: u32,")
    val _ =
      assert_absent "datatype pretty false override"
        "normalized uRust declaration" pretty_false
    val (pretty_quiet_result, pretty_quiet_warning) =
      capture_warning "pretty-quiet"
        ("urust_datatype [pretty, verbosity = 0] pretty_quiet " ^
          cartouche " struct PrettyQuiet; ")
    val _ =
      (case pretty_quiet_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      assert_contains "datatype pretty verbosity warning"
        "uRust command option \"pretty\" has no effect when verbosity = 0"
        pretty_quiet_warning

    val (_, _, inferred) =
      capture_result true "inferred"
        ("urust_datatype [verbosity = 1] " ^
          cartouche " struct InferredOutput; ")
    val (_, _, explicit) =
      capture_result true "explicit"
        ("urust_datatype [verbosity = 1] explicit_output " ^
          cartouche " struct ExplicitOutput; ")
    val _ =
      List.app
        (fn output =>
          assert_contains "binding-independent verbosity"
            "urust_datatype generated artifacts" output)
        [inferred, explicit]

    val (_, _, inline_override) =
      capture_result true "inline-override"
        ("declare [[urust_verbosity = 2]]\n" ^
         "urust_datatype [verbosity = 0] inline_override " ^
          cartouche " struct InlineOverride; ")
    val _ =
      assert_absent "inline verbosity override"
        "urust_datatype generated artifacts" inline_override

    val (_, _, interactive_gated) =
      capture_result false "interactive-gated"
        ("declare [[show_results = true]]\n" ^
         "urust_datatype [verbosity = 2] interactive_gated " ^
          cartouche " struct InteractiveGated; ")
    val _ =
      assert_contains "noninteractive with show_results"
        "urust_datatype generated artifacts"
        interactive_gated

    val (_, _, show_results_gated) =
      capture_result true "show-results-gated"
        ("declare [[show_results = false]]\n" ^
         "urust_datatype [verbosity = 2] show_results_gated " ^
          cartouche " struct ShowResultsGated; ")
    val _ =
      assert_contains "interactive with show_results disabled"
        "urust_datatype generated artifacts"
        show_results_gated

    val (_, _, fully_gated) =
      capture_result false "fully-gated"
        ("declare [[show_results = false]]\n" ^
         "urust_datatype [verbosity = 2] fully_gated " ^
          cartouche " struct FullyGated; ")
    val _ =
      assert_absent "combined interactive/show_results gate"
        "urust_datatype generated artifacts" fully_gated

    val (failed_result, _, failed_output) =
      capture_result true "failed-output"
        ("urust_datatype [verbosity = 2] failed_output " ^
          datatype_source "FailedOutput"
            "value: u32, value: bool,")
    val _ =
      (case failed_result of
         Exn.Res _ => error "failed declaration unexpectedly succeeded"
       | Exn.Exn _ => ())
    val _ =
      assert_absent "failed declaration"
        "urust_datatype generated artifacts" failed_output

    val (late_failed_result, _, late_failed_output) =
      capture_result true "late-failed-output"
        ("urust_notation (literal) True (\"LateOwnedEnum\")\n" ^
         "urust_datatype [verbosity = 2] late_owned_enum " ^
          cartouche
            " enum LateOwnedEnum { Ready, } ")
    val _ =
      (case late_failed_result of
         Exn.Res _ =>
           error "late registration-conflict declaration unexpectedly succeeded"
       | Exn.Exn exn =>
           if String.isSubstring
               "conflicts with an existing micro_rust_notation"
               (Runtime.exn_message exn)
           then ()
           else Exn.reraise exn)
    val _ =
      assert_absent "late failed declaration"
        "urust_datatype generated artifacts"
        late_failed_output

    val _ =
      assert_rejected "struct-inside-urust-expr"
        "uRust struct declarations are not expressions; use urust_datatype"
        ("urust_expr struct_inside_expr " ^
          cartouche " struct LocalStruct; ")
    val _ =
      assert_rejected "enum-inside-urust-expr"
        "uRust enum declarations are not expressions; use urust_datatype"
        ("urust_expr enum_inside_expr " ^
          cartouche " enum LocalEnum { Empty, } ")
    val _ =
      assert_rejected "struct-inside-urust-fn"
        "uRust struct declarations are not expressions; use urust_datatype"
        ("urust_fn struct_inside_fn " ^
          cartouche "fn struct_inside_fn() -> () { struct LocalStruct; }")
    val _ =
      assert_rejected "enum-inside-urust-fn"
        "uRust enum declarations are not expressions; use urust_datatype"
        ("urust_fn enum_inside_fn " ^
          cartouche "fn enum_inside_fn() -> () { enum LocalEnum { Empty, } }")
    val _ =
      assert_rejected "nested-struct-inside-urust-expr"
        "uRust struct declarations are not expressions; use urust_datatype"
        ("urust_expr nested_struct_inside_expr " ^
          cartouche
            " if true { struct NestedStruct; } else { () } ")
    val _ =
      assert_rejected "nested-enum-inside-urust-fn"
        "uRust enum declarations are not expressions; use urust_datatype"
        ("urust_fn nested_enum_inside_fn " ^ cartouche
          "fn NestedEnumInsideFn() -> () { { enum NestedEnum { Ready, } } }")

    val _ =
      assert_rejected "underscore-binding"
        "_ is not a datatype naming placeholder"
        ("urust_datatype _ " ^
          cartouche " struct Placeholder; ")
    val _ =
      assert_rejected "underscore-item-name"
        "item name `_` is not supported"
        ("urust_datatype " ^
          cartouche " struct _; ")
    val _ =
      assert_rejected "underscore-field-name"
        "field name `_` is not supported"
        ("urust_datatype underscore_field_name " ^
          datatype_source "UnderscoreFieldName"
            "_: u32,")
    val _ =
      assert_rejected "underscore-variant-name"
        "variant name `_` is not supported"
        ("urust_datatype underscore_variant_name " ^
          cartouche
            " enum UnderscoreVariantName { _, } ")
    val _ =
      assert_rejected "recursive-type" "Undefined type"
        ("urust_datatype recursive_type " ^
          datatype_source "RecursiveType"
            ("next: " ^ type_cartouche "recursive_type" ^ ","))
    val _ =
      assert_rejected "malformed-type" "Inner syntax error"
        ("urust_datatype malformed_type " ^
          datatype_source "MalformedType"
            ("value: " ^ type_cartouche "nat =>" ^ ","))
    val _ =
      assert_rejected "empty-hol-type" "Inner syntax error"
        ("urust_datatype empty_hol_type " ^
          datatype_source "EmptyHolType"
            ("value: " ^ type_cartouche "" ^ ","))
    val _ =
      assert_rejected "polymorphic-field-type"
        "unrelated HOL variable in datatype field"
        ("urust_datatype polymorphic_field_type " ^
          cartouche
            (" struct PolymorphicFieldType(" ^
             type_cartouche "'a" ^ "); "))
    val _ =
      assert_rejected "unprefixed-type-cartouche"
        "HOL type cartouches must use the \<tau> prefix"
        ("urust_datatype unprefixed_type " ^
          datatype_source "UnprefixedType"
            ("value: " ^ cartouche "nat option" ^ ","))
    val _ =
      assert_rejected "separated-type-prefix"
        "unexpected input"
        ("urust_datatype separated_type_prefix " ^
          datatype_source "SeparatedTypePrefix"
            ("value: \<tau> " ^ cartouche "nat option" ^ ","))
    val _ =
      assert_rejected "unsupported-bare-type"
        "unknown Rust type \"CustomType\""
        ("urust_datatype unsupported_bare_type " ^
          datatype_source "UnsupportedBareType"
            "value: CustomType,")
    val _ =
      assert_rejected "unsupported-u128"
        "unknown Rust type \"u128\""
        ("urust_datatype unsupported_u128 " ^
          datatype_source "UnsupportedU128"
            "value: u128,")
    val _ =
      assert_rejected "unsupported-rust-tuple-type"
        "singleton tuple types is not supported"
        ("urust_datatype unsupported_rust_tuple " ^
          datatype_source "UnsupportedRustTuple"
            "value: (u32,),")
    val _ =
      assert_rejected "zero-length-rust-array-type"
        "does not satisfy sort"
        ("urust_datatype unsupported_rust_array " ^
          datatype_source "UnsupportedRustArray"
            "value: [u8; 0],")
    val _ =
      assert_rejected "unsupported-rust-reference-type"
        "Rust reference types is not supported"
        ("urust_datatype unsupported_rust_reference " ^
          datatype_source "UnsupportedRustReference"
            "value: &u32,")
    val _ =
      assert_rejected "duplicate-field" "duplicate field"
        ("urust_datatype duplicate_field " ^
          datatype_source "DuplicateField"
            "value: u32, value: bool,")
    val _ =
      assert_rejected "duplicate-variant-field"
        "duplicate field"
        ("urust_datatype duplicate_variant_field " ^
          cartouche
            (" enum DuplicateVariantField { " ^
             "Named { value: u32, value: bool, }, } "))
    val _ =
      assert_rejected "generated-field-name-collision"
        "duplicate generated HOL field \"generated_field_collision_foo_bar\""
        ("urust_datatype generated_field_collision " ^
          datatype_source "GeneratedFieldCollision"
            "fooBar: u32, foo_bar: bool,")
    val _ =
      assert_rejected "generated-selector-name-collision"
        "duplicate generated HOL selector \"generated_selector_collision_foo_bar_value\""
        ("urust_datatype generated_selector_collision " ^
          cartouche
            (" enum GeneratedSelectorCollision { " ^
             "FooBar { value: u32, }, " ^
             "Foo_Bar { value: bool, }, } "))
    val _ =
      assert_rejected "duplicate-variant" "duplicate variant"
        ("urust_datatype duplicate_variant " ^
          cartouche
            " enum DuplicateVariant { Same, Same, } ")
    val _ =
      assert_succeeded "empty-struct"
        ("urust_datatype empty_struct " ^
          cartouche " struct EmptyStruct {} ")
    val _ =
      assert_succeeded "empty-tuple-struct"
        ("urust_datatype empty_tuple " ^
          cartouche " struct EmptyTuple(); ")
    val _ =
      assert_rejected "empty-enum" "syntax error"
        ("urust_datatype empty_enum " ^
          cartouche " enum EmptyEnum {} ")
    val _ =
      assert_rejected "empty-source" "syntax error"
        ("urust_datatype empty_source " ^ cartouche "")
    val _ =
      assert_rejected "trailing-item"
        "syntax error found at struct"
        ("urust_datatype trailing_item " ^
          cartouche " struct First; struct Second; ")
    val _ =
      assert_rejected "unit-struct-missing-semicolon"
        "syntax error"
        ("urust_datatype unit_missing_semicolon " ^
          cartouche " struct UnitMissingSemicolon ")
    val _ =
      assert_rejected "tuple-struct-missing-semicolon"
        "syntax error"
        ("urust_datatype tuple_missing_semicolon " ^
          cartouche " struct TupleMissingSemicolon(u32) ")
    val _ =
      assert_rejected "named-struct-extra-semicolon"
        "syntax error found at ;"
        ("urust_datatype named_extra_semicolon " ^
          cartouche
            " struct NamedExtraSemicolon { value: u32, }; ")
    val _ =
      assert_rejected "enum-extra-semicolon"
        "syntax error found at ;"
        ("urust_datatype enum_extra_semicolon " ^
          cartouche
            " enum EnumExtraSemicolon { Ready, }; ")
    val _ =
      assert_rejected "missing-field-comma"
        "syntax error"
        ("urust_datatype missing_field_comma " ^
          cartouche
            (" struct MissingFieldComma { " ^
             "first: u32 second: bool, } "))
    val _ =
      assert_rejected "missing-variant-comma"
        "syntax error"
        ("urust_datatype missing_variant_comma " ^
          cartouche
            " enum MissingVariantComma { First Second, } ")
    val _ =
      assert_rejected "missing-tuple-type-comma"
        "syntax error"
        ("urust_datatype missing_tuple_type_comma " ^
          cartouche
            " struct MissingTupleTypeComma(u32 bool); ")

    val excessive_fields =
      1 upto 15
      |> map (fn index => "f" ^ string_of_int index ^ ": u32")
      |> commas
    val _ =
      assert_rejected "excess-arity" "at most 14"
        ("urust_datatype excess_arity " ^
          datatype_source "ExcessArity"
            (excessive_fields ^ ","))
    val excessive_types =
      replicate 15 "u32"
      |> commas
    val _ =
      assert_rejected "tuple-struct-excess-arity"
        "at most 14"
        ("urust_datatype tuple_excess_arity " ^
          cartouche
            (" struct TupleExcessArity(" ^
             excessive_types ^ "); "))
    val _ =
      assert_rejected "tuple-variant-excess-arity"
        "at most 14"
        ("urust_datatype tuple_variant_excess_arity " ^
          cartouche
            (" enum TupleVariantExcessArity { " ^
             "TooLarge(" ^ excessive_types ^ "), } "))
    val _ =
      assert_rejected "named-variant-excess-arity"
        "at most 14"
        ("urust_datatype named_variant_excess_arity " ^
          cartouche
            (" enum NamedVariantExcessArity { " ^
             "TooLarge { " ^ excessive_fields ^ ", }, } "))

    val _ =
      assert_item_parser_rejected
        "unterminated-hol-type"
        "unterminated \<tau>-prefixed HOL type cartouche"
        (" struct UnterminatedHolType { value: " ^
          "\<tau>" ^ Symbol.open_ ^ "nat option")
    val _ =
      assert_item_parser_succeeded
        "after-unterminated-hol-type"
        " struct RecoveredAfterHolType; "
    val _ =
      assert_item_parser_rejected
        "unterminated-block-comment"
        "unterminated block comment"
        " struct UnterminatedComment /* outer /* inner */ "
    val _ =
      assert_item_parser_succeeded
        "after-unterminated-block-comment"
        (" /* outer /* inner */ recovered */ " ^
          "struct RecoveredAfterComment; ")

    val _ =
      assert_rejected "unsupported-conformance-option"
        "unknown uRust command option \"conformance\""
        ("urust_datatype [conformance] unsupported_option " ^
          cartouche " struct UnsupportedOption; ")
    val _ =
      assert_rejected "unsupported-attributes-option"
        "unknown uRust command option \"attrs\""
        ("urust_datatype [attrs = []] unsupported_attrs " ^
          cartouche " struct UnsupportedAttrs; ")
    val _ =
      assert_rejected "invalid-inline-pp-test"
        "expects true or false"
        ("urust_datatype [pp_test = 1] invalid_pp_test " ^
          cartouche " struct InvalidPpTest; ")
    val _ =
      assert_rejected "invalid-inline-pretty"
        "expects true or false"
        ("urust_datatype [pretty = 1] invalid_pretty " ^
          cartouche " struct InvalidPretty; ")
    val _ =
      assert_rejected "duplicate-inline-pp-test"
        "duplicate uRust command option \"pp_test\""
        ("urust_datatype [pp_test, pp_test = false] " ^
          "duplicate_pp_test " ^
          cartouche " struct DuplicatePpTest; ")
    val _ =
      assert_rejected "duplicate-inline-pretty"
        "duplicate uRust command option \"pretty\""
        ("urust_datatype [pretty, pretty = false] " ^
          "duplicate_pretty " ^
          cartouche " struct DuplicatePretty; ")
    val _ =
      assert_rejected "invalid-inline-verbosity"
        "must be 0, 1, or 2, but found 3"
        ("urust_datatype [verbosity = 3] invalid_verbosity " ^
          cartouche " struct InvalidVerbosity; ")
    val _ =
      assert_rejected "missing-inline-verbosity"
        "expects an integer from 0 to 2"
        ("urust_datatype [verbosity] missing_verbosity " ^
          cartouche " struct MissingVerbosity; ")
    val _ =
      assert_rejected "wrong-inline-verbosity-type"
        "expects an integer from 0 to 2"
        ("urust_datatype [verbosity = true] wrong_verbosity " ^
          cartouche " struct WrongVerbosity; ")
    val _ =
      assert_rejected "duplicate-inline-verbosity"
        "duplicate uRust command option \"verbosity\""
        ("urust_datatype [verbosity = 0, verbosity = 1] " ^
          "duplicate_verbosity " ^
          cartouche " struct DuplicateVerbosity; ")
    val _ =
      assert_rejected "invalid-scoped-datatype-verbosity"
        "must be 0, 1, or 2, but found 3"
        ("declare [[urust_verbosity = 3]]\n" ^
         "urust_datatype invalid_scoped_datatype_verbosity " ^
          cartouche " struct InvalidScopedDatatypeVerbosity; ")

    val _ =
      assert_rejected "inferred-collision" "Duplicate type"
        ("urust_datatype " ^
           cartouche " struct HTTPServer; " ^ "\n" ^
         "urust_datatype " ^
           cartouche " struct HttpServer; ")
    val _ =
      assert_rejected "item-conflict"
        "conflicting active mappings for \"ConflictItem\""
        ("urust_datatype conflict_first " ^
           cartouche " struct ConflictItem; " ^ "\n" ^
         "urust_datatype conflict_second " ^
           cartouche " struct ConflictItem; ")
    val _ =
      assert_rejected "explicit-hol-binding-collision"
        "Duplicate type"
        ("urust_datatype shared_hol_binding " ^
           cartouche " struct FirstRustIdentity; " ^ "\n" ^
         "urust_datatype shared_hol_binding " ^
           cartouche " struct SecondRustIdentity; ")
    val _ =
      assert_rejected "notation-before-item"
        "conflicts with an existing micro_rust_notation"
        ("urust_notation (literal) True (\"NotationOwned\")\n" ^
         "urust_datatype notation_owned " ^
           cartouche " struct NotationOwned; ")
    val _ =
      assert_rejected "call-notation-before-item"
        "conflicts with an existing micro_rust_notation"
        ("urust_notation (call) " ^
           cartouche "lift_fun1 (\<lambda>x::unit. x)" ^
           " (\"CallNotationOwned\")\n" ^
         "urust_datatype call_notation_owned " ^
           cartouche " struct CallNotationOwned; ")
    val _ =
      assert_rejected "notation-before-enum-type"
        "conflicts with an existing micro_rust_notation"
        ("urust_notation (literal) True (\"NotationOwnedEnum\")\n" ^
         "urust_datatype notation_owned_enum " ^
           cartouche
             " enum NotationOwnedEnum { Ready, } ")
    val _ =
      assert_rejected "notation-before-enum-variant"
        "conflicts with an existing micro_rust_notation"
        ("urust_notation (literal) True " ^
           "(\"VariantNotationOwned::Ready\")\n" ^
         "urust_datatype variant_notation_owned " ^
           cartouche
             " enum VariantNotationOwned { Ready, } ")
    val _ =
      assert_rejected "notation-after-item"
        "already owned by urust_datatype"
        ("urust_datatype item_owned " ^
           cartouche " struct ItemOwned; " ^ "\n" ^
         "urust_notation (literal) True (\"ItemOwned\")")
    val _ =
      assert_rejected "call-notation-after-item"
        "already owned by urust_datatype"
        ("urust_datatype call_item_owned " ^
           cartouche " struct CallItemOwned(u32); " ^ "\n" ^
         "urust_notation (call) " ^
           cartouche "lift_fun1 (\<lambda>x::unit. x)" ^
           " (\"CallItemOwned\")")

    val _ =
      assert_succeeded "named-variant-construction"
        ("urust_expr _ " ^
          cartouche
            " ParserMessage::Named { code: 1u32, payload: \<llangle>[] :: 8 word list\<rrangle>, } ")
    val _ =
      assert_rejected "tuple-struct-as-bare-value"
        "requires positional call syntax"
        ("urust_expr _ " ^
          cartouche " ParserTuple ")
    val _ =
      assert_rejected "unit-struct-as-call"
        "is a bare value, not a call"
        ("urust_expr _ " ^
          cartouche " ParserMarker() ")
    val _ =
      assert_rejected "named-struct-as-call"
        "must use struct construction syntax"
        ("urust_expr _ " ^
          cartouche
            " ParserPoint(1u32, \<llangle>[] :: 32 word list\<rrangle>) ")
    val _ =
      assert_rejected "tuple-variant-as-bare-value"
        "requires positional call syntax"
        ("urust_expr _ " ^
          cartouche " ParserMessage::Data ")
    val _ =
      assert_rejected "unit-variant-as-call"
        "is a bare value, not a call"
        ("urust_expr _ " ^
          cartouche " ParserMessage::Empty() ")
    val _ =
      assert_rejected "tuple-struct-as-struct-expression"
        "does not support struct construction syntax"
        ("urust_expr _ " ^
          cartouche
            " ParserTuple { first: 1u32, second: true, third: None, } ")
    val _ =
      assert_rejected "generated-item-generics"
        "constructor generic arity does not match its declaration"
        ("urust_expr _ " ^
          cartouche
            " ParserTuple::<1>(1u32, true, None) ")
    val _ =
      assert_rejected "tuple-struct-too-few-arguments"
        "Type unification failed"
        ("urust_expr _ " ^
          cartouche " ParserTuple(1u32, true) ")
    val _ =
      assert_rejected "tuple-variant-too-many-arguments"
        "Type unification failed"
        ("urust_expr _ " ^
          cartouche " ParserMessage::Data(1u32, None, true) ")
    val _ =
      assert_rejected "tuple-pattern-wrong-arity"
        "expects 3 pattern argument(s), but got 2"
        ("urust_expr _ " ^
          cartouche
            (" match ParserTuple(1u32, true, None) { " ^
             "ParserTuple(_, _) \<Rightarrow> (), } "))
    val _ =
      assert_rejected "named-struct-pattern-missing-field"
        "is missing field(s): history"
        ("urust_expr _ " ^
          cartouche
            (" match \<llangle>undefined :: parser_point\<rrangle> { " ^
             "ParserPoint { x } \<Rightarrow> x, } "))
    val _ =
      assert_rejected "named-struct-pattern-unknown-field"
        "has unknown field \"unknown\""
        ("urust_expr _ " ^
          cartouche
            (" match \<llangle>undefined :: parser_point\<rrangle> { " ^
             "ParserPoint { unknown: _, .. } \<Rightarrow> 0u32, } "))
    val _ =
      assert_rejected "named-struct-pattern-duplicate-field"
        "has duplicate field \"x\""
        ("urust_expr _ " ^
          cartouche
            (" match \<llangle>undefined :: parser_point\<rrangle> { " ^
             "ParserPoint { x: _, x: _, .. } \<Rightarrow> 0u32, } "))
    val _ =
      assert_rejected "named-struct-pattern-multiple-rest"
        "has multiple `..` rest entries"
        ("urust_expr _ " ^
          cartouche
            (" match \<llangle>undefined :: parser_point\<rrangle> { " ^
             "ParserPoint { .., .. } \<Rightarrow> 0u32, } "))
    val _ =
      assert_rejected "tuple-struct-projection"
        "Type unification failed"
        ("urust_expr _ " ^
          cartouche " ParserTuple(1u32, true, None).0 ")
    val _ =
      assert_rejected "constructor-basename"
        "requires an exact item path"
        ("urust_expr _ " ^
          cartouche " Data(1u32, None) ")
    val _ =
      assert_rejected_all "shared-constructor-basename"
        ["requires an exact item path",
         "FirstSharedChoice::SharedPayload",
         "SecondSharedChoice::SharedPayload"]
        ("urust_expr _ " ^
          cartouche " SharedPayload(1u32) ")
    val _ =
      assert_rejected "wrong-qualified-constructor-path"
        "requires an exact micro_rust_notation (literal) declaration"
        ("urust_expr _ " ^
          cartouche " MissingModule::ParserMarker ")

    val _ =
      assert_succeeded "recovery"
        ("urust_datatype recovery_type " ^
          cartouche " struct RecoveryType; ")

    val _ =
      assert_succeeded "detached-scope"
        ("urust_datatype detached_scope " ^
          cartouche " struct DetachedScope; ")
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "DetachedScope"
    val NONE =
      URust_Item_Scope.lookup_constructor
        \<^context> "DetachedScope"
  in
    val _ = ()
  end
\<close>

chapter\<open> Type alias registry \<close>

declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 0]]

urust_type "RegistryOrdered<'value>" = \<open> 'value::linorder list \<close>

urust_type "RegistryMappedWord" = \<open> 16 word \<close>

ML\<open>
structure Registry_Alias_Probe =
struct
  open URust_AST
  val pos = Position.line_file 1 "registry-alias-probes"
  val layout = make_source_layout pos []
  fun primitive typ = Primitive_Type (typ, pos)
  fun path name types =
    Path_Type
      ([Rust_Type_Path_Segment
        (name, pos,
         if null types then NONE else SOME (map Rust_Type_Argument types),
         layout)], layout)
  fun pointer mutability typ = Raw_Pointer_Type (mutability, typ, layout)
  fun alias name parameters rhs lthy =
    #1 (Micro_Rust_Semantic_Navigation.capture (fn () =>
      URust_Type_Mappings.declare_alias
        {registration = NONE, item_name = (name, pos),
         parameters = map (fn name => (name, pos)) parameters, rhs = rhs} lthy))
  fun require description condition =
    if condition then () else error ("registry alias probe: " ^ description)
  fun captured action =
    #1 (Micro_Rust_Semantic_Navigation.capture action)
  fun rejected needle action =
    (case Exn.result (fn () => captured action) () of
       Exn.Res _ => error ("registry alias probe unexpectedly accepted: " ^ needle)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else require ("missing diagnostic " ^ needle)
           (String.isSubstring needle (Runtime.exn_message exn)))
end
\<close>

local_setup\<open>
  Registry_Alias_Probe.alias "RegistryWidth" [] (Registry_Alias_Probe.primitive URust_AST.DPT_U16) #>
  Registry_Alias_Probe.alias "RegistryChain" [] (Registry_Alias_Probe.path "RegistryWidth" []) #>
  Registry_Alias_Probe.alias "RegistryIdentity" ["T"] (Registry_Alias_Probe.path "T" []) #>
  Registry_Alias_Probe.alias "RegistryPair" ["T", "U"]
    (URust_AST.Tuple_Type
      ([Registry_Alias_Probe.path "T" [], Registry_Alias_Probe.path "U" []],
       Registry_Alias_Probe.layout)) #>
  Registry_Alias_Probe.alias "RegistrySorted" ["T"]
    (Registry_Alias_Probe.path "RegistryOrdered" [Registry_Alias_Probe.path "T" []]) #>
  Registry_Alias_Probe.alias "RegistryPtr" ["T"]
    (Registry_Alias_Probe.pointer URust_AST.RPM_Const (Registry_Alias_Probe.path "T" [])) #>
  Registry_Alias_Probe.alias "RegistryMutPtr" ["T"]
    (Registry_Alias_Probe.pointer URust_AST.RPM_Mut (Registry_Alias_Probe.path "T" [])) #>
  Registry_Alias_Probe.alias "RegistrySigned" [] (Registry_Alias_Probe.primitive URust_AST.DPT_I32) #>
  Registry_Alias_Probe.alias "RegistryUnsigned" [] (Registry_Alias_Probe.primitive URust_AST.DPT_U32) #>
  Registry_Alias_Probe.alias "RegistryMappedAlias" [] (Registry_Alias_Probe.path "RegistryMappedWord" [])
\<close>

ML_val\<open>
  local
    open Registry_Alias_Probe
    val ctxt = \<^context>
    fun resolve typ = captured (fn () => URust_Type_Mappings.resolve ctxt typ)
    fun signature_types types = captured (fn () => URust_Type_Mappings.resolve_signature ctxt types)
    fun cast typ = captured (fn () =>
      URust_Type_Mappings.resolve_cast ctxt (SCT_Type typ))
    val _ = require "alias chain changed HOL meaning"
      (resolve (path "RegistryChain" []) = \<^typ>\<open>16 word\<close>)
    val _ = require "generic identity instantiations collapsed"
      (signature_types
        [path "RegistryIdentity" [primitive DPT_U8],
         path "RegistryIdentity" [primitive DPT_U16]] =
        [\<^typ>\<open>8 word\<close>, \<^typ>\<open>16 word\<close>])
    val _ = require "positional generic tuple parameters collapsed"
      (resolve (path "RegistryPair" [primitive DPT_U8, primitive DPT_U16]) =
        \<^typ>\<open>8 word \<times> 16 word \<times> tnil\<close>)
    val SOME sorted = URust_Type_Mappings.lookup ctxt "RegistrySorted"
    val _ = require "generic sort requirement was not captured"
      (URust_Type_Mappings.entry_parameter_sorts sorted = [\<^sort>\<open>linorder\<close>])
    val _ = require "signed alias selected unsigned cast"
      (cast (path "RegistrySigned" []) = CT_Signed ST_I32)
    val _ = require "unsigned alias selected signed cast"
      (cast (path "RegistryUnsigned" []) = CT_Unsigned UT_U32)
    val _ = require "generic identity cast lost primitive metadata"
      (cast (path "RegistryIdentity" [primitive DPT_U16]) = CT_Unsigned UT_U16)
    val _ = require "const pointer alias lost mutability"
      (cast (path "RegistryPtr" [primitive DPT_U16]) =
        CT_RawPointer (RPM_Const, UT_U16))
    val _ = require "mut pointer alias lost mutability"
      (cast (path "RegistryMutPtr" [primitive DPT_U16]) =
        CT_RawPointer (RPM_Mut, UT_U16))
    val _ = rejected "no supported cast operation" (fn () =>
      cast (path "RegistryMappedAlias" []))
    val [pointer_left, pointer_right, nested] =
      signature_types
        [path "RegistryPtr" [primitive DPT_U8],
         pointer RPM_Mut (primitive DPT_U16),
         pointer RPM_Const (path "RegistryPtr" [primitive DPT_U8])]
    val expected_right =
      \<^typ>\<open>('address, 'global, 16 word) Global_Store.ref\<close>
    val expected_nested =
      \<^typ>\<open>('address, 'global, ('address, 'global, 8 word) Global_Store.ref) Global_Store.ref\<close>
    val [address, global] = Term.add_tvarsT pointer_left [] |> map TVar
    val _ = require "backend address/global slots collapsed" (address <> global)
    (* Match structurally because Term.add_tvarsT does not promise address/global order. *)
    val _ = require "signature pointers did not share their backend"
      (Type.raw_instance (pointer_right, Logic.varifyT_global expected_right) andalso
       eq_set (op =) (Term.add_tvarsT pointer_left [], Term.add_tvarsT pointer_right []) andalso
       Type.raw_instance (nested, Logic.varifyT_global expected_nested) andalso
       eq_set (op =) (Term.add_tvarsT pointer_left [], Term.add_tvarsT nested []))
    val [fresh_pointer] = signature_types [path "RegistryPtr" [primitive DPT_U8]]
    val _ = require "separate signatures reused flexible backend slots"
      (null (inter (op =) (Term.add_tvarsT pointer_left []) (Term.add_tvarsT fresh_pointer [])))
    val fields =
      captured (fn () => URust_Type_Mappings.resolve_fields ctxt
        [path "RegistryPtr" [primitive DPT_U8], pointer RPM_Mut (primitive DPT_U16)])
    val _ = require "field batch did not expose exactly one backend pair"
      (length (#backend_parameters fields) = 2 andalso
        forall (fn typ => eq_set (op =)
          (Term.add_tfreesT typ [], #backend_parameters fields)) (#types fields))
    val lthy = Named_Target.theory_init \<^theory>
    val SOME identity = URust_Type_Mappings.lookup lthy "RegistryIdentity"
    val replay = alias "RegistryIdentity" ["Value"] (path "Value" []) lthy
    val SOME identical = URust_Type_Mappings.lookup replay "RegistryIdentity"
    val _ = require "alpha-identical aliases lost navigation identity"
      (URust_Type_Mappings.entry_identity identity =
        URust_Type_Mappings.entry_identity identical)
    val _ = rejected "alias and direct/generated mapping collide" (fn () =>
      alias "RegistryMappedWord" [] (primitive DPT_U16) lthy)
    val _ = rejected "conflicting active mappings" (fn () =>
      alias "RegistryWidth" [] (primitive DPT_U8) lthy)
    val _ = rejected "duplicate type parameter" (fn () =>
      alias "RegistryDuplicate" ["T", "T"] (path "T" []) lthy)
    val _ = rejected "unused type parameters" (fn () =>
      alias "RegistryUnused" ["T"] (primitive DPT_U16) lthy)
    val _ = rejected "recursive alias dependency" (fn () =>
      alias "RegistryRecursive" [] (path "RegistryRecursive" []) lthy)
    val recursive_chain =
      lthy
      |> alias "RegistryCycleLeft" [] (primitive DPT_U16)
      |> alias "RegistryCycleRight" [] (path "RegistryCycleLeft" [])
    val _ = rejected "recursive alias dependency" (fn () =>
      alias "RegistryCycleLeft" [] (path "RegistryCycleRight" []) recursive_chain)
    val _ = rejected "unknown Rust type" (fn () =>
      alias "RegistryUnknown" [] (path "RegistryMissing" []) lthy)
    val _ = rejected "generic arities" (fn () =>
      alias "RegistryArity" [] (path "RegistryIdentity" []) lthy)
    val _ = rejected "does not satisfy sort" (fn () =>
      resolve (path "RegistrySorted"
        [HOL_Type_Source (Input.string "nat \<Rightarrow> nat")]))
    val _ = rejected "type variables are not supported" (fn () =>
      resolve (HOL_Type_Source (Input.string "'unrelated")))
    val _ = rejected "unrelated HOL type variables" (fn () =>
      alias "RegistryFreeEscape" [] (HOL_Type_Source (Input.string "'unrelated")) lthy)
    val fixed = TFree ("'fixed", \<^sort>\<open>type\<close>)
    val fixed_ctxt = Variable.declare_typ fixed ctxt
    val [fixed_alias] = captured (fn () =>
      URust_Type_Mappings.resolve_signature fixed_ctxt
        [path "RegistryIdentity" [HOL_Type_Source (Input.string "'fixed")]])
    val _ = require "ambient signature type was made flexible" (fixed_alias = fixed)
    val _ = rejected "does not satisfy sort" (fn () =>
      URust_Type_Mappings.resolve_signature fixed_ctxt
        [path "RegistrySorted" [HOL_Type_Source (Input.string "'fixed")]])
    val generated_parameters =
      [("'generated_address", \<^sort>\<open>type\<close>),
       ("'generated_global", \<^sort>\<open>type\<close>)]
    val generated_template =
      Type (\<^type_name>\<open>prod\<close>, map TFree generated_parameters)
    val generated = captured (fn () =>
      URust_Type_Mappings.register_generated_scheme
        {rust_name = "RegistryGeneratedPair", rust_pos = pos,
         hol_type_name = \<^type_name>\<open>prod\<close>,
         hol_type = generated_template, backend_parameters = generated_parameters}
        lthy)
    val generated_alias = alias "RegistryGeneratedAlias" []
      (path "RegistryGeneratedPair" []) generated
    val generated_fields = captured (fn () =>
      URust_Type_Mappings.resolve_fields generated_alias
        [path "RegistryGeneratedPair" [], path "RegistryGeneratedAlias" [],
         pointer RPM_Const (primitive DPT_U8)])
    val SOME generated_entry =
      URust_Type_Mappings.lookup generated_alias "RegistryGeneratedPair"
    val _ = require "generated scheme exposed Rust generic arguments"
      (URust_Type_Mappings.entry_arities generated_entry = [0] andalso
        null (URust_Type_Mappings.entry_parameter_sorts generated_entry))
    val [generated_direct, generated_synonym, generated_pointer] = #types generated_fields
    val _ = require "generated alias did not share the field batch backend pair"
      (generated_direct = generated_synonym andalso
       eq_set (op =)
         (Term.add_tfreesT generated_direct [], Term.add_tfreesT generated_pointer []))
    val _ = rejected "alias and direct/generated mapping collide" (fn () =>
      alias "RegistryGeneratedPair" [] (primitive DPT_U16) generated)
    val registration_pos =
      Position.make0 7 101 118 "" "registry-quoted-path" "registry-path-probe"
    val item_pos =
      Position.make0 9 205 216 "" "registry-quoted-path" "registry-path-probe"
    val malformed_path_message =
      (case Exn.result (fn () => captured (fn () =>
          URust_Type_Mappings.declare_alias
            {registration = SOME ("wire::::InvalidPath", registration_pos),
             item_name = ("InvalidPath", item_pos), parameters = [],
             rhs = primitive DPT_U16} lthy)) () of
         Exn.Res _ => error "malformed registration path unexpectedly accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    fun diagnostic_range (XML.Text _) ranges = ranges
      | diagnostic_range (XML.Elem ((_, properties), children)) ranges =
          let
            val ranges' =
              (case
                (Properties.get properties Markup.offsetN,
                 Properties.get properties Markup.end_offsetN) of
                 (SOME offset, SOME end_offset) => (offset, end_offset) :: ranges
               | _ => ranges)
          in fold diagnostic_range children ranges' end
    val _ = require "malformed quoted path reported a duplicate or item-name range"
      (fold diagnostic_range (YXML.parse_body malformed_path_message) [] =
        [("101", "118")])
  in val _ = writeln "registry alias probes passed" end
\<close>

chapter\<open> Type alias syntax \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]

ML\<open>
local
  open URust_AST
  val ctxt = \<^context>
  fun require label condition =
    if condition then () else error ("alias syntax probe: " ^ label)
  fun source text = Parser_Lex_Util.text_source text
  fun alias text =
    (case URust_Parser.parse_type_alias_source ctxt (source text) of
       SOME item => item
     | NONE => error "alias syntax probe: missing item")
  fun expression text =
    (case URust_Parser.parse_source ctxt (source text) of
       SOME ast => ast
     | NONE => error "alias syntax probe: missing expression")
  fun reject label parse text =
    (case Exn.result (fn () => parse text) () of
       Exn.Exn _ => ()
     | Exn.Res _ => error ("alias syntax probe: accepted " ^ label))
  fun alias_roundtrip text =
    let
      val original = alias text
      val options = URust_Printer.serialized_options
      val rendered = URust_Printer.string_of_type_alias options original
      val reparsed = alias rendered
    in
      require ("alias tokens changed for " ^ text)
        (URust_Printer.tokens_of_type_alias options original =
         URust_Printer.tokens_of_type_alias options reparsed);
      require ("alias printer is unstable for " ^ text)
        (rendered = URust_Printer.string_of_type_alias options reparsed)
    end
  fun expression_roundtrip text =
    let
      val original = expression text
      val options = URust_Printer.serialized_options
      val rendered = URust_Printer.string_of_expr options original
      val reparsed = expression rendered
      val human = URust_Printer.string_of_expr URust_Printer.human_options original
      val human_reparsed = expression human
    in
      require ("cast tokens changed for " ^ text)
        (URust_Printer.tokens_of_expr options original =
         URust_Printer.tokens_of_expr options reparsed);
      require ("human printer is unstable for " ^ text)
        (human = URust_Printer.string_of_expr URust_Printer.human_options human_reparsed)
    end
  val _ =
    List.app alias_roundtrip
      ["type Width = u16;",
       "type OtherWidth = Width;",
       "type Pair<T> = (T, T);",
       "type Pair<T, U,> = (T, U);",
       "type Ptr<T> = *const T;",
       "type MutPtr<T> = *mut T;",
       "type Nested<T> = Option<*const Pair<T, T>>;",
       "type Deep<T> = Option<Option<Option<T>>>;",
       "type Qualified = types::Width;",
       "type Mapped<T> = containers::Array<T, 32>;",
       "type Group<T> = (T);",
       "type OneTuple<T> = (T,);",
       "type Array = [u8; 32];",
       "type NestedArray<T> = Option<Option<[T; 32]>>;",
       "type Escaped = \<tau>\<open>nat\<close>;",
       "/* outer /* nested */ comment */ type Comments<T> = /* rhs */ T;"]
  val _ =
    List.app (reject "malformed alias" alias)
      ["", "type Width = u16", "type = u16;", "type Width u16;",
       "type Width = ;", "type Pair<> = u16;", "type Pair<T: Bound> = T;",
       "type Pair<T = u8> = T;", "type Pair<const N> = u8;",
       "type Pair<T> = Option<T>;;", "type Width = u16; type Extra = u8;",
       "struct Width;", "fn width() {}"]
  val _ =
    List.app expression_roundtrip
      ["value as u8", "value as i32", "value as *const u16",
       "value as *mut u32", "value as Width", "value as types::Width",
       "value as Identity<u16>", "value as Pair<u8, u16>",
       "value as Identity<Identity<u16>>",
       "value as Identity<Identity<Identity<u16>>>",
       "value as Ptr<Option<u16>>",
       "value as *const Identity<u16>",
       "value as &&u8",
       "value as Identity<&&u8>",
       "value as (u16)", "value as (u8, u16)", "value as [u8; 4]",
       "value as bool", "value as i16", "value as u128",
       "value as Identity<u16> as Identity<u32>",
       "(value as u16) < limit",
       "(value as Width) << shift",
       "(value + other as u16) < limit",
       "value as (u16) < limit",
       "value as Identity<u16> < limit",
       "value as Identity<u16> << shift",
       "value as Identity<Identity<u16>> >> shift",
       "value as Identity<u16>> limit",
       "value as Identity<u16>>= limit",
       "value as Identity<Identity<u16>>>= limit",
       "left >> right", "left << right",
       "left >>= right", "left <<= right",
       "if value as Identity<u16> < limit { left } else { right }",
       "if (value as u16) < limit { left } else { right }",
       "[value as Identity<u16>; 2 as usize]"]
  val _ =
    List.app (reject "ambiguous or malformed cast" expression)
      ["value as u16 < limit", "value as u16 << shift",
       "value as Width < limit", "value as Width << shift",
       "if value as u16 < limit { left } else { right }",
       "value as Identity<>", "value as Identity<u16",
       "[value; 2 as Width]", "[value; 2 as Identity<usize>]",
       "[value; 2 as (usize)]", "type Width = u16;"]
  val recovered = alias "type Recovered<T> = Option<Option<T>>;"
  val _ = require "parser state did not recover" (#1 (type_alias_name recovered) = "Recovered")
  val recovered_expression = expression "left >> right"
  val _ =
    (case recovered_expression of
       UE_Bin (Shr, _, _, _) => ()
     | _ => error "alias syntax probe: expression shift changed after recovery")
  val positions_source =
    Parser_Lex_Util.positioned_content_source
      "type Positioned<T, U> = Pair<T, U>;"
      (Position.make0 23 5000 0 "" "" "type-alias-syntax-positions")
  val positions_item = the (URust_Parser.parse_type_alias_source ctxt positions_source)
  fun offsets pos = (Position.offset_of pos, Position.end_offset_of pos)
  val _ =
    require "alias parameter source ranges changed"
      (map (offsets o #2) (type_alias_parameters positions_item) =
        [(SOME 5016, SOME 5017), (SOME 5019, SOME 5020)])
  val _ =
    require "alias complete span changed"
      (offsets (type_alias_item_position positions_item) =
        (SOME 5000, SOME 5035))
  val _ =
    (case expression "value as Identity<u16>" of
       UE_Cast (_, SCT_Type (Path_Type
         ([Rust_Type_Path_Segment
           ("Identity", _, SOME [Rust_Type_Argument (Primitive_Type (DPT_U16, _))], _)],
           _)), _) => ()
     | _ => error "alias syntax probe: cast did not use shared type AST")
  val _ =
    (case expression "value as *const u16" of
       UE_Cast (_, target as SCT_Primitive
         (CT_RawPointer (RPM_Const, UT_U16), _), _) =>
           require "legacy primitive position API disappeared"
             (is_some (source_cast_target_type_position target))
     | _ => error "alias syntax probe: primitive compatibility AST changed")
  val _ =
    URust_Printer_Output.pretty_human_type_alias_with_reparse
      (fn input => ignore (URust_Parser.parse_type_alias_source ctxt input))
      (alias "type Printable<T> = (T, T);")
    |> ignore
in
  val _ = writeln "W2 alias syntax, shared casts, positions, recovery and printer probes passed"
end
\<close>

chapter\<open> Rust type aliases in cast targets \<close>

section\<open> Imported aliases are available \<close>

declare [[urust_verbosity = 0]]

ML_val\<open>
  local
    val ctxt = \<^context>
    val alias =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "0_u64 as U8Alias")
    val primitive =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "0_u64 as u8")
  in
    val _ =
      if Term.aconv (alias, primitive) then ()
      else error "imported Rust alias did not retain its declared meaning"
  end
\<close>

section\<open> Primitive equivalence and grammar composition \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun parse text =
      (case
          URust_Parser.parse_source ctxt
            (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "cast-target alias audit: empty parse")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun assert message condition =
      if condition then ()
      else error ("cast-target alias audit: " ^ message)
  in
    val _ =
      (case parse "value as types::U16Alias" of
         UE_Cast
           (UE_Path _,
            SCT_Named path, _) =>
           assert "named cast target lost its exact qualified path"
             (render_path path = "types::U16Alias")
       | _ =>
           error
             "cast-target alias audit: named cast AST shape changed")
    val _ =
      assert "unchecked integral alias changed the generated term"
        (Term.aconv
          (unchecked "value as U8Alias",
           unchecked "value as u8"))
    val _ =
      assert "unchecked qualified alias changed the generated term"
        (Term.aconv
          (unchecked "value as types::U16Alias",
           unchecked "value as u16"))
    val _ =
      assert "unchecked pointer alias changed the generated term"
        (Term.aconv
          (unchecked "value as MutUsizePointer",
           unchecked "value as *mut usize"))
    val _ =
      assert "unchecked alias chain changed the generated term"
        (Term.aconv
          (unchecked "value as U64Alias as U8Alias as I32Alias",
           unchecked "value as u64 as u8 as i32"))
  end
\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_failure label action expected =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("cast-target alias " ^ label ^
               " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if String.isSubstring expected message then ()
               else
                 error
                   ("cast-target alias " ^ label ^
                     " produced the wrong diagnostic:\n" ^ message)
             end)

    val _ =
      expect_failure "generic use"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source
              "0_u64 as U8Alias::<Width>"))
        "syntax error"

    val _ =
      expect_failure "inexact qualified use"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source "0u64 as U16Alias"))
        "unknown Rust type"

    val _ =
      expect_failure "wrong qualifier"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source "0u64 as other::U16Alias"))
        "unknown Rust type"

  in
    val _ = ()
  end
\<close>

section\<open> Direct declarations and locale scope \<close>

context cast_alias_scope
begin

ML_val\<open>
  local
    val ctxt = \<^context>
    val alias =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "scope_word as LocaleWidth")
    val primitive =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "scope_word as u16")
  in
    val _ =
      if Term.aconv (alias, primitive) then ()
      else error "locale alias did not persist in its declaration context"
  end
\<close>

end

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then () else error ("cast-target alias diagnostics: " ^ message)

    fun reject_then_recover (text, prefix, expected) =
      let
        val start = Position.make0 23 7 0 "" "" "cast-alias-positioned-use"
        val expected_pos = Position.symbol_explode prefix start
        val source = Parser_Lex_Util.positioned_content_source text start
        val _ =
          (case Exn.result (Parser_Test_Elaboration.expression ctxt) source of
             Exn.Res _ => error ("invalid cast-target alias accepted: " ^ quote text)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let
                   val raw_message = Runtime.exn_message exn
                   val message = XML.content_of (YXML.parse_body raw_message)
                   val markup =
                     fold Parser_Test_Reports.collect_markup
                       (YXML.parse_body raw_message) []
                   val positions =
                     map_filter
                       (fn (name, props) =>
                         if name = Markup.positionN
                         then SOME (Position.of_properties props)
                         else NONE)
                       markup
                 in
                   assert "wrong rejection reason" (String.isSubstring expected message);
                   assert "error lost its smallest source position"
                     (exists
                       (fn pos =>
                         Position.file_of pos = Position.file_of expected_pos andalso
                         Position.offset_of pos = Position.offset_of expected_pos)
                       positions)
                 end)
        val alias =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source "0u64 as types::U16Alias")
        val primitive =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source "0u64 as u16")
      in
        assert "failed declaration/use poisoned subsequent elaboration"
          (Term.aconv (alias, primitive))
      end
  in
    val _ = List.app reject_then_recover
      [("0u64 as UnknownWidth", "0u64 as ", "unknown Rust type"),
       ("0u64 as types::UnknownWidth", "0u64 as ", "unknown Rust type"),
       ("0u64 as U8Alias::<Width>", "0u64 as U8Alias",
        "syntax error")]
  end
\<close>

ML_val\<open>
  local
    fun rejected text =
      (case
          Exn.result
            (Parser_Test_Elaboration.expression \<^context>)
            (Parser_Lex_Util.text_source text) of
         Exn.Res _ => false
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             String.isSubstring "unknown Rust type"
               (Runtime.exn_message exn))
    val imported_alias =
      Parser_Test_Elaboration.expression \<^context>
        (Parser_Lex_Util.text_source "0_u64 as U8Alias")
    val primitive =
      Parser_Test_Elaboration.expression \<^context>
        (Parser_Lex_Util.text_source "0_u64 as u8")
  in
    val _ =
      if rejected "0_u64 as ExperimentWidth" andalso
         rejected "0_u64 as LocaleWidth" andalso
         Term.aconv (imported_alias, primitive)
      then ()
      else
        error
          "cast-target alias remained active after its confined context"
  end
\<close>

section\<open> Conflicts and idempotence \<close>

ML_val\<open>
  local
    fun declare source_name text lthy =
      #1 (Micro_Rust_Semantic_Navigation.capture (fn () =>
        let
          val source =
            Parser_Lex_Util.positioned_content_source text
              (Position.line_file 1 source_name)
          val item =
            (case URust_Parser.parse_type_alias_source lthy source of
               SOME item => item
             | NONE => error "direct alias audit: empty declaration")
        in
          URust_Type_Mappings.declare_alias
            {registration = NONE,
             item_name = URust_AST.type_alias_name item,
             parameters = URust_AST.type_alias_parameters item,
             rhs = URust_AST.type_alias_rhs item}
            lthy
        end))

    fun collect_markup (XML.Text _) result = result
      | collect_markup
          (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    val base_lthy = Named_Target.theory_init \<^theory>
    val left_context =
      declare "cast-alias-conflict-left" "type SharedWidth = u8;" base_lthy
    val conflict =
      Exn.result
        (fn () =>
          declare "cast-alias-conflict-right" "type SharedWidth = u16;"
            left_context)
        ()

    val _ =
      (case conflict of
         Exn.Res _ =>
           error "conflicting direct Rust alias declarations were accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val raw_message = Runtime.exn_message exn
               val message =
                 XML.content_of (YXML.parse_body raw_message)
                   handle Fail _ => raw_message
               val positions =
                 maps YXML.parse_body [raw_message]
                 |> (fn trees => fold collect_markup trees [])
                 |> map_filter
                     (fn (name, properties) =>
                       if name = Markup.positionN
                       then SOME properties
                       else NONE)
                 |> distinct (op =)
             in
               if String.isSubstring
                    "conflicting active mappings for \"SharedWidth\""
                    message andalso
                  String.isSubstring "different Rust meanings" message andalso
                  String.isSubstring "urust_type_alias declaration" message andalso
                  length positions = 2 andalso
                  member (op =)
                    (map (Position.file_of o Position.of_properties) positions)
                    (SOME "cast-alias-conflict-left") andalso
                  member (op =)
                    (map (Position.file_of o Position.of_properties) positions)
                    (SOME "cast-alias-conflict-right")
               then ()
               else
                 error
                   ("conflicting direct Rust alias diagnostic did not " ^
                     "report both declarations:\n" ^ message)
             end)

    val SOME original = URust_Type_Mappings.lookup base_lthy "StableWidth"
    val repeated_context =
      base_lthy
      |> declare "cast-alias-idempotent-first" "type StableWidth = u16;"
      |> declare "cast-alias-idempotent-second" "type StableWidth = u16;"
    val SOME repeated = URust_Type_Mappings.lookup repeated_context "StableWidth"
    val _ =
      if URust_Type_Mappings.entry_identity original =
          URust_Type_Mappings.entry_identity repeated
      then ()
      else error "idempotent direct alias registration changed navigation identity"
    val _ =
      ignore
        (Parser_Test_Elaboration.expression repeated_context
          (Parser_Lex_Util.text_source
            "0_u64 as StableWidth"))
  in
    val _ = ()
  end
\<close>

section\<open> Declaration and use diagnostics \<close>

ML_val\<open>
  local
    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun assert_rejected source_name command_text expected =
      (case
          Exn.result
            (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("invalid cast-target alias declaration was accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring expected message andalso
                  String.isSubstring source_name message
               then ()
               else
                 error
                   ("wrong cast-target alias declaration diagnostic:\n" ^
                     message)
             end)

    val _ =
      assert_rejected "cast-alias-unknown-dependency"
        ("urust_type_alias " ^ Symbol.open_ ^ " type AliasChain = MissingAliasDependency; " ^ Symbol.close)
        "unknown Rust type"
    val _ =
      assert_rejected "cast-alias-malformed-target"
        ("urust_type_alias " ^ Symbol.open_ ^ " type BrokenPointer = *const; " ^ Symbol.close)
        "syntax error"
    val _ =
      assert_rejected "cast-alias-generic-name"
        ("urust_type_alias \"Types::Alias::<Width>\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-empty-segment"
        ("urust_type_alias \"Types::\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-reserved-segment"
        ("urust_type_alias \"Types::u16\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "reserved segment"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val text =
      "value as U8Alias; value as U8Alias; " ^
      "value as types::U16Alias"
    val start =
      Position.make0 17 4 0 "" ""
        "cast-target-alias-markup"
    val reports =
      Synchronized.var "cast_target_alias_reports" ([]: string list)

    fun capture chunks =
      Synchronized.change reports (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                let
                  val source =
                    Parser_Lex_Util.positioned_content_source
                      text start
                  val expression =
                    (case URust_Parser.parse_source ctxt source of
                       SOME parsed => parsed
                     | NONE =>
                         error
                           "cast-target alias markup audit: empty parse")
                in
                  ignore
                    (URust_Translate.mk_expression ctxt [] expression)
                end)
              ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)

    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value reports)) []

    fun alias_references alias =
      map_filter
        (fn (name, properties) =>
          if name = Markup.entityN andalso
             Properties.get properties Markup.kindN =
               SOME "micro_rust_type_mapping" andalso
             Properties.get properties Markup.nameN = SOME alias
          then Properties.get properties Markup.refN
          else NONE)
        markup

    fun count_markup name =
      length (filter (fn (actual, _) => actual = name) markup)

    val u8_references = alias_references "U8Alias"
    val qualified_references =
      alias_references "types::U16Alias"
    val _ =
      if length u8_references = 2 andalso
         length (distinct (op =) u8_references) = 1
      then ()
      else
        error
          "cast-target alias uses did not retain one stable declaration identity"
    val _ =
      if length qualified_references = 1 then ()
      else
        error
          "qualified cast-target alias lost its declaration reference"
    val _ =
      if count_markup Markup.keyword3N >= 4 andalso
         count_markup Markup.typingN >= 4
      then ()
      else
        error
          "cast-target alias segments lost semantic or typing markup"
  in
    val _ =
      writeln
        "Direct Rust alias term, scope, diagnostic, and markup regressions passed"
  end
\<close>

chapter\<open> Rust type aliases \<close>

declare [[urust_verbosity = 2]]

ML_val\<open>
local
  val thy = \<^theory>
  val _ =
    if Keyword.is_command (Thy_Header.get_keywords thy) "urust_cast_alias"
    then error "retired urust_cast_alias keyword remains installed"
    else ()
  val retired = Exn.result (fn () =>
    Outer_Syntax.parse_text thy (K thy)
      (Position.line_file 1 "retired-type-alias-command")
      "urust_cast_alias \"RetiredWidth\" = \"u16\""
    |> (fn transitions => fold (Toplevel.command_exception false)
      transitions (Toplevel.make_state (SOME thy)))) ()
  val _ =
    (case retired of
       Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn else ()
     | Exn.Res _ => error "retired urust_cast_alias command accepted")
  val pointer_type =
    Consts.the_constraint (Proof_Context.consts_of \<^context>)
      \<^const_name>\<open>command_pointer_identity\<close>
  val _ =
    if length (Term.add_tvarsT (hd (binder_types pointer_type)) []) = 2 then ()
    else error "pointer alias signature did not generalize both backend parameters"
in
  val _ = writeln "alias command and existing primitive cast equivalences passed"
end
\<close>

section\<open> Command failures, dependency capture and recovery \<close>

ML_val\<open>
local
  val thy = \<^theory>
  val ctxt = \<^context>
  fun require message condition =
    if condition then () else error ("alias command audit: " ^ message)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun command file text =
    Outer_Syntax.parse_text thy (K thy)
      (Position.make0 1 1 0 "" file ""
        |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false)
         transitions (Toplevel.make_state (SOME thy)))
  fun declaration text = "urust_type_alias " ^ cartouche text
  fun reject (label, text, expected) =
    (case Exn.result (fn () => command label text) () of
       Exn.Res _ => error ("invalid alias command accepted: " ^ label)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else require ("wrong diagnostic: " ^ label)
           (String.isSubstring expected (Runtime.exn_message exn)))
  val _ = List.app reject
    [("alias-duplicate", declaration "type Duplicate<T, T> = T;",
       "duplicate type parameter"),
     ("alias-unused", declaration "type Unused<T> = u16;",
       "unused type parameters"),
     ("alias-recursive", declaration "type Recursive = Recursive;",
       "recursive alias dependency"),
     ("alias-unknown", declaration "type Unknown = UnknownDependency;",
       "unknown Rust type"),
     ("alias-arity", declaration "type WrongArity = CommandIdentity<u8, u16>;",
       "generic arities"),
     ("alias-sort", declaration ("type WrongSort = CommandSorted<" ^
        "\<tau>" ^ cartouche "nat \<Rightarrow> nat" ^ ">;"),
       "does not satisfy sort"),
     ("alias-variable", declaration ("type FreeEscape = \<tau>" ^
        cartouche "'unrelated" ^ ";"), "unrelated HOL type variables"),
     ("alias-terminal", "urust_type_alias \"types::Different\" " ^
        cartouche "type Declared = u16;", "must match item name"),
     ("alias-manual-collision", declaration "type CommandMapped = u16;",
       "alias and direct/generated mapping collide"),
     ("manual-alias-collision", "urust_type \"CommandWidth\" = " ^
        cartouche "16 word", "alias and direct/generated mapping collide"),
     ("generated-alias-collision", "urust_datatype " ^
        cartouche "struct CommandWidth(u16);",
       "alias and direct/generated mapping collide"),
     ("alias-mutability-conflict", declaration "type CommandPtr<T> = *mut T;",
       "different Rust meanings")]
  val alias = the (URust_Type_Mappings.lookup ctxt "CommandChain")
  val _ = require "dependency was not captured as a checked HOL template"
    (URust_Type_Mappings.entry_template alias = \<^typ>\<open>16 word\<close>)
  val _ = reject
    ("captured-dependency-conflict", declaration "type CommandWidth = u8;",
     "conflicting active mappings")
  val recovered =
    command "alias-command-recovery" (declaration "type RecoveredAlias = CommandChain;")
    |> Toplevel.context_of
  val _ = require "recovery changed captured meaning"
    (Parser_Test_Elaboration.expression recovered
       (Parser_Lex_Util.text_source "5u32 as RecoveredAlias")
     aconv
     Parser_Test_Elaboration.expression ctxt
       (Parser_Lex_Util.text_source "5u32 as u16"))
  val _ = require "failed declarations installed a registry entry"
    (forall (is_none o URust_Type_Mappings.lookup ctxt)
      ["Duplicate", "Unused", "Recursive", "Unknown", "WrongArity",
       "WrongSort", "FreeEscape", "Declared"])
  val (navigation_state, markup) =
    Parser_Test_Reports.markup (fn () =>
      command "alias-dependency-navigation"
        (declaration "type NavigationAlias<T> = CommandIdentity<T>;"))
  fun entities property alias reports =
    map_filter
      (fn (name, props) =>
        if name = Markup.entityN andalso
           Properties.get props Markup.kindN = SOME "micro_rust_type_mapping" andalso
           Properties.get props Markup.nameN = SOME alias
        then Properties.get props property else NONE)
      reports
  val identity = the (URust_Type_Mappings.lookup ctxt "CommandIdentity")
  val installed =
    the (URust_Type_Mappings.lookup (Toplevel.context_of navigation_state) "NavigationAlias")
  val _ = require "alias declaration lost its entity identity"
    (entities Markup.defN "NavigationAlias" markup =
      [string_of_int (URust_Type_Mappings.entry_identity installed)])
  val _ = require "alias dependency did not navigate to its captured declaration"
    (entities Markup.refN "CommandIdentity" markup =
      [string_of_int (URust_Type_Mappings.entry_identity identity)])
  val _ = require "alias parameters lost their declaration and use markup"
    (length (filter (fn (name, _) => name = Markup.tfreeN) markup) >= 2)
  val (_, failed_markup) =
    Parser_Test_Reports.markup (fn () =>
      Exn.result (fn () =>
        command "alias-failed-navigation"
          (declaration "type FailedNavigation<T> = (CommandIdentity<T>, MissingType);")) ())
  val _ = require "failed declaration replayed successful semantic reports"
    (null (entities Markup.defN "FailedNavigation" failed_markup) andalso
     null (entities Markup.refN "CommandIdentity" failed_markup))
in
  val _ = writeln "alias command failures, capture and recovery passed"
end
\<close>

section\<open> Definition-time capture across dependency scopes \<close>

context includes capture_dependency_right
begin

ML_val\<open>
  val captured = the (URust_Type_Mappings.lookup \<^context> "CapturedDependency")
  val dependency = the (URust_Type_Mappings.lookup \<^context> "CaptureDependency")
  val _ =
    if URust_Type_Mappings.entry_template captured = \<^typ>\<open>16 word\<close> andalso
       URust_Type_Mappings.entry_template dependency = \<^typ>\<open>8 word\<close>
    then ()
    else error "alias meaning changed with its dependency's active scope"
\<close>

urust_fn \<open>
  fn CapturedWidths(left: CapturedDependency, right: CaptureDependency) -> (u16, u8) {
    (left, right)
  }
\<close>

end

chapter\<open> Raw pointer types \<close>

ML\<open>
structure Datatype_Pointer_Probe =
struct
  fun require message condition =
    if condition then () else error ("datatype pointer probe: " ^ message)
end
\<close>

ML_val\<open>
  local
    open Datatype_Pointer_Probe
    val ctxt = \<^context>
    fun mapping name = the (URust_Type_Mappings.lookup ctxt name)
    fun sugar name = the (Ctr_Sugar.ctr_sugar_of ctxt name)
    fun require_pointer name hol_name =
      let
        val entry = mapping name
        val native = sugar hol_name
        val (_, parameters) = dest_Type (#T native)
        val _ = require (name ^ " lost its address/global parameters")
          (length parameters = 2 andalso hd parameters <> hd (tl parameters) andalso
           forall Term.is_TVar parameters)
        val _ = require (name ^ " exposed extra Rust generic arguments")
          (URust_Type_Mappings.entry_arities entry = [0] andalso
           null (URust_Type_Mappings.entry_parameter_sorts entry))
        val _ = require (name ^ " registry lost implicit backend parameters")
          (length (URust_Type_Mappings.entry_backend_parameter_sorts entry) = 2)
        val _ = require (name ^ " fields use different backend parameters")
          (forall (fn constructor =>
             eq_set (op =)
               (Term.add_tvars constructor [], Term.add_tvarsT (#T native) []))
            (#ctrs native))
      in () end
    val _ = List.app (fn (name, hol_name) => require_pointer name hol_name)
      [("PointerPacket", \<^type_name>\<open>pointer_packet\<close>),
       ("PointerFields", \<^type_name>\<open>pointer_fields\<close>),
       ("PointerTuple", \<^type_name>\<open>pointer_tuple\<close>),
       ("PointerChoice", \<^type_name>\<open>pointer_choice\<close>),
       ("PointerOuter", \<^type_name>\<open>pointer_outer\<close>),
       ("PointerWrapped", \<^type_name>\<open>pointer_wrapped\<close>)]
    val SOME packet = URust_Item_Scope.lookup_constructor ctxt "PointerPacket"
    val _ = require "stored constructor lost its native scheme"
      (fastype_of (URust_Item_Scope.constructor_scheme packet) =
        fastype_of (hd (#ctrs (sugar \<^type_name>\<open>pointer_packet\<close>))))
    val _ = require "expression constructor no longer infers fresh type instances"
      (URust_Item_Scope.constructor_term packet =
        Const (\<^const_name>\<open>make_pointer_packet\<close>, dummyT))
    val pointer_field = hd (URust_Item_Scope.constructor_field_entries packet)
    val _ = require "stored selector lost its native scheme"
      (fastype_of (URust_Item_Scope.field_scheme pointer_field) =
        fastype_of (hd (hd (#selss (sugar \<^type_name>\<open>pointer_packet\<close>)))))
    val _ = require "expression selector no longer infers fresh type instances"
      (URust_Item_Scope.field_selector pointer_field =
        Const (\<^const_name>\<open>pointer_packet_pointer\<close>, dummyT))
    val descriptor =
      prepare_record_descriptor "pointer_packet" (Named_Target.theory_init \<^theory>)
    val _ = require "lens descriptor uses a different record scheme"
      (#record_type descriptor = #T (sugar \<^type_name>\<open>pointer_packet\<close>))
    val _ = require "pointer selector scheme diverged from its record parameter pair"
      (eq_set (op =)
        (Term.add_tvarsT (#field_type (hd (#fields descriptor))) [],
         Term.add_tvarsT (#record_type descriptor) []))
    val _ = List.app
      (fn name =>
        require (name ^ " gained implicit parameters")
          (null (URust_Type_Mappings.entry_backend_parameter_sorts (mapping name))))
      ["PlainPacket", "PlainTuple", "PlainChoice"]
    val _ = require "nonpointer record became polymorphic"
      (null (snd (dest_Type (#T (sugar \<^type_name>\<open>plain_packet\<close>)))))
    fun function_type name =
      Consts.the_constraint (Proof_Context.consts_of ctxt) name
    val build_type = function_type \<^const_name>\<open>build_pointer_packet\<close>
    val read_type = function_type \<^const_name>\<open>read_pointer_packet\<close>
    val _ = require "constructor function did not generalize pointer backends"
      (length (Term.add_tvarsT (hd (binder_types build_type)) []) = 2)
    val _ = require "selector function did not generalize pointer backends"
      (length (Term.add_tvarsT (hd (binder_types read_type)) []) = 2)
    val lthy = Named_Target.theory_init \<^theory>
    val rejected =
      Exn.result (fn () =>
        URust_Datatype.define
          {source = Input.string "struct PointerBad { pointer: *const u8, unrelated: \<tau>\<open>'unrelated\<close> }",
           explicit_binding = NONE, interactive = false, verbosity = 0,
           pp_test = true, pretty = false, register_notation = true, renames = [],
           unprefixed_selectors = NONE,
           backend = "hol", word_width = NONE, parameters = [], plugins = K Plugin_Name.default_filter}
          lthy) ()
    val _ =
      (case rejected of
         Exn.Res _ => error "unrelated HOL field variable was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else require "wrong unrelated-variable diagnostic"
             (String.isSubstring "unrelated HOL variable"
               (Runtime.exn_message exn)))
    val _ = require "failed datatype installed its mapping"
      (is_none (URust_Type_Mappings.lookup lthy "PointerBad"))
  in val _ = writeln "datatype pointer probes passed" end
\<close>

section\<open> Signature constraints and independent instantiation \<close>

ML_val\<open>
local
  val ctxt = \<^context>
  fun require message condition =
    if condition then () else error ("pointer signature audit: " ^ message)
  fun argument_type name =
    Consts.the_constraint (Proof_Context.consts_of ctxt) name
    |> binder_types |> hd
  val _ = require "body did not constrain the pointer backend"
    (argument_type \<^const_name>\<open>pointer_body_constraint\<close> =
      \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>)
  val _ = require "explicit result did not constrain the pointer backend"
    (argument_type \<^const_name>\<open>pointer_result_constraint\<close> =
      \<^typ>\<open>(int, nat, 8 word) Global_Store.ref\<close>)
  val independent_type =
    Consts.the_constraint (Proof_Context.consts_of ctxt)
      \<^const_name>\<open>pointer_independent_calls\<close>
  val _ = require "independent calls lost one concrete backend"
    (Term.exists_subtype
       (fn T => T = \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>)
       independent_type andalso
     Term.exists_subtype
       (fn T => T = \<^typ>\<open>(int, nat, 8 word) Global_Store.ref\<close>)
       independent_type)
in
  val _ = ()
end
\<close>

locale pointer_alias_context =
  fixes pointer :: "('address, 'global, 8 word) Global_Store.ref"
begin

urust_type_alias \<open> type LocalePointer<T> = *const T; \<close>
urust_datatype \<open> struct LocalePointerPacket { pointer: LocalePointer<u8> } \<close>

urust_fn \<open>
  fn LocalePointerIdentity(value: LocalePointer<u8>) -> LocalePointer<u8> {
    if true { value } else { pointer }
  }
\<close>

ML_val\<open>
local
  val typ =
    fastype_of (Syntax.read_term \<^context> "locale_pointer_identity")
  val pointer_type = fastype_of (Syntax.read_term \<^context> "pointer")
in
  val _ =
    if member (op =) (binder_types typ) pointer_type then ()
    else error "locale signature lost its rigid pointer backend"
end
\<close>

end

context pointer_alias_context
begin

urust_fn \<open>
  fn ReopenLocalePointer(packet: LocalePointerPacket) -> LocalePointer<u8> {
    packet.pointer
  }
\<close>

ML_val\<open>
  val _ =
    if is_some (URust_Item_Scope.lookup_constructor \<^context> "LocalePointerPacket") andalso
       is_some (URust_Type_Mappings.lookup \<^context> "LocalePointer")
    then ()
    else error "locale reopening lost pointer type schemes"
\<close>

end

locale pointer_alias_left = pointer_alias_context pointer for pointer

locale pointer_alias_right = pointer_alias_context pointer for pointer

locale pointer_alias_join =
  pointer_alias_left pointer + pointer_alias_right pointer for pointer
begin

urust_fn \<open>
  fn MergedLocalePointer(packet: LocalePointerPacket) -> LocalePointer<u8> {
    packet.pointer
  }
\<close>

ML_val\<open>
local
  val ctxt = \<^context>
  val entry = the (URust_Type_Mappings.lookup ctxt "LocalePointerPacket")
  val constructor = the (URust_Item_Scope.lookup_constructor ctxt "LocalePointerPacket")
in
  val _ =
    if length (URust_Type_Mappings.entry_backend_parameter_sorts entry) = 2 andalso
       length (Term.add_tvars (URust_Item_Scope.constructor_scheme constructor) []) = 2
    then ()
    else error "merged locale lost its native pointer constructor scheme"
end
\<close>

end

ML_val\<open>
  val _ =
    if is_none (URust_Type_Mappings.lookup \<^context> "LocalePointer") andalso
       is_none (URust_Type_Mappings.lookup \<^context> "LocalePointerPacket")
    then ()
    else error "locale pointer registrations escaped their target"
\<close>

chapter\<open> Generic datatypes and backend selection \<close>

section\<open> Generic declarations and backend selection \<close>

declare [[urust_pretty = false, urust_verbosity = 0]]

urust_datatype \<open> struct Buffer<T, const N: usize> { values: [T; N] } \<close>

urust_datatype \<open> struct Envelope<T, const N: usize, P> { buffer: Buffer<T, N> } \<close>

urust_datatype \<open> struct GenericUnit<T, U, const N: usize>; \<close>

urust_datatype \<open> struct GenericTuple<T, U, const N: usize>(u32); \<close>

urust_datatype \<open> struct EmptyNamed<T> {} \<close>

urust_datatype \<open> struct EmptyTuple<T>(); \<close>

urust_datatype [parameters = ["T" \<rightarrow> "'element::ord"]] \<open>
  struct SortedHint<T>;
\<close>

\<comment>\<open>RUST-CHANGE: this proof-source mirror omits a PhantomData field and its pure
initializer/pattern slot. The original type parameter is retained. Automatic field handling is
not requested; effectful initializers would need explicit effect-preserving source adaptation.\<close>

urust_datatype \<open> struct TaggedAddress<T> { address: u64 } \<close>

urust_type "Sized<'a, const 'n>" = \<open>('a, 'n::len) array\<close>

urust_datatype \<open> struct MappedBuffer<T, const N: usize> { values: Sized<T, N> } \<close>

urust_type_alias \<open> type ConcreteBuffer = Buffer<u8, 0x10>; \<close>

urust_type_alias \<open> type ForwardBuffer<T, const N: usize> = Buffer<T, N>; \<close>

urust_type_alias \<open> type UnusedWidth<const N: usize> = u8; \<close>

urust_datatype [parameters = ["N" \<rightarrow> "'length::len"]] \<open>
  struct IndirectBuffer<T, const N: usize> { inner: ForwardBuffer<T, N> }
\<close>

urust_datatype [parameters = ["T" \<rightarrow> "'element", "P" \<rightarrow> "'tag"]] \<open>
  enum Choice<T, P> { Empty, Data(T), Named { value: T, active: bool } }
\<close>

urust_datatype \<open> enum Ordinary<T, P, const N: usize> { One, Two, Three } \<close>

urust_datatype [backend = hol] \<open> enum NativeChoice<T, P> { NativeEmpty, NativeData(T) } \<close>

urust_datatype [backend = "enum"] \<open> enum Single<T, P> { Only(T) } \<close>

urust_datatype \<open> #[repr(u8)] enum Status<T, P> { Idle, Ready = 7, Busy } \<close>

urust_datatype [backend = "simple_word_enum", word_width = 16,
  plugins = (plugins only: word_conversion)] \<open>
  enum ExplicitWord { Zero, Gap = 0xff, Next }
\<close>

urust_datatype [word_width = 8] \<open> enum Boundary { Min = 0, Max = 255 } \<close>

urust_datatype [word_width = 8, renames = ["On" \<rightarrow> "ModelOn"]] \<open>
  enum RenamedWord<T, const N: usize> { Off, On = 3 }
\<close>

urust_datatype [word_width = 8] model_flags \<open>
  enum SourceFlags<T, P> { FlagOff, FlagOn = 5 }
\<close>

urust_datatype [renames = ["Wrapped" \<rightarrow> "ModelWrapped"]] \<open>
  enum RenamedPayload<T, P> { Wrapped { value: T } }
\<close>

urust_datatype [parameters = ["T" \<rightarrow> "'a", "P" \<rightarrow> "'b"]] \<open>
  enum ParameterNames<T, P> { ParameterValue(T), ParameterEmpty }
\<close>

urust_datatype \<open>
  enum EmptyShapes<T, const N: usize> { EmptyUnit, EmptyPositional(), EmptyFields {} }
\<close>

urust_datatype [backend = hol] \<open>
  enum NativeShapes<T, const N: usize> { NativeUnit, NativePositional(T), NativeFields { item: T } }
\<close>

urust_datatype [word_width = 8] \<open>
  enum WordShapes<T, const N: usize> { WordUnit, WordPositional(), WordFields {} }
\<close>

lemma buffer_selector: \<open>buffer_values (make_buffer xs) = xs\<close> by simp

lemma tagged_selector: \<open>tagged_address_address (make_tagged_address n) = n\<close> by simp

lemma word_gaps: \<open>explicit_word_to_u16_pure Gap = 255\<close>
  \<open>explicit_word_to_u16_pure Next = 256\<close>
  by (simp_all add: explicit_word_to_u16_pure_alt explicit_word_rep_defs)

urust_expr constructed_tag \<open> TaggedAddress::<u8> { address: 5u64 } \<close>

urust_expr constructed_fixed_array \<open>
  Buffer::<u8, 4> { values: \<llangle>array_constant (0 :: 8 word)\<rrangle> }
\<close>

urust_expr constructed_tuple \<open> GenericTuple::<u8, u16, 0>(3u32) \<close>

urust_expr unused_unit \<open> GenericUnit::<u8, u16, 0> \<close>

urust_expr empty_named_value \<open> EmptyNamed::<u8> {} \<close>

urust_expr empty_tuple_value \<open> EmptyTuple::<u8>() \<close>

urust_expr word_value \<open> Status::<u8, u16>::Ready \<close>

urust_expr word_conversion \<open> Status::to_u8(Status::<u8, u16>::Busy) \<close>

urust_expr renamed_word_value \<open> RenamedWord::<u8, 0>::On \<close>

urust_expr renamed_word_conversion \<open> RenamedWord::to_u8(RenamedWord::<u8, 0>::On) \<close>

urust_expr explicit_binding_conversion \<open> SourceFlags::to_u8(SourceFlags::<u8, u16>::FlagOn) \<close>

urust_expr renamed_payload_value \<open> RenamedPayload::<u32, u8>::Wrapped { value: 7u32 } \<close>

urust_expr named_choice \<open> Choice::<u32, u8>::Named { active: true, value: 3u32 } \<close>

urust_expr mixed_match \<open>
  match Choice::<u32, u8>::Data(3u32) {
    Choice::Empty => 0u32,
    Choice::Data(n) => n,
    Choice::Named { value, active: _ } => value,
  }
\<close>

urust_expr typed_pattern \<open>
  match Choice::<u32, u8>::Data(3u32) { Choice::<u32, u8>::Data(value) => value, _ => 0u32 }
\<close>

urust_expr parameter_names_match \<open>
  match ParameterNames::<u8, u16>::ParameterValue(1u8) {
    ParameterNames::ParameterValue(value) => value,
    ParameterNames::ParameterEmpty => 0u8,
  }
\<close>

urust_expr word_match \<open>
  match Status::<u8, u16>::Ready { Status::Idle => 0u8, Status::Ready => 7u8, Status::Busy => 8u8 }
\<close>

urust_expr empty_shape_match \<open>
  match (EmptyShapes::<u8, 0>::EmptyFields {}) {
    EmptyShapes::EmptyUnit => 0u8,
    EmptyShapes::EmptyPositional() => 1u8,
    EmptyShapes::EmptyFields {} => 2u8,
  }
\<close>

urust_expr native_shape_match \<open>
  match (NativeShapes::<u8, 0>::NativeFields { item: 3u8 }) {
    NativeShapes::NativeUnit => 0u8,
    NativeShapes::NativePositional(item) => item,
    NativeShapes::NativeFields { item } => item,
  }
\<close>

urust_expr word_shape_match \<open>
  match WordShapes::<u8, 0>::WordPositional() {
    WordShapes::WordUnit => 0u8,
    WordShapes::WordPositional() => 1u8,
    WordShapes::WordFields {} => 2u8,
  }
\<close>

urust_fn tagged_field \<open> fn tagged_field(x: TaggedAddress<u8>) -> u64 { x.address } \<close>

urust_fn buffer_identity \<open> fn buffer_identity(x: Buffer<u8, 4>) -> Buffer<u8, 4> { x } \<close>

urust_fn buffer_field \<open> fn buffer_field(x: Buffer<u8, 4>) -> [u8; 4] { x.values } \<close>

urust_fn forwarded_signature \<open>
  fn forwarded_signature(x: ForwardBuffer<u8, 0x10>) -> Buffer<u8, 16> { x }
\<close>

urust_fn unused_const_alias \<open>
  fn unused_const_alias(x: UnusedWidth<0>) -> UnusedWidth<16> { x }
\<close>

urust_type "Maybe<'a>" = \<open>'a option\<close>

urust_type "LooseConst<const 'n>" = \<open>'n option\<close>

urust_expr nested_type_constructor \<open> Choice::<Maybe<u8>, u16>::Data(Some(2u8)) \<close>

urust_expr escaped_type_constructor \<open>
  Choice::<\<tau>\<open>nat\<close>, u8>::Data(\<llangle>3 :: nat\<rrangle>)
\<close>

urust_expr escaped_length_constructor (xs) \<open> Buffer::<u8, \<tau>\<open>4\<close>> { values: xs } \<close>

urust_expr underscore_length (xs) \<open> Buffer::<u8, 1_6> { values: xs } \<close>

urust_expr_rejects \<open> Choice::<u8, u16>::Data(5u16) \<close> \<open>Type unification failed\<close>

urust_datatype \<open>
  struct GenericPointer<T, P, const N: usize> { pointer: *const T, values: Buffer<T, N> }
\<close>

urust_datatype \<open> enum PointerPayload<T, P> { Raw(*const T), PointerEmpty } \<close>

urust_fn generic_pointer_identity \<open>
  fn generic_pointer_identity(x: GenericPointer<u8, u16, 4>) -> GenericPointer<u8, u16, 4> { x }
\<close>

urust_fn pointer_payload \<open>
  fn pointer_payload(pointer: *const u8) -> PointerPayload<u8, u16> { PointerPayload::<u8, u16>::Raw(pointer) }
\<close>

ML_val \<open>
local
  val thy = \<^theory>
  val ctxt = \<^context>
  fun require message condition = if condition then () else error message
  fun mapping name = the (URust_Type_Mappings.lookup ctxt name)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun command label text =
    Outer_Syntax.parse_text thy (K thy)
      (Position.make0 1 1 0 "" label "" |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false)
      transitions (Toplevel.make_state (SOME thy)))
  fun rejection (label, options, source, expected) =
    (case Exn.result (fn () => command label
      ("urust_datatype " ^ options ^ " " ^ cartouche source)) () of
      Exn.Res _ => error ("invalid datatype accepted: " ^ label)
    | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
      else require ("wrong diagnostic for " ^ label ^ ": " ^ Runtime.exn_message exn)
        (String.isSubstring expected (Runtime.exn_message exn)))
  val _ = List.app rejection
    [("word-no-width", "[backend = \"simple_word_enum\"]", "enum Invalid { First, Second }", "explicit width"),
     ("word-payload", "[backend = \"simple_word_enum\", word_width = 8]", "enum Invalid { Stored(u8) }", "no payload"),
     ("struct-enum", "[backend = \"enum\"]", "struct Invalid;", "require an enum"),
     ("width-conflict", "[word_width = 16]", "#[repr(u8)] enum Invalid { First }", "conflicts"),
     ("width-hol", "[backend = hol, word_width = 8]", "enum Invalid { First }", "requires"),
     ("unsupported-repr", "", "#[repr(i8)] enum Invalid { First }", "unsupported repr"),
     ("usize-repr", "", "#[repr(usize)] enum Invalid { First }", "unsupported repr"),
     ("explicit-overflow", "[word_width = 8]", "enum Invalid { First = 256 }", "out of range"),
     ("implicit-overflow", "[word_width = 8]", "enum Invalid { First = 255, Second }", "out of range"),
     ("duplicate-discriminant", "[word_width = 8]", "enum Invalid { First = 7, Second = 7 }", "duplicate discriminant"),
     ("recursive-generic", "", "struct Invalid<T>(Invalid<T>);", "recursive"),
     ("const-kind", "", "struct Invalid<T> { value: Buffer<u8, T> }", "type parameters used as const"),
     ("type-kind", "", "struct Invalid<const N: usize> { value: Maybe<N> }", "const parameters used as type"),
     ("const-minimum-sort", "", "struct Invalid { value: LooseConst<\<tau>\<open>nat\<close>> }", "does not satisfy sort"),
     ("const-field", "", "struct Invalid<const N: usize> { value: N }", "const parameters used as field"),
     ("zero-array", "", "struct Invalid { value: [u8; 0] }", "does not satisfy sort"),
     ("override-sort", "[parameters = [\"N\" \<rightarrow> \"'n::len0\"]]",
       "struct Invalid<const N: usize> { value: [u8; N] }", "does not satisfy inferred sort"),
     ("override-unknown", "[parameters = [\"X\" \<rightarrow> \"'x\"]]", "struct Invalid<T>;", "unknown parameter override"),
     ("override-duplicate-name", "[parameters = [\"T\" \<rightarrow> \"'x\", \"U\" \<rightarrow> \"'x\"]]",
       "struct Invalid<T, U>;", "HOL parameter names must be distinct"),
     ("automatic-marker", "", "struct Invalid<T> { value: PhantomData<T> }", "automatic PhantomData field handling is deferred"),
     ("qualified-marker", "", "struct Invalid<T> { value: core::marker::PhantomData<T> }", "automatic PhantomData field handling is deferred"),
     ("word-marker-payload", "[word_width = 8]", "enum Invalid<T> { Value(PhantomData<T>) }", "automatic PhantomData field handling is deferred")]
  val _ = List.app (fn (name, count) => require ("declared parameters were dropped: " ^ name)
    (length (URust_Type_Mappings.entry_parameter_sorts (mapping name)) = count))
    [("GenericUnit", 3), ("GenericTuple", 3), ("EmptyNamed", 1), ("EmptyTuple", 1),
     ("Ordinary", 3), ("NativeChoice", 2), ("Single", 2), ("Status", 2), ("RenamedWord", 2)]
  val _ = List.app (fn name => require ("unused shape parameter was dropped: " ^ name)
    (URust_Type_Mappings.entry_parameter_sorts (mapping name) = [\<^sort>\<open>type\<close>, \<^sort>\<open>len0\<close>]))
    ["EmptyShapes", "NativeShapes", "WordShapes"]
  val _ = require "const length sort was not inferred"
    (nth (URust_Type_Mappings.entry_parameter_sorts (mapping "Buffer")) 1 = \<^sort>\<open>len\<close>)
  val _ = require "unused word const parameter lost len0"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "RenamedWord") = [\<^sort>\<open>type\<close>, \<^sort>\<open>len0\<close>])
  val _ = require "unused alias const parameter was dropped"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "UnusedWidth") = [\<^sort>\<open>len0\<close>])
  val _ = require "explicit unused sorted parameter introduced an implicit memory parameter"
    (URust_Type_Mappings.entry_parameter_sorts (mapping "SortedHint") = [\<^sort>\<open>ord\<close>] andalso
     null (URust_Type_Mappings.entry_backend_parameter_sorts (mapping "SortedHint")))
  val _ = require "unused parameters acquired equality constraints"
    (Sign.of_sort thy (\<^typ>\<open>(nat \<Rightarrow> nat, nat \<Rightarrow> nat, 0) ordinary\<close>, \<^sort>\<open>equal\<close>))
  val _ = require "ordinary enum used a HOL datatype"
    (is_none (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>ordinary\<close>))
  val _ = require "HOL backend lost native constructor metadata"
    (is_some (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>native_choice\<close>))
  val _ = require "repr enum did not use a word typedef"
    (not (null (Typedef.get_info ctxt \<^type_name>\<open>status\<close>)))
  val _ = require "source and memory parameters were conflated"
    (length (URust_Type_Mappings.entry_parameter_sorts (mapping "GenericPointer")) = 3 andalso
     length (URust_Type_Mappings.entry_backend_parameter_sorts (mapping "GenericPointer")) = 2)
  val _ = require "temporary overloaded setting escaped"
    (not (Config.get ctxt Typedef.overloaded) andalso not (Config.get_global thy Typedef.overloaded))
  val _ = require "duplicate word notation registration"
    (null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral "Status::Ready"))
  val recovered = command "backend-recovery"
    ("urust_datatype [word_width = 8] " ^ cartouche "enum Invalid { Recovered = 255 }") |> Toplevel.context_of
  val _ = require "failed declarations left registry state"
    (is_some (URust_Type_Mappings.lookup recovered "Invalid") andalso is_none (URust_Type_Mappings.lookup ctxt "Invalid"))
in val _ = writeln "unified generic datatype probes passed" end
\<close>

section\<open> Ordinary explicit singleton modelling \<close>

text\<open>No builtin mapping or field policy is installed for PhantomData. An ordinary HOL datatype,
manual type mapping and literal notation can model it as a stored singleton field.\<close>

datatype 'a explicit_token = ExplicitToken

urust_type "PhantomData<'a>" = \<open>'a explicit_token\<close>

urust_notation (literal) ExplicitToken ("PhantomData")

urust_datatype \<open> struct ManualCarrier<T> { value: u8, token: PhantomData<T> } \<close>

urust_expr manual_carrier \<open> ManualCarrier::<u8> { token: PhantomData, value: 5u8 } \<close>

urust_expr stored_token_abort \<open>
  ManualCarrier::<u8> { token: { assert!(false); PhantomData }, value: 5u8 }
\<close>

urust_expr stored_token_order \<open>
  ManualCarrier::<u8> {
    token: { \<epsilon>\<open>put (\<lambda>_::nat. 1)\<close>; PhantomData },
    value: { \<epsilon>\<open>put (\<lambda>_::nat. 2)\<close>; 5u8 },
  }
\<close>

lemma stored_token_abort_preserved: \<open>stored_token_abort = abort AssertionFailed\<close>
  by (simp add: stored_token_abort_def micro_rust_simps assert_def assert_val_def
    sequence_def false_def literal_def abort_def Core_Expression.bind.simps evaluate_def)

lemma stored_token_source_order:
  \<open>evaluate stored_token_order 0 = Success (make_manual_carrier 5 ExplicitToken) 2\<close>
  by (simp add: stored_token_order_def micro_rust_simps sequence_def evaluate_def
    literal_def put_def Core_Expression.bind.simps)

urust_expr_rejects \<open> ManualCarrier::<u8> { value: 5u8 } \<close> \<open>missing field "token"\<close>

urust_expr_rejects \<open>
  ManualCarrier::<u8> { value: 5u8, token: PhantomData, extra: { assert!(false); 0u8 } }
\<close> \<open>unknown field "extra"\<close>

urust_expr_rejects \<open>
  ManualCarrier::<u8> { value: 5u8, token: PhantomData, token: PhantomData }
\<close> \<open>duplicate struct initializer\<close>

urust_fn manual_token \<open> fn manual_token(x: ManualCarrier<u8>) -> PhantomData<u8> { x.token } \<close>

urust_fn manual_pattern \<open>
  fn manual_pattern(x: ManualCarrier<u8>) -> PhantomData<u8> { match x { ManualCarrier { value: _, token } => token } }
\<close>

urust_datatype \<open> #[repr(u8)] enum MappedStatus<T> { MappedReady(PhantomData<T>) = 7, MappedBusy } \<close>

ML_val \<open>
  val ctxt = \<^context>
  val carrier = the (URust_Item_Scope.lookup_constructor ctxt "ManualCarrier")
  val _ = if length (binder_types (fastype_of (URust_Item_Scope.constructor_scheme carrier))) = 2
    andalso length (URust_Item_Scope.constructor_fields carrier) = 2 then ()
    else error "manually mapped singleton field was discarded"
  val _ = if is_none (Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>mapped_status\<close>) andalso
    length (binder_types (fastype_of (URust_Item_Scope.constructor_scheme
      (the (URust_Item_Scope.lookup_constructor ctxt "MappedStatus::MappedReady"))))) = 1
    then () else error "a stored singleton payload made an enum eligible for word representation"
  val source = Parser_Lex_Util.text_source "enum StoredPayload<T> { Stored(PhantomData<T>) }"
  val result = Exn.result (URust_Datatype.define
    {source = source, explicit_binding = NONE, interactive = false, verbosity = 0,
     pp_test = true, pretty = false, register_notation = true, renames = [],
     unprefixed_selectors = NONE,
     backend = "simple_word_enum", word_width = SOME 8, parameters = [], plugins = K Plugin_Name.default_filter})
      (Named_Target.theory_init \<^theory>)
  val _ = case result of Exn.Res _ => error "explicit word backend discarded a stored singleton payload"
    | Exn.Exn exn => if String.isSubstring "no payload" (Runtime.exn_message exn) then ()
      else Exn.reraise exn
\<close>

section\<open> Generic manifests and read-only pretty replay \<close>

ML_val \<open>
local
  val thy = \<^theory>
  fun require message condition = if condition then () else error message
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun probe (rust_name, backend_options, declaration, backend, count) =
    let
      val label = "unified-replay-" ^ rust_name
      val output = Synchronized.var label ([]: string list)
      fun collect chunks =
        if Position.file_of (Position.thread_data ()) = SOME label
        then Synchronized.change output (append chunks) else ()
      fun run () =
        Outer_Syntax.parse_text thy (K thy) (Position.line_file 1 label)
          ("urust_datatype [pretty, pp_test, verbosity = 2" ^ backend_options ^ "] " ^
            cartouche declaration)
        |> (fn transitions => fold (Toplevel.command_exception true)
          transitions (Toplevel.make_state (SOME thy)))
      val state = Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.writeln_fn collect run ())
      val ctxt = Toplevel.context_of state
      val plain = XML.content_of (YXML.parse_body (implode (Synchronized.value output)))
        |> Symbol.explode |> filter_out Symbol.is_control |> implode
      val _ = List.app (fn text => require ("generic manifest omitted " ^ quote text)
        (String.isSubstring text plain))
        ["backend: " ^ backend, "T ->", "P ->", "const N ->", "len0",
         "normalized uRust declaration", "normalized generated declaration"]
      val mapping = the (URust_Type_Mappings.lookup ctxt rust_name)
      val _ = require "pretty replay changed the complete parameter scheme"
        (length (URust_Type_Mappings.entry_parameter_sorts mapping) = 3 andalso
         length (URust_Type_Mappings.entry_backend_parameter_sorts mapping) = count)
      val _ = require "pretty replay registered the item twice"
        (length (URust_Item_Scope.dump_types ctxt) = length (URust_Item_Scope.dump_types \<^context>) + 1)
      val _ = require "pretty replay registered constructors twice"
        (length (URust_Item_Scope.dump_constructors ctxt) =
          length (URust_Item_Scope.dump_constructors \<^context>) + (if backend = "hol" then 1 else 2))
      val generated = String.fields (fn c => c = #"\n") plain
        |> drop_prefix (not o String.isPrefix "normalized generated declaration")
        |> space_implode "\n"
      val _ = require "verbose output lost unused HOL parameters"
        (String.isSubstring "'p" generated andalso String.isSubstring "'n" generated)
    in () end
  val _ = List.app probe
    [("ReplayRecord", "", "struct ReplayRecord<T, P, const N: usize> { value: T, pointer: *const T }", "hol", 2),
     ("ReplayCustom", "", "enum ReplayCustom<T, P, const N: usize> { ReplayValue(T), ReplayEmpty }", "enum", 0),
     ("ReplayHol", ", backend = hol", "struct ReplayHol<T, P, const N: usize>(T);", "hol", 0),
     ("ReplayWord", ", word_width = 8", "enum ReplayWord<T, P, const N: usize> { ReplayOff, ReplayOn = 9 }", "simple_word_enum", 0)]
in val _ = writeln "generic manifests and read-only pretty replay passed" end
\<close>

locale unified_declaration_scope = fixes scope_marker :: nat
begin
urust_datatype \<open> enum LocalChoice<T, P> { LocalValue(T), LocalEmpty } \<close>
urust_datatype [word_width = 8] \<open> enum LocalWord<T> { LocalOff, LocalOn = 9 } \<close>
urust_datatype \<open> struct LocalTagged<T> { value: u8 } \<close>
urust_expr local_choice \<open> LocalChoice::<u8, u16>::LocalValue(4u8) \<close>
urust_expr local_word \<open> LocalWord::<u16>::LocalOn \<close>
urust_fn local_field \<open> fn local_field(x: LocalTagged<u8>) -> u8 { x.value } \<close>
end

chapter\<open> Rust type mappings \<close>

section\<open> Extensible Rust-to-HOL type mappings \<close>

urust_type "PacketId" = \<open>64 word\<close>

urust_type "transport::PacketFlag" = \<open>bool\<close>

urust_type "ResultMap<'ok, 'err>" = \<open>('ok, 'err) result\<close>

urust_type "Wrap<'value>" = \<open>'value option\<close>

urust_type "Ordered<'value>" = \<open>'value::linorder list\<close>

urust_type "wire::Envelope<'header>::Body<'payload>" =
  \<open>('header, 'payload) result\<close>

urust_type "FunctionType" = \<open>nat \<Rightarrow> nat\<close>

urust_type "u128" = \<open>128 word\<close>

urust_type "AlphaMap<'left, 'right>" =
  \<open>('left, 'right) result\<close>

urust_type "AlphaMap<'x, 'y>" =
  \<open>('x, 'y) result\<close>

urust_datatype \<open>
  struct MappedTypes {
    identifier: PacketId,
    flag: transport::PacketFlag,
    outcome: ResultMap<PacketId, bool>,
    nested: Wrap<Wrap<Wrap<u8>>>,
    commented: ResultMap<
      /* first */ Wrap<u16>,
      // second
      Wrap<bool>,
    >,
    segmented: wire::Envelope<u8>::Body<PacketId>,
    wide: u128,
    unit: (),
    grouped: (PacketId),
    pair: (u8, bool),
  }
\<close>

urust_datatype \<open>
  struct MappedTupleTypes {
    flat: (u8, bool, PacketId),
    flat_four: (u8, bool, PacketId, Wrap<u16>),
    nested_tuple: (u8, (bool, PacketId)),
    generic_tuple: (Wrap<u8>, PacketId),
    escaped_tuple: (PacketId, \<tau>\<open>nat\<close>),
    escaped: \<tau>\<open>nat option\<close>,
  }
\<close>

urust_datatype \<open>
  struct TupleArity16((
    u8, u8, u8, u8, u8, u8, u8, u8,
    u8, u8, u8, u8, u8, u8, u8, u8,
  ));
\<close>

urust_datatype \<open>
  struct TupleArity17((
    u8, u8, u8, u8, u8, u8, u8, u8,
    u8, u8, u8, u8, u8, u8, u8, u8, u8,
  ));
\<close>

urust_datatype explicit_mapped_hol \<open>
  enum MappedChoice {
    Empty,
    Payload(PacketId),
  }
\<close>

urust_datatype \<open>
  struct UsesGenerated(MappedTypes, MappedTupleTypes, MappedChoice);
\<close>

datatype ordinary_type_registry_control =
  Ordinary_Type_Registry_Control

bundle scoped_type_mapping
begin

urust_type "ScopedType" = \<open>nat\<close>

end

bundle conflicting_type_mapping_left
begin

urust_type "BundleConflict" = \<open>nat\<close>

end

bundle conflicting_type_mapping_right
begin

urust_type "BundleConflict" = \<open>bool\<close>

end

context includes scoped_type_mapping
begin

urust_datatype \<open>
  struct ScopedTypeHolder(ScopedType);
\<close>

end

locale type_mapping_left
begin

urust_type "LocaleType" = \<open>nat\<close>

urust_datatype \<open>
  struct LocaleTypeHolder(LocaleType);
\<close>

end

locale type_mapping_right
begin

urust_type "LocaleType" = \<open>bool\<close>

urust_datatype \<open>
  struct LocaleTypeHolder(LocaleType);
\<close>

end

section\<open> Registry and generated-type audits \<close>

ML_val \<open>
  local
    val expected =
      [("u8", \<^typ>\<open>8 word\<close>),
       ("u16", \<^typ>\<open>16 word\<close>),
       ("u32", \<^typ>\<open>32 word\<close>),
       ("u64", \<^typ>\<open>64 word\<close>),
       ("usize", \<^typ>\<open>64 word\<close>),
       ("i32", \<^typ>\<open>32 word\<close>),
       ("i64", \<^typ>\<open>64 word\<close>),
       ("bool", \<^typ>\<open>bool\<close>),
       ("()", \<^typ>\<open>unit\<close>)]

    fun check (name, typ) =
      (case URust_Type_Mappings.lookup \<^context> name of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry = typ andalso
               URust_Type_Mappings.entry_arities entry = [0] andalso
               null
                 (URust_Type_Mappings.entry_parameter_sorts entry) andalso
               URust_Type_Mappings.entry_origin entry =
                 "urust_type declaration"
           then ()
           else
             error
               ("unexpected built-in uRust type mapping for " ^
                 quote name)
       | NONE =>
           error
             ("missing built-in uRust type mapping for " ^
               quote name))

    val _ = List.app check expected
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun run source_name command_text () =
      let
        val thy = \<^theory>\<open>Parser_Test_Utils\<close>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    val command_text =
      "urust_datatype before_u128 " ^
        cartouche " struct BeforeU128(u128); "
    val _ =
      (case Exn.result (run "before-u128" command_text) () of
         Exn.Res _ =>
           error "u128 unexpectedly resolved before registration"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring
               "unknown Rust type \"u128\"" (Runtime.exn_message exn)
           then ()
           else
             error
               ("unexpected pre-registration u128 diagnostic: " ^
                 Runtime.exn_message exn))
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  val SOME alpha =
    URust_Type_Mappings.lookup \<^context> "AlphaMap"
  val _ =
    if URust_Type_Mappings.entry_arities alpha = [2] andalso
        length
          (URust_Type_Mappings.entry_parameter_sorts alpha) = 2
    then ()
    else error "alpha-normalized mapping metadata changed"
\<close>

ML_val \<open>
  local
    fun require_sugar name =
      (case Ctr_Sugar.ctr_sugar_of \<^context> name of
         SOME sugar => sugar
       | NONE => error ("missing generated datatype " ^ quote name))

    fun argument_types name =
      let
        val sugar = require_sugar name
      in
        (case #ctrs sugar of
           [Const (constructor, _)] =>
             binder_types
               (Consts.the_constraint
                 (Proof_Context.consts_of \<^context>) constructor)
         | _ => error "expected one generated constructor")
      end

    fun tuple_elements typ =
      if typ = \<^typ>\<open>tnil\<close> then []
      else
        (case try HOLogic.dest_prodT typ of
           SOME (head, tail) => head :: tuple_elements tail
         | NONE => error "expected a tnil-terminated tuple type")

    val mapped = argument_types \<^type_name>\<open>mapped_types\<close>
    val _ =
      if mapped =
          [\<^typ>\<open>64 word\<close>,
           \<^typ>\<open>bool\<close>,
           \<^typ>\<open>(64 word, bool) result\<close>,
           \<^typ>\<open>8 word option option option\<close>,
           \<^typ>\<open>(16 word option, bool option) result\<close>,
           \<^typ>\<open>(8 word, 64 word) result\<close>,
           \<^typ>\<open>128 word\<close>,
           \<^typ>\<open>unit\<close>,
           \<^typ>\<open>64 word\<close>,
           \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>]
      then ()
      else error "registry-backed datatype field resolution changed"

    val mapped_tuples =
      argument_types \<^type_name>\<open>mapped_tuple_types\<close>
    val _ =
      if mapped_tuples =
          [\<^typ>\<open>8 word \<times> bool \<times> 64 word \<times> tnil\<close>,
           \<^typ>\<open>8 word \<times> bool \<times> 64 word \<times> 16 word option \<times> tnil\<close>,
           \<^typ>\<open>8 word \<times> (bool \<times> 64 word \<times> tnil) \<times> tnil\<close>,
           \<^typ>\<open>8 word option \<times> 64 word \<times> tnil\<close>,
           \<^typ>\<open>64 word \<times> nat \<times> tnil\<close>,
           \<^typ>\<open>nat option\<close>]
      then ()
      else error "registry-backed tuple field resolution changed"

    val [tuple16] =
      argument_types \<^type_name>\<open>tuple_arity16\<close>
    val [tuple17] =
      argument_types \<^type_name>\<open>tuple_arity17\<close>
    val _ =
      if length (tuple_elements tuple16) = 16 andalso
          length (tuple_elements tuple17) = 17
      then ()
      else error "large Rust tuple encoding changed"
    val _ =
      if tuple16 = tuple17
      then error "tuple arities 16 and 17 collapsed"
      else ()

    val _ =
      (case URust_Type_Mappings.lookup \<^context> "MappedTypes" of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry =
               \<^typ>\<open>mapped_types\<close>
           then ()
           else error "generated struct mapping has the wrong HOL type"
       | NONE => error "generated struct did not register a type mapping")
    val _ =
      (case URust_Type_Mappings.lookup \<^context> "MappedChoice" of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry =
               \<^typ>\<open>explicit_mapped_hol\<close>
           then ()
           else error "generated enum mapping has the wrong HOL type"
       | NONE => error "generated enum did not register a type mapping")
    val _ =
      if argument_types \<^type_name>\<open>uses_generated\<close> =
          [\<^typ>\<open>mapped_types\<close>,
           \<^typ>\<open>mapped_tuple_types\<close>,
           \<^typ>\<open>explicit_mapped_hol\<close>]
      then ()
      else error "later generated-type references changed"
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup
      \<^context> "ordinary_type_registry_control"
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup \<^context> "ScopedType"
  val SOME _ =
    URust_Type_Mappings.lookup \<^context> "ScopedTypeHolder"
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup \<^context> "LocaleType"
  val NONE =
    URust_Type_Mappings.lookup \<^context> "LocaleTypeHolder"
\<close>

section\<open> Source positions and registry markup \<close>

ML_val \<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation
    val mapping_kind = "micro_rust_type_mapping"

    fun audit message condition =
      if condition then ()
      else error ("uRust type mapping markup audit: " ^ message)

    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun command_start source_name =
      Position.make0 1 1 0 "" source_name source_name

    fun run source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (command_start source_name)
            command_text
      in
        fold (Toplevel.command_exception true) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun mapping_ids property rust_name position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN =
                  SOME mapping_kind andalso
                Properties.get properties Markup.nameN =
                  SOME rust_name andalso
                has_position properties position
            then Properties.get properties property
            else NONE)
      |> distinct (op =)

    fun mapping_entities markup =
      filter
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN =
              SOME mapping_kind)
        markup

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing source token " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (Position.range
            (token_start,
             Position.symbol_explode needle token_start))
      end

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect
              (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun range_of position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    val declaration_file = "urust-type-mapping-definition"
    val declaration_text =
      "urust_type \"MarkupId\" = " ^ cartouche "nat"
    val (declaration_state, declaration_markup) =
      Parser_Test_Reports.markup
        (run declaration_file declaration_text)
    val declaration_ctxt =
      Toplevel.context_of declaration_state
      |> Context_Position.set_visible true
    val SOME mapping =
      URust_Type_Mappings.lookup declaration_ctxt "MarkupId"
    val identity =
      Value.print_int
        (URust_Type_Mappings.entry_identity mapping)
    val declaration_position =
      URust_Type_Mappings.entry_declaration_position mapping
    val _ =
      audit "declaration position lost its source file"
        (Position.file_of declaration_position =
          SOME declaration_file)
    val declaration_ids =
      mapping_ids Markup.defN "MarkupId"
        declaration_position declaration_markup
    val _ =
      audit
        ("declaration entity identity or exact range changed: " ^
          commas_quote declaration_ids ^ " from " ^
          commas_quote
            (map
              (fn (_, properties) =>
                commas
                  (map
                    (fn (name, value) => name ^ "=" ^ value)
                    properties))
              (mapping_entities declaration_markup)))
        (declaration_ids = [identity])

    val parameter_file = "urust-type-mapping-parameters"
    val parameter_text =
      "urust_type \"MarkupPair<'left, 'right>\" = " ^
        cartouche "('left, 'right) result"
    val (_, parameter_markup) =
      Parser_Test_Reports.markup
        (run parameter_file parameter_text)
    val parameter_start = command_start parameter_file
    val left_position =
      token_position parameter_text parameter_start "'left" 0
    val right_position =
      token_position parameter_text parameter_start "'right" 0
    val _ =
      audit "first mapping placeholder lost native type-variable markup"
        (count_markup Markup.tfreeN
          left_position parameter_markup = 1)
    val _ =
      audit "second mapping placeholder lost native type-variable markup"
        (count_markup Markup.tfreeN
          right_position parameter_markup = 1)

    val use_text = " struct MarkupHolder(MarkupId); "
    val use_start =
      Position.make0 41 5000 0 "" ""
        "urust-type-mapping-reference"
    val use_source =
      Parser_Lex_Util.positioned_content_source
        use_text use_start
    val SOME parsed_use =
      URust_Parser.parse_datatype_source
        declaration_ctxt use_source
    val mapped_type =
      (case parsed_use of
         URust_AST.Struct_Item
           (_, _, URust_AST.Tuple_Shape [typ], _) => typ
       | _ => error "unexpected mapping markup test AST")
    val use_position =
      URust_AST.rust_type_position mapped_type
    val expected_use_position =
      token_position use_text use_start "MarkupId" 0
    val _ =
      audit "parsed mapping-use source range changed"
        (Position.offset_of use_position =
          Position.offset_of expected_use_position andalso
         Position.end_offset_of use_position =
          Position.end_offset_of expected_use_position)
    val (resolved_type, deferred_reports) =
      Navigation.capture
        (fn () =>
          URust_Type_Mappings.resolve
            declaration_ctxt mapped_type)
    val _ =
      audit "mapped HOL type changed"
        (resolved_type = \<^typ>\<open>nat\<close>)
    val ((), use_markup) =
      Parser_Test_Reports.markup
        (fn () =>
          Navigation.replay declaration_ctxt deferred_reports)
    val _ =
      audit "mapping reference identity or exact range changed"
        (mapping_ids Markup.refN "MarkupId"
          expected_use_position use_markup = [identity])
    val _ =
      audit "mapping reference typing markup changed"
        (count_markup Markup.typingN
          expected_use_position use_markup = 1)
    val _ =
      audit "mapping reference keyword styling changed"
        (count_markup Markup.keyword3N
          expected_use_position use_markup = 1)

    val unknown_text =
      " struct PositionedUnknown(missing::Type); "
    val unknown_start =
      Position.make0 52 8000 0 "" ""
        "urust-type-mapping-diagnostic"
    val SOME parsed_unknown =
      URust_Parser.parse_datatype_source
        \<^context>
        (Parser_Lex_Util.positioned_content_source
          unknown_text unknown_start)
    val unknown_type =
      (case parsed_unknown of
         URust_AST.Struct_Item
           (_, _, URust_AST.Tuple_Shape [typ], _) => typ
       | _ => error "unexpected positioned diagnostic AST")
    val unknown_position =
      URust_AST.rust_type_position unknown_type
    val unknown_message =
      (case Exn.result
          (fn () =>
            Navigation.capture
              (fn () =>
                URust_Type_Mappings.resolve
                  \<^context> unknown_type)) () of
         Exn.Res _ =>
           error "unknown positioned type unexpectedly resolved"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    val _ =
      audit "unknown-type guidance changed"
        (String.isSubstring
          ("unknown Rust type \"missing::Type\"; " ^
           "declare it with urust_type or use")
          unknown_message)
    val _ =
      audit "unknown-type diagnostic range changed"
        (diagnostic_ranges
          (YXML.parse_body unknown_message) =
            [range_of unknown_position])

    val failure_text =
      "urust_datatype " ^
        cartouche
          (" struct MarkupFailure { " ^
           "accepted: PacketId, rejected: MissingMarkupType, } ")
    val (failure_result, failure_markup) =
      Parser_Test_Reports.markup
        (fn () =>
          Exn.result
            (run "urust-type-mapping-failure" failure_text) ())
    val _ =
      (case failure_result of
         Exn.Res _ =>
           error "failing datatype unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit "failing datatype diagnostic changed"
               (String.isSubstring
                 "unknown Rust type \"MissingMarkupType\""
                 (Runtime.exn_message exn)))
    val _ =
      audit "failed datatype emitted registry success markup"
        (null (mapping_entities failure_markup))
  in
    val _ = ()
  end
\<close>

section\<open> Diagnostics, rollback, and recovery \<close>

ML_val \<open>
  local
    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun run source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun rejected label expected command_text =
      (case Exn.result (run label command_text) () of
         Exn.Res _ =>
           error
             ("expected command rejection for " ^ quote label)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring expected
               (Runtime.exn_message exn)
           then ()
           else
             error
               ("unexpected diagnostic for " ^ quote label ^
                 "\nexpected: " ^ quote expected ^
                 "\nactual: " ^
                 Runtime.exn_message exn))

    fun accepted label command_text =
      (case Exn.result (run label command_text) () of
         Exn.Res state => state
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             error
               ("unexpected rejection for " ^ quote label ^ ": " ^
                 Runtime.exn_message exn))

    fun datatype_command name field_type =
      "urust_datatype " ^ name ^ " " ^
        cartouche
          (" struct " ^ name ^ "(" ^ field_type ^ "); ")

    fun mapping key typ =
      "urust_type " ^ quote key ^ " = " ^ cartouche typ

    val SOME alpha_before =
      URust_Type_Mappings.lookup \<^context> "AlphaMap"
    val alpha_state =
      accepted "mapping-idempotent-alpha-renaming"
        (mapping "AlphaMap<'first, 'second>"
          "('first, 'second) result")
    val SOME alpha_after =
      URust_Type_Mappings.lookup
        (Toplevel.context_of alpha_state) "AlphaMap"
    val _ =
      if URust_Type_Mappings.entry_identity alpha_before =
          URust_Type_Mappings.entry_identity alpha_after
      then ()
      else error "idempotent mapping registration changed identity"

    val _ =
      rejected "mapping-template-conflict"
        "conflicting active mappings for \"PacketId\""
        (mapping "PacketId" "32 word")
    val _ =
      rejected "mapping-arity-conflict"
        "different generic arity"
        (mapping "PacketId<'a>" "'a")
    val _ =
      rejected "mapping-missing-placeholder"
        "missing \"'b\""
        (mapping "Missing<'a, 'b>" "'a option")
    val _ =
      rejected "mapping-extra-placeholder"
        "undeclared \"'b\""
        (mapping "Extra<'a>" "('a, 'b) result")
    val _ =
      rejected "mapping-duplicate-placeholder"
        "mapping placeholders must be distinct"
        (mapping "Duplicate<'a, 'a>" "'a option")
    val _ =
      rejected "mapping-malformed-parameters"
        "malformed Rust type key"
        (mapping "Malformed<'a,,>" "'a")
    val _ =
      rejected "builtin-override"
        "conflicting active mappings for \"u8\""
        (mapping "u8" "nat")
    val _ =
      rejected "bundle-conflict"
        "conflicting active mappings for \"BundleConflict\""
        ("context includes conflicting_type_mapping_left\n" ^
          "begin\n" ^
          "context includes conflicting_type_mapping_right\n" ^
          "begin\n" ^
          "end\n" ^
          "end")

    val _ =
      rejected "unknown-path"
        "unknown Rust type \"missing::Type\""
        (datatype_command "UnknownPath" "missing::Type")
    val _ =
      rejected "unknown-str"
        "unknown Rust type \"str\""
        (datatype_command "UnknownStr" "str")
    val _ =
      rejected "unknown-never"
        "unknown Rust type \"!\""
        (datatype_command "UnknownNever" "!")
    val _ =
      rejected "wrong-generic-arity"
        "active urust_type mapping expects [2]"
        (datatype_command "WrongArity" "ResultMap<u8>")
    val _ =
      rejected "numeric-generic"
        "numeric generic arguments for type parameters is not supported"
        (datatype_command "NumericGeneric" "Wrap<4>")
    val _ =
      rejected "wrong-sort"
        "does not satisfy sort"
        (datatype_command "WrongSort" "Ordered<FunctionType>")
    val _ =
      rejected "singleton-tuple"
        "singleton tuple types is not supported"
        (datatype_command "SingletonTuple" "(u8,)")
    val _ =
      rejected "reference"
        "Rust reference types is not supported"
        (datatype_command "ReferenceField" "&u32")
    val _ =
      rejected "mutable-reference"
        "Rust reference types is not supported"
        (datatype_command "MutableReferenceField" "&mut u32")
    val _ =
      rejected "raw-pointer-unknown-pointee"
        "unknown Rust type \"missing::Pointee\""
        (datatype_command "RawPointerField" "*const missing::Pointee")
    val _ =
      rejected "slice"
        "Rust slice types is not supported"
        (datatype_command "SliceField" "[u8]")
    val _ =
      rejected "zero-array"
        "does not satisfy sort"
        (datatype_command "ArrayField" "[u8; 0]")
    val _ =
      rejected "recursive"
        "recursive Rust datatype reference \"RecursiveMapped\""
        (datatype_command "RecursiveMapped" "RecursiveMapped")
    val _ =
      rejected "nested-recursive"
        "recursive Rust datatype reference \"NestedRecursiveMapped\""
        (datatype_command "NestedRecursiveMapped"
          "Wrap<NestedRecursiveMapped>")
    val _ =
      rejected "enum-recursive"
        "recursive Rust datatype reference \"EnumRecursiveMapped\""
        ("urust_datatype " ^
          cartouche
            (" enum EnumRecursiveMapped { " ^
             "Again(EnumRecursiveMapped), } "))
    val _ =
      rejected "malformed-hol-escape"
        "Inner syntax error"
        (datatype_command "MalformedEscape"
          ("\<tau>" ^ cartouche "nat \<Rightarrow>"))
    val _ =
      rejected "polymorphic-hol-escape"
        "unrelated HOL variable in datatype field"
        (datatype_command "PolymorphicEscape"
          ("\<tau>" ^ cartouche "'a"))
    val _ =
      rejected "generated-mapping-conflict"
        "conflicting active mappings for \"PacketId\""
        ("urust_datatype rollback_conflict " ^
          cartouche " struct PacketId; ")
    val _ =
      rejected "generation-failure"
        "Duplicate type name declaration"
        ("urust_datatype ordinary_type_registry_control " ^
          cartouche " struct GenerationFailure; ")

    val NONE =
      URust_Type_Mappings.lookup \<^context> "UnknownPath"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "UnknownPath"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "RecursiveMapped"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "RecursiveMapped"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "EnumRecursiveMapped"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "EnumRecursiveMapped"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "GenerationFailure"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "GenerationFailure"

    val malformed =
      Parser_Lex_Util.text_source
        " struct Broken(ResultMap<Wrap<u8>,); "
    val _ =
      (case Exn.result
          (fn () =>
            URust_Parser.parse_datatype_source
              \<^context> malformed) () of
         Exn.Res _ => error "malformed generic unexpectedly parsed"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())
    val SOME _ =
      URust_Parser.parse_datatype_source \<^context>
        (Parser_Lex_Util.text_source
          " struct Recovered(ResultMap<Wrap<u8>, bool>); ")
    val SOME _ =
      URust_Parser.parse_source \<^context>
        (Parser_Lex_Util.text_source "8u32 >> 1u32")
  in
    val _ = ()
  end
\<close>

chapter\<open> Datatype selector naming \<close>

text\<open>
Selector-naming audits run each command from a fresh state of this theory, so failures leave no
declaration behind. Every rejection asserts the exact source range of its first position, which
is the key, target, field or option that explains it.
\<close>

ML\<open>
structure Selector_Name_Test =
struct
  val quiet = "declare [[urust_pp_test = false, urust_pretty = false, urust_verbosity = 0]]\n"

  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close

  fun rename_list entries =
    "[" ^ commas (map (fn (source, target) =>
      quote source ^ " \<rightarrow> " ^ quote target) entries) ^ "]"

  fun run_from start thy text =
    let
      val transitions = Outer_Syntax.parse_text thy (K thy) start (quiet ^ text)
    in
      Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
        Exn.result (fn () =>
          fold (Toplevel.command_exception true) transitions
            (Toplevel.make_state (SOME thy))) ()) ()
    end

  fun run thy label = run_from (Position.line_file 1 label) thy

  (* Output and reports of one run. Reports need a document identity in their positions. *)
  fun run_output thy label text =
    let
      val output = Synchronized.var ("selector_name_output_" ^ label) ([]: string list)
      val reports = Synchronized.var ("selector_name_reports_" ^ label) ([]: string list)
      fun collect target chunks =
        if Position.file_of (Position.thread_data ()) = SOME label
        then Synchronized.change target (append chunks) else ()
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Unsynchronized.setmp Private_Output.report_fn (collect reports) (fn () =>
            Unsynchronized.setmp Private_Output.writeln_fn (collect output) (fn () =>
              run_from (Position.make0 1 1 0 "" label label) thy text) ()) ())
      val plain =
        XML.content_of (YXML.parse_body (implode (Synchronized.value output)))
        |> Symbol.explode |> filter_out Symbol.is_control |> implode
      val markup =
        fold Parser_Test_Reports.collect_markup
          (maps YXML.parse_body (Synchronized.value reports)) []
    in {result = result, plain = plain, markup = markup} end

  fun has_definition_entity markup name (start, stop) =
    exists
      (fn (element, properties) =>
        element = Markup.entityN andalso
        Properties.get properties Markup.nameN = SOME name andalso
        is_some (Properties.get properties Markup.defN) andalso
        Properties.get properties Markup.offsetN = SOME (Value.print_int start) andalso
        Properties.get properties Markup.end_offsetN = SOME (Value.print_int stop))
      markup

  fun plain_message exn =
    XML.content_of (YXML.parse_body (Runtime.exn_message exn))

  fun message_positions exn =
    let
      fun collect (XML.Text _) = []
        | collect (XML.Elem ((name, properties), body)) =
            (if name = Markup.positionN then [Position.of_properties properties] else []) @
              maps collect body
    in maps collect (YXML.parse_body (Runtime.exn_message exn)) end

  (* The symbol range of needle in the occurrence-th occurrence of prefix ^ needle within the
     complete command text, which starts at offset 1. *)
  fun source_range text occurrence (prefix, needle) =
    let
      val whole = quiet ^ text
      val pattern = prefix ^ needle
      fun find from count =
        let
          val (preceding, rest) =
            Substring.position pattern (Substring.extract (whole, from, NONE))
          val _ =
            if Substring.isEmpty rest
            then error ("selector naming audit: missing " ^ quote pattern) else ()
          val index = from + Substring.size preceding
        in if count <= 1 then index else find (index + size pattern) (count - 1) end
      val index = find 0 occurrence + size prefix
      val start = length (Symbol.explode (String.substring (whole, 0, index))) + 1
    in (start, start + length (Symbol.explode needle)) end

  fun key_range text occurrence key = source_range text occurrence ("\"", key)

  fun succeeded thy label text =
    (case run thy label text of
       Exn.Res state => Toplevel.context_of state
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else error (label ^ " unexpectedly failed:\n" ^ plain_message exn))

  fun rejected_at thy label fragment (start, stop) text =
    (case run thy label text of
       Exn.Res _ => error (label ^ " unexpectedly succeeded")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let
             val message = plain_message exn
             val actual =
               (case message_positions exn of
                  pos :: _ =>
                    (Position.offset_of pos, Position.end_offset_of pos, Position.file_of pos)
                | [] => (NONE, NONE, NONE))
             val expected = (SOME start, SOME stop, SOME label)
             fun show (offset, end_offset, file) =
               @{make_string} (offset, end_offset, file)
           in
             if not (String.isSubstring fragment message)
             then error (label ^ " produced the wrong diagnostic:\n" ^ message)
             else if actual <> expected
             then
               error (label ^ " is positioned at " ^ show actual ^ " instead of " ^
                 show expected ^ ":\n" ^ message)
             else ()
           end)
end
\<close>

section\<open> Payload rename keys \<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    val item =
      T.cartouche " enum SelectorNameKeys { Named { value: u32 }, Pair(u32, bool), Unit } "
    fun rejected_key backend (label, key, fragment) =
      let
        val text =
          "urust_datatype [" ^ backend ^ "renames = " ^
            T.rename_list [(key, "selector_name_chosen")] ^ "] " ^ item
      in T.rejected_at thy label fragment (T.key_range text 1 key) text end
  in
    val _ =
      List.app (fn (suffix, backend) =>
        List.app (fn (label, key, fragment) =>
          rejected_key backend ("selector-name-" ^ label ^ suffix, key, fragment))
          [("unknown-variant", "Missing.value",
            "unknown rename key \"Missing.value\": enum \"SelectorNameKeys\" has no variant " ^
              "\"Missing\""),
           ("unknown-constructor", "Missing",
            "enum \"SelectorNameKeys\" has no variant \"Missing\""),
           ("path-variant", "SelectorNameKeys::Named.value",
            "has no variant \"SelectorNameKeys::Named\""),
           ("unknown-field", "Named.missing",
            "unknown rename key \"Named.missing\": variant \"Named\" has no field \"missing\""),
           ("nested-field", "Named.value.inner", "variant \"Named\" has no field \"value.inner\""),
           ("named-index", "Named.0", "variant \"Named\" has no field \"0\""),
           ("unit-payload", "Unit.0", "variant \"Unit\" has no payload fields"),
           ("unit-field", "Unit.value", "variant \"Unit\" has no payload fields"),
           ("out-of-range", "Pair.2",
            "unknown rename key \"Pair.2\": variant \"Pair\" has 2 positional fields"),
           ("large-index", "Pair.18446744073709551616", "variant \"Pair\" has 2 positional fields"),
           ("non-decimal", "Pair.first",
            "invalid rename key \"Pair.first\": tuple variant fields are named by 0-based " ^
              "decimal indices"),
           ("negative", "Pair.-1", "invalid rename key \"Pair.-1\""),
           ("leading-zero", "Pair.01", "invalid rename key \"Pair.01\""),
           ("hexadecimal", "Pair.0x1", "invalid rename key \"Pair.0x1\""),
           ("separated", "Pair.0_1", "invalid rename key \"Pair.0_1\""),
           ("empty-index", "Pair.", "invalid rename key \"Pair.\""),
           ("empty-variant", ".0", "has no variant \"\"")])
        [("-enum", ""), ("-hol", "backend = hol, ")]
  end
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    fun declaration backend entries item =
      "urust_datatype [" ^ backend ^ "renames = " ^ T.rename_list entries ^ "] " ^
        T.cartouche item
    val keys_item = " enum SelectorNameKeys { Named { value: u32 }, Pair(u32, bool), Unit } "
    val order_item = " enum SelectorNameOrder { Pair(u32), Named { value: u32 } } "
  in
    val _ =
      List.app (fn (suffix, backend) =>
        let
          val duplicate_key =
            declaration backend
              [("Pair.0", "selector_name_first"), ("Pair.0", "selector_name_second")] keys_item
          val _ =
            T.rejected_at thy ("selector-name-duplicate-key" ^ suffix)
              "duplicate rename key \"Pair.0\"" (T.key_range duplicate_key 2 "Pair.0")
              duplicate_key
          val duplicate_target =
            declaration backend
              [("Pair.0", "selector_name_same"), ("Named.value", "selector_name_same")] keys_item
          (* Effective selectors are checked in source variant order: Named, then Pair. *)
          val _ =
            T.rejected_at thy ("selector-name-duplicate-target" ^ suffix)
              "duplicate generated HOL selector \"selector_name_same\""
              (T.key_range duplicate_target 1 "selector_name_same") duplicate_target
          val default_after =
            declaration backend [("Pair.1", "selector_name_keys_named_value")] keys_item
          val _ =
            T.rejected_at thy ("selector-name-default-after" ^ suffix)
              "duplicate generated HOL selector \"selector_name_keys_named_value\""
              (T.key_range default_after 1 "selector_name_keys_named_value") default_after
          val default_before =
            declaration backend [("Pair.0", "selector_name_order_named_value")] order_item
          val _ =
            T.rejected_at thy ("selector-name-default-before" ^ suffix)
              "duplicate generated HOL selector \"selector_name_order_named_value\""
              (T.source_range default_before 1 ("{ ", "value")) default_before
          val collision =
            "urust_datatype [" ^ backend ^ "renames = [] ] " ^
              T.cartouche
                " enum SelectorNameSnake { FooBar { value: u32 }, Foo_Bar { value: bool } } "
          val _ =
            T.rejected_at thy ("selector-name-default-collision" ^ suffix)
              "duplicate generated HOL selector \"selector_name_snake_foo_bar_value\""
              (T.source_range collision 2 ("{ ", "value")) collision
          val resolved =
            declaration backend [("Foo_Bar.value", "selector_name_resolved")]
              " enum SelectorNameResolved { FooBar { value: u32 }, Foo_Bar { value: bool } } "
          val ctxt = T.succeeded thy ("selector-name-resolved" ^ suffix) resolved
          val entry =
            the (URust_Item_Scope.lookup_constructor ctxt "SelectorNameResolved::Foo_Bar")
          val _ =
            if map (apsnd (Long_Name.base_name o dest_Const_name))
                (URust_Item_Scope.constructor_fields entry) = [("value", "selector_name_resolved")]
            then () else error "a payload key did not resolve a snake-case selector collision"
        in () end)
        [("-enum", ""), ("-hol", "backend = hol, ")]
  end
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
  in
    (* Keys use the source variant name; a constructor rename neither hides nor renames them. *)
    val _ =
      List.app (fn (suffix, backend) =>
        let
          val text =
            "urust_datatype [" ^ backend ^ "renames = " ^
              T.rename_list
                [("Named", "SelectorNameModelNamed"), ("Named.value", "selector_name_value"),
                 ("Pair", "SelectorNameModelPair"), ("Pair.1", "selector_name_flag")] ^ "] " ^
              T.cartouche
                " enum SelectorNameSource { Named { value: u32, other: bool }, Pair(u32, bool) } "
          val ctxt = T.succeeded thy ("selector-name-source-variant" ^ suffix) text
          fun entry path = the (URust_Item_Scope.lookup_constructor ctxt path)
          val named = entry "SelectorNameSource::Named"
          val pair = entry "SelectorNameSource::Pair"
          val _ =
            if map (apsnd (Long_Name.base_name o dest_Const_name))
                (URust_Item_Scope.constructor_fields named) =
                [("value", "selector_name_value"), ("other", "selector_name_source_named_other")]
            then () else error ("named payload keys changed field metadata" ^ suffix)
          val _ =
            if map (Long_Name.base_name o dest_Const_name o URust_Item_Scope.constructor_term)
                [named, pair] = ["SelectorNameModelNamed", "SelectorNameModelPair"] andalso
              null (URust_Item_Scope.constructor_fields pair)
            then () else error ("constructor keys changed with payload keys" ^ suffix)
          val flag_type =
            fastype_of (Proof_Context.read_const {proper = true, strict = false} ctxt
              "selector_name_flag")
          val _ =
            if Long_Name.base_name (dest_Type_name (domain_type flag_type)) =
                "selector_name_source" andalso range_type flag_type = \<^typ>\<open>bool\<close>
            then () else error ("positional key generated the wrong selector type" ^ suffix)
        in () end)
        [("-enum", ""), ("-hol", "backend = hol, ")]

    (* simple_word_enum variants have no payload; tuple structs have no keys. *)
    val word =
      "urust_datatype [word_width = 8, renames = " ^
        T.rename_list [("On.0", "selector_name_on")] ^ "] " ^
        T.cartouche " enum SelectorNameWord { On, Off } "
    val _ =
      T.rejected_at thy "selector-name-word-key" "variant \"On\" has no payload fields"
        (T.key_range word 1 "On.0") word
    val word_field =
      "urust_datatype [renames = " ^ T.rename_list [("On.value", "selector_name_on")] ^ "] " ^
        T.cartouche " #[repr(u8)] enum SelectorNameWord { On = 1, Off = 2 } "
    val _ =
      T.rejected_at thy "selector-name-word-field" "variant \"On\" has no payload fields"
        (T.key_range word_field 1 "On.value") word_field
    val _ =
      List.app (fn (label, key) =>
        let
          val text =
            "urust_datatype [renames = " ^ T.rename_list [(key, "selector_name_first")] ^ "] " ^
              T.cartouche " struct SelectorNameTuple(u32, bool); "
        in
          T.rejected_at thy label
            ("unknown rename key " ^ quote key ^ ": struct \"SelectorNameTuple\" has only " ^
              "positional fields, and tuple struct fields have no rename keys")
            (T.key_range text 1 key) text
        end)
        [("selector-name-tuple-struct-index", "0"),
         ("selector-name-tuple-struct-qualified", "SelectorNameTuple.0")]
  end
\<close>

section\<open> Native parity of positional selectors \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    fun sugar name = the (Ctr_Sugar.ctr_sugar_of ctxt name)
    val generated = sugar \<^type_name>\<open>selector_name_parity\<close>
    val native = sugar \<^type_name>\<open>selector_name_native_parity\<close>
    fun const_names (sugar: Ctr_Sugar.ctr_sugar) =
      map_filter (try dest_Const_name)
        (#ctrs sugar @ flat (#selss sugar) @ #discs sugar @ [#casex sugar])
    val _ =
      if length (const_names generated) = length (const_names native) then ()
      else error "positional selector parity: different constructor-sugar shapes"
    val constants = const_names native ~~ const_names generated
    val native_type = dest_Type_name (#T native)
    val generated_type = dest_Type_name (#T generated)
    fun rename_type (Type (name, Ts)) =
          Type (if name = native_type then generated_type else name, map rename_type Ts)
      | rename_type T = T
    (* Ctr_Sugar names variables after the type. *)
    val native_base = Long_Name.base_name native_type
    val generated_base = Long_Name.base_name generated_type
    fun rename_variable name =
      if String.isPrefix native_base name
      then generated_base ^ unprefix native_base name else name
    fun rename (Const (name, T)) =
          Const (the_default name (AList.lookup (op =) constants name), rename_type T)
      | rename (Free (name, T)) = Free (rename_variable name, rename_type T)
      | rename (Var ((name, index), T)) = Var ((rename_variable name, index), rename_type T)
      | rename (Abs (name, T, body)) = Abs (name, rename_type T, rename body)
      | rename (t $ u) = rename t $ rename u
      | rename t = t
    fun same label native_thms generated_thms =
      if length native_thms = length generated_thms andalso
          forall (fn (n, g) => rename (Thm.prop_of n) aconv Thm.prop_of g)
            (native_thms ~~ generated_thms)
      then () else error ("positional selector parity: different " ^ label)
    val _ = same "sel facts" (flat (#sel_thmss native)) (flat (#sel_thmss generated))
    val _ = same "selector definitions" (#sel_defs native) (#sel_defs generated)
    val _ = same "collapse facts" (#collapses native) (#collapses generated)
    val _ = same "split facts" (#split_sels native) (#split_sels generated)
    val _ =
      if map rename (flat (#selss native)) = flat (#selss generated)
      then () else error "positional selector parity: different selector constants"
    val _ =
      if Long_Name.base_name (dest_Const_name (hd (hd (#selss generated)))) =
          "selector_name_parity_boxed"
      then () else error "positional selector parity: wrong selector name"
    (* The default simpset alone proves each generated sel equation. *)
    val _ =
      List.app (fn thm =>
        let val (goals, goal_ctxt) = Variable.import_terms true [Thm.prop_of thm] ctxt
        in
          ignore (Goal.prove goal_ctxt [] [] (the_single goals)
            (fn {context, ...} => simp_tac context 1))
        end)
        (flat (#sel_thmss generated))
  in end
\<close>

section\<open> Unprefixed selectors \<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    fun fields ctxt path =
      URust_Item_Scope.constructor_fields (the (URust_Item_Scope.lookup_constructor ctxt path))
      |> map (apsnd (Long_Name.base_name o dest_Const_name))
    fun added_fields ctxt =
      let val earlier = map (#serial o #3) (Micro_Rust_Names.dump \<^context>)
      in
        Micro_Rust_Names.dump ctxt
        |> filter_out (fn (_, _, entry) => member (op =) earlier (#serial entry))
        |> map (fn (kind, name, entry) =>
            (kind, name, Long_Name.base_name (dest_Const_name (#hol_term entry))))
      end
    val flags_item =
      T.cartouche
        " struct SelectorNameFlags { selectorNameFirst: u32, selector_name_second: bool } "
    val unprefixed =
      [("selectorNameFirst", "selector_name_first"),
       ("selector_name_second", "selector_name_second")]
    val prefixed =
      [("selectorNameFirst", "selector_name_flags_selector_name_first"),
       ("selector_name_second", "selector_name_flags_selector_name_second")]
  in
    (* The bare spelling is canonical; an explicit false or an omitted option keeps the prefix. *)
    val _ =
      List.app (fn (label, option, expected) =>
        let
          val ctxt =
            T.succeeded thy label ("urust_datatype [" ^ option ^ "] " ^ flags_item)
          val lenses =
            map (fn (_, selector) => "selector_name_flags_" ^ selector ^ "_lens") expected
        in
          if fields ctxt "SelectorNameFlags" = expected andalso
              eq_set (op =) (added_fields ctxt,
                map2 (fn (source, _) => fn lens => (Micro_Rust_Names.NField, source, lens))
                  expected lenses)
          then () else error (label ^ " chose the wrong selectors or field registrations")
        end)
      [("selector-name-option-bare", "unprefixed_selectors", unprefixed),
       ("selector-name-option-true", "unprefixed_selectors = true", unprefixed),
       ("selector-name-option-false", "unprefixed_selectors = false", prefixed),
       ("selector-name-option-omitted", "pp_test", prefixed)]

    val suppressed =
      T.succeeded thy "selector-name-option-suppressed"
        ("urust_datatype [unprefixed_selectors, register_notation = false] " ^ flags_item)
    val _ =
      if fields suppressed "SelectorNameFlags" = unprefixed andalso null (added_fields suppressed)
        andalso can (Proof_Context.get_thm suppressed)
          "selector_name_flags_selector_name_first_lens_valid"
      then () else error "unprefixed selectors changed suppressed field registration"

    (* The option is inline-only: no attribute and no scoped default exist. *)
    val _ =
      List.app (fn (label, option) =>
        let val text = "declare [[" ^ option ^ "]]"
        in
          T.rejected_at thy label ("Undefined attribute: " ^ quote option)
            (T.source_range text 1 ("[[", option)) text
        end)
      [("selector-name-no-attribute", "unprefixed_selectors"),
       ("selector-name-no-scoped-setting", "urust_unprefixed_selectors")]
    val integer = "urust_datatype [unprefixed_selectors = 1] " ^ flags_item
    val _ =
      T.rejected_at thy "selector-name-option-integer"
        "uRust command option \"unprefixed_selectors\" expects true or false"
        (T.source_range integer 1 ("= ", "1")) integer
    val duplicate =
      "urust_datatype [unprefixed_selectors, unprefixed_selectors = false] " ^ flags_item
    val _ =
      T.rejected_at thy "selector-name-option-duplicate"
        "duplicate uRust command option \"unprefixed_selectors\""
        (T.source_range duplicate 1 (", ", "unprefixed_selectors")) duplicate
    val _ =
      List.app (fn command =>
        let val text = command ^ " [unprefixed_selectors] _ " ^ T.cartouche " () "
        in
          T.rejected_at thy ("selector-name-option-" ^ command)
            "unknown uRust command option \"unprefixed_selectors\""
            (T.source_range text 1 ("[", "unprefixed_selectors")) text
        end)
      ["urust_expr", "urust_fn"]

    (* simple_word_enum generates no selectors, however the backend is selected. *)
    val _ =
      List.app (fn (label, options, item) =>
        let val text = "urust_datatype [" ^ options ^ "] " ^ T.cartouche item
        in
          T.rejected_at thy label
            "unprefixed_selectors does not apply to the simple_word_enum backend"
            (T.source_range text 1 ("", "unprefixed_selectors")) text
        end)
      [("selector-name-word-width", "word_width = 8, unprefixed_selectors",
        " enum SelectorNameWord { On, Off } "),
       ("selector-name-word-repr", "unprefixed_selectors",
        " #[repr(u8)] enum SelectorNameWord { On = 1, Off = 2 } "),
       ("selector-name-word-explicit",
        "backend = \"simple_word_enum\", word_width = 8, unprefixed_selectors",
        " enum SelectorNameWord { On, Off } ")]
    val _ =
      List.app (fn (label, options, item) =>
        ignore (T.succeeded thy label ("urust_datatype [" ^ options ^ "] " ^ T.cartouche item)))
      [("selector-name-word-false", "word_width = 8, unprefixed_selectors = false",
        " enum SelectorNameWord { On, Off } "),
       ("selector-name-word-custom", "backend = \"enum\", unprefixed_selectors",
        " #[repr(u8)] enum SelectorNameWord { On = 1, Off = 2 } "),
       ("selector-name-tuple-struct", "unprefixed_selectors",
        " struct SelectorNameTuple(u32, bool); ")]
  end
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    fun declaration options item =
      "urust_datatype [" ^ options ^ "] " ^ T.cartouche item
  in
    (* Unprefixed names take part in every effective-name check. *)
    val struct_collision =
      declaration "unprefixed_selectors"
        " struct SelectorNameCollision { selectorNameValue: u32, selector_name_value: bool } "
    val _ =
      T.rejected_at thy "selector-name-unprefixed-collision"
        "duplicate generated HOL field \"selector_name_value\""
        (T.source_range struct_collision 1 (", ", "selector_name_value")) struct_collision
    val struct_key =
      declaration
        ("unprefixed_selectors, renames = " ^
          T.rename_list [("selector_name_first", "selector_name_second")])
        " struct SelectorNameKeyed { selector_name_first: u32, selector_name_second: bool } "
    val _ =
      T.rejected_at thy "selector-name-unprefixed-key-default"
        "duplicate generated HOL field \"selector_name_second\""
        (T.source_range struct_key 1 (", ", "selector_name_second")) struct_key
    val _ =
      List.app (fn (suffix, backend) =>
        let
          val shared =
            declaration (backend ^ "unprefixed_selectors")
              (" enum SelectorNameShared { First { selector_name_value: u32 }, " ^
                "Second { selector_name_value: bool } } ")
          val _ =
            T.rejected_at thy ("selector-name-unprefixed-variants" ^ suffix)
              "duplicate generated HOL selector \"selector_name_value\""
              (T.source_range shared 2 ("{ ", "selector_name_value")) shared
          val payload_key =
            declaration
              (backend ^ "unprefixed_selectors, renames = " ^
                T.rename_list [("Second.selector_name_b", "selector_name_a")])
              (" enum SelectorNamePayload { First { selector_name_a: u32 }, " ^
                "Second { selector_name_b: bool } } ")
          val _ =
            T.rejected_at thy ("selector-name-unprefixed-payload-key" ^ suffix)
              "duplicate generated HOL selector \"selector_name_a\""
              (T.key_range payload_key 1 "selector_name_a") payload_key
          val hidden =
            declaration (backend ^ "unprefixed_selectors")
              " enum SelectorNameHiddenChoice { Hidden { _selectorNameSecret: u32 } } "
          val _ =
            T.rejected_at thy ("selector-name-unprefixed-invalid-payload" ^ suffix)
              ("invalid HOL name binding \"_selector_name_secret\" for the unprefixed selector " ^
                "of field \"_selectorNameSecret\"")
              (T.source_range hidden 1 ("{ ", "_selectorNameSecret")) hidden
          val resolved =
            declaration
              (backend ^ "unprefixed_selectors, renames = " ^
                T.rename_list [("Hidden._selectorNameSecret", "selector_name_secret")])
              " enum SelectorNameHiddenChoice { Hidden { _selectorNameSecret: u32 } } "
          val ctxt = T.succeeded thy ("selector-name-unprefixed-resolved" ^ suffix) resolved
          val entry =
            the (URust_Item_Scope.lookup_constructor ctxt "SelectorNameHiddenChoice::Hidden")
        in
          if map (apsnd (Long_Name.base_name o dest_Const_name))
              (URust_Item_Scope.constructor_fields entry) =
              [("_selectorNameSecret", "selector_name_secret")]
          then () else error ("an explicit key did not replace an invalid default" ^ suffix)
        end)
      [("-enum", ""), ("-hol", "backend = hol, ")]
    val hidden_struct =
      declaration "unprefixed_selectors" " struct SelectorNameHidden { _selectorNameSecret: u32 } "
    val _ =
      T.rejected_at thy "selector-name-unprefixed-invalid-field"
        "invalid HOL name binding \"_selector_name_secret\" for the unprefixed selector"
        (T.source_range hidden_struct 1 ("{ ", "_selectorNameSecret")) hidden_struct
  end
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    val label = "selector-name-shared-structs"
    val text =
      "urust_datatype [unprefixed_selectors] " ^
        T.cartouche " struct SelectorNameLeft { selector_name_shared: u32 } " ^ "\n" ^
      "urust_datatype [unprefixed_selectors] " ^
        T.cartouche " struct SelectorNameRight { selector_name_shared: bool } "
    val ctxt = T.succeeded thy label text
    fun read name =
      dest_Const_name (Proof_Context.read_const {proper = true, strict = false} ctxt name)
    fun qualified_path name = Long_Name.explode name |> rev |> take 2 |> rev
    fun lens_of source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)
      |> (fn term => Term.add_const_names term [])
      |> filter (String.isSuffix "_selector_name_shared_lens")
      |> map Long_Name.base_name
  in
    (* Record selectors are qualified by their type. Both declarations succeed, the later short
       name shadows the earlier one, and each selector is defined at its own source field. *)
    val _ =
      if qualified_path (read "selector_name_shared") =
            ["selector_name_right", "selector_name_shared"] andalso
          qualified_path (read "selector_name_left.selector_name_shared") =
            ["selector_name_left", "selector_name_shared"]
      then () else error "unprefixed record selectors no longer shadow by short name"
    val _ =
      List.app (fn (qualified, occurrence) =>
        let
          val {pos, ...} =
            Name_Space.the_entry (Proof_Context.const_space ctxt) (read qualified)
          val (start, _) = T.source_range text occurrence ("{ ", "selector_name_shared")
        in
          if Position.offset_of pos = SOME start andalso Position.file_of pos = SOME label
          then () else error ("unprefixed selector " ^ qualified ^ " lost its field position")
        end)
      [("selector_name_left.selector_name_shared", 1),
       ("selector_name_right.selector_name_shared", 2)]
    (* Rust field access remains type-directed between the two lenses. *)
    val _ =
      if lens_of "(SelectorNameLeft { selector_name_shared: 1u32 }).selector_name_shared" =
            ["selector_name_left_selector_name_shared_lens"] andalso
          lens_of "(SelectorNameRight { selector_name_shared: true }).selector_name_shared" =
            ["selector_name_right_selector_name_shared_lens"]
      then () else error "shared unprefixed field names changed Rust field resolution"

    (* Custom enum payload selectors are unqualified constants, so the second declaration of the
       same unprefixed selector is the native duplicate-constant error at its field. *)
    val enum_label = "selector-name-shared-custom-enums"
    val enum_text =
      "urust_datatype [unprefixed_selectors] " ^
        T.cartouche " enum SelectorNameFirstSignal { Tone { selector_name_level: u32 } } " ^ "\n" ^
      "urust_datatype [unprefixed_selectors] " ^
        T.cartouche " enum SelectorNameSecondSignal { Chime { selector_name_level: bool } } "
    val _ =
      T.rejected_at thy enum_label "Duplicate constant declaration"
        (T.source_range enum_text 2 ("{ ", "selector_name_level")) enum_text
  end
\<close>

section\<open> Generated selector output \<close>

text\<open>
Manifests, normalized generated declarations and definition entities derive from the actual
generated selectors: keyed and automatic positional selectors appear with the named ones.
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    val item =
      " enum SelectorNameOutput { Unset, Packed(u32, bool), Marked { value: u32, other: bool } } "
    val entries =
      [("Packed.1", "selector_name_packed_flag"), ("Marked.value", "selector_name_marked_value")]
    fun require label condition = if condition then () else error ("selector output: " ^ label)
    fun index_of text plain =
      (case Substring.position text (Substring.full plain) of
         (before_text, rest) =>
           if Substring.isEmpty rest then error ("selector output is missing " ^ quote text)
           else Substring.size before_text)
  in
    val _ =
      List.app (fn (suffix, backend, hol) =>
        let
          val label = "selector-name-output" ^ suffix
          val text =
            "urust_datatype [" ^ backend ^ "verbosity = 2, renames = " ^
              T.rename_list entries ^ "] " ^ T.cartouche item
          val {result, plain, markup} = T.run_output thy label text
          val ctxt =
            (case result of
               Exn.Res state => Toplevel.context_of state
             | Exn.Exn exn => Exn.reraise exn)
          fun full name =
            dest_Const_name (Proof_Context.read_const {proper = true, strict = false} ctxt name)
          val flag = full "selector_name_packed_flag"
          val value = full "selector_name_marked_value"
          val other = full "selector_name_output_marked_other"
          val manifest =
            ["SelectorNameOutput::Packed.1 -> " ^ flag,
             "SelectorNameOutput::Marked.value -> " ^ value,
             "SelectorNameOutput::Marked.other -> " ^ other]
          val positional_default = "SelectorNameOutput::Packed.0 -> "
          (* Ctr_Sugar names the remaining positional field; the custom enum defines nothing. *)
          val _ =
            if hol then
              let val default = full "un_Packed1"
              in
                require ("automatic hol selector in the manifest" ^ suffix)
                  (index_of (positional_default ^ default) plain <
                    index_of (hd manifest) plain);
                require ("automatic hol selector in the declaration" ^ suffix)
                  (String.isSubstring ("(" ^ default ^ ": 32 word)") plain)
              end
            else
              require ("custom enum invented a positional selector" ^ suffix)
                (not (String.isSubstring positional_default plain))
          val _ =
            require ("manifest selector order" ^ suffix)
              (index_of (nth manifest 0) plain < index_of (nth manifest 1) plain andalso
                index_of (nth manifest 1) plain < index_of (nth manifest 2) plain)
          val _ =
            List.app (fn expected =>
              require ("normalized declaration lacks " ^ expected ^ suffix)
                (String.isSubstring expected plain))
              ["(" ^ flag ^ ": bool)", "(" ^ value ^ ": 32 word)", "(" ^ other ^ ": bool)",
               "definition selector_name_packed_flag_def:",
               "definition selector_name_marked_value_def:"]
          val _ =
            List.app (fn (target, name) =>
              require ("definition entity of " ^ name ^ suffix)
                (T.has_definition_entity markup name (T.key_range text 1 target)))
              [("selector_name_packed_flag", flag), ("selector_name_marked_value", value)]
        in () end)
        [("-enum", "", false), ("-hol", "backend = hol, ", true)]

    (* An unprefixed custom-enum payload selector is defined at its source field. *)
    val label = "selector-name-output-unprefixed"
    val text =
      "urust_datatype [verbosity = 1, unprefixed_selectors] " ^
        T.cartouche " enum SelectorNameUnprefixedOutput { Tone { selector_name_pitch_level: u32 } } "
    val {result, plain, markup} = T.run_output thy label text
    val ctxt =
      (case result of
         Exn.Res state => Toplevel.context_of state
       | Exn.Exn exn => Exn.reraise exn)
    val pitch =
      dest_Const_name (Proof_Context.read_const {proper = true, strict = false} ctxt
        "selector_name_pitch_level")
    val _ =
      require "unprefixed selector in the manifest"
        (String.isSubstring
          ("SelectorNameUnprefixedOutput::Tone.selector_name_pitch_level -> " ^ pitch) plain)
    val _ =
      require "definition entity of an unprefixed selector"
        (T.has_definition_entity markup pitch
          (T.source_range text 1 ("{ ", "selector_name_pitch_level")))
  end
\<close>

section\<open> Generated name conflicts \<close>

text\<open>
Rename targets and unprefixed names are checked against every name the backend binds for the
declaration: constructors, Ctr_Sugar's automatic \<open>un_\<close> selectors and \<open>is_\<close>
discriminators exactly where it generates them, other selectors, and record constructors and
updates. Conflicts are positioned at the explicit or unprefixed name.
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    fun declaration backend entries item =
      "urust_datatype [" ^ backend ^ "renames = " ^ T.rename_list entries ^ "] " ^
        T.cartouche item
    val hol = "backend = hol, "
    fun rejected_at_target label backend entries item (target, occurrence) fragment =
      let val text = declaration backend entries item
      in T.rejected_at thy label fragment (T.key_range text occurrence target) text end
    fun fields ctxt path =
      URust_Item_Scope.constructor_fields (the (URust_Item_Scope.lookup_constructor ctxt path))
      |> map (apsnd (Long_Name.base_name o dest_Const_name))
    fun read ctxt name =
      Long_Name.base_name
        (dest_Const_name (Proof_Context.read_const {proper = true, strict = false} ctxt name))
  in
    (* Ctr_Sugar's automatic selectors: a shared, mistyped or same-constructor coincidence. *)
    val _ =
      List.app (fn (label, entries, item, target, fragment) =>
        rejected_at_target ("selector-name-automatic-" ^ label) hol entries item target fragment)
        [("same-type", [("B.0", "un_A")], " enum SelectorNameMerge { A(u32), B(u32) } ",
          ("un_A", 1),
          "generated HOL selector \"un_A\" conflicts with the automatic selector of " ^
            "SelectorNameMerge::A.0"),
         ("named-payload", [("B.value", "un_A")],
          " enum SelectorNameMerge { A(u32), B { value: u32 } } ", ("un_A", 1),
          "conflicts with the automatic selector of SelectorNameMerge::A.0"),
         ("different-type", [("B.0", "un_A")], " enum SelectorNameMerge { A(u32), B(bool) } ",
          ("un_A", 1), "conflicts with the automatic selector of SelectorNameMerge::A.0"),
         ("same-variant", [("A.0", "un_A2")], " enum SelectorNameMerge { A(u32, u32), B } ",
          ("un_A2", 1), "conflicts with the automatic selector of SelectorNameMerge::A.1"),
         ("renamed-constructor",
          [("A", "SelectorNameModelA"), ("B.0", "un_SelectorNameModelA")],
          " enum SelectorNameMerge { A(u32), B(u32) } ", ("un_SelectorNameModelA", 1),
          "conflicts with the automatic selector of SelectorNameMerge::A.0"),
         ("discriminator", [("B.0", "is_A")], " enum SelectorNameMerge { A(u32), B(u32) } ",
          ("is_A", 1),
          "generated HOL selector \"is_A\" conflicts with the automatic discriminator of " ^
            "SelectorNameMerge::A"),
         ("discriminator-three", [("C.0", "is_B")],
          " enum SelectorNameMerge { A, B(u32), C(u32) } ", ("is_B", 1),
          "conflicts with the automatic discriminator of SelectorNameMerge::B"),
         ("constructor-discriminator", [("A.0", "selector_name_first"), ("B", "is_A")],
          " enum SelectorNameMerge { A(u32), B(u32) } ", ("is_A", 1),
          "generated HOL constructor \"is_A\" conflicts with the automatic discriminator of " ^
            "SelectorNameMerge::A")]

    (* Only the names Ctr_Sugar generates are reserved. *)
    val _ =
      List.app (fn (label, entries, item, checks) =>
        let val ctxt = T.succeeded thy ("selector-name-automatic-" ^ label)
          (declaration hol entries item)
        in List.app (fn (name, expected) =>
          if read ctxt name = expected then ()
          else error ("selector-name-automatic-" ^ label ^ " generated the wrong " ^ name)) checks
        end)
      [("own-default", [("A.0", "un_A")], " enum SelectorNameOwn { A(u32), B(u32) } ",
        [("un_A", "un_A"), ("un_B", "un_B"), ("is_A", "is_A")]),
       ("omitted-discriminator", [("A.0", "is_B")], " enum SelectorNameOmitted { A(u32), B(u32) } ",
        [("is_B", "is_B"), ("is_A", "is_A")]),
       ("nullary-discriminator", [("B.0", "is_A")], " enum SelectorNameNullary { A, B(u32) } ",
        [("is_A", "is_A")]),
       ("renamed-default", [("A", "SelectorNameModelA"), ("B.0", "un_A")],
        " enum SelectorNameRenamedDefault { A(u32), B(u32) } ",
        [("un_A", "un_A"), ("un_SelectorNameModelA", "un_SelectorNameModelA")])]

    (* Unqualified custom-enum selectors would shadow constructors; there are no discriminators. *)
    val _ =
      List.app (fn (suffix, backend) =>
        rejected_at_target ("selector-name-constructor" ^ suffix) backend [("Packed.1", "Unset")]
          " enum SelectorNameShadow { Unset, Packed(u32, bool) } " ("Unset", 1)
          ("generated HOL selector \"Unset\" conflicts with the constructor of " ^
            "SelectorNameShadow::Unset"))
        [("-enum", ""), ("-hol", hol)]
    val _ =
      List.app (fn (suffix, backend) =>
        rejected_at_target ("selector-name-renamed-constructor" ^ suffix) backend
          [("Unset", "SelectorNameModelUnset"), ("Marked.value", "SelectorNameModelUnset")]
          " enum SelectorNameShadow { Unset, Marked { value: u32 } } "
          ("SelectorNameModelUnset", 2)
          "conflicts with the constructor of SelectorNameShadow::Unset")
        [("-enum", ""), ("-hol", hol)]
    val custom_discriminator =
      T.succeeded thy "selector-name-custom-discriminator"
        (declaration "" [("B.0", "is_A")] " enum SelectorNameCustomDisc { A(u32), B(u32) } ")
    val _ =
      if read custom_discriminator "is_A" = "is_A" then ()
      else error "the custom enum reserved a discriminator name"

    (* Record constructors and updates. *)
    val update =
      declaration "unprefixed_selectors, " [("selectorNameFirst", "update_selector_name_second")]
        " struct SelectorNameRecord { selectorNameFirst: u32, selector_name_second: bool } "
    val _ =
      T.rejected_at thy "selector-name-record-update"
        ("generated HOL field \"update_selector_name_second\" conflicts with the automatic " ^
          "update function of SelectorNameRecord.selector_name_second")
        (T.key_range update 1 "update_selector_name_second") update
    val constructor =
      declaration "" [("selectorNameFirst", "make_selector_name_record")]
        " struct SelectorNameRecord { selectorNameFirst: u32 } "
    val _ =
      T.rejected_at thy "selector-name-record-constructor"
        ("generated HOL field \"make_selector_name_record\" conflicts with the automatic " ^
          "constructor of SelectorNameRecord")
        (T.key_range constructor 1 "make_selector_name_record") constructor
    val unprefixed =
      "urust_datatype [unprefixed_selectors] " ^
        T.cartouche " struct SelectorNameMade { makeSelectorNameMade: u32 } "
    val _ =
      T.rejected_at thy "selector-name-unprefixed-record-constructor"
        "generated HOL field \"make_selector_name_made\" conflicts with the automatic constructor"
        (T.source_range unprefixed 1 ("{ ", "makeSelectorNameMade")) unprefixed
    val own_update =
      T.succeeded thy "selector-name-record-own-update"
        (declaration "" [("selectorNameFirst", "update_selector_name_first")]
          " struct SelectorNameRecord { selectorNameFirst: u32 } ")
    val _ =
      if fields own_update "SelectorNameRecord" =
          [("selectorNameFirst", "update_selector_name_first")]
      then () else error "a selector named after its own update was rejected"
  end
\<close>

ML_val\<open>
  local
    structure T = Selector_Name_Test
    val thy = \<^theory>
    fun pair_item second =
      T.cartouche (" enum SelectorNamePair { A(u32, u32), A1(" ^ second ^ "), N { v: u32 } } ")
  in
    (* Ctr_Sugar names A's first field and A1's field both un_A1. Without a key or unprefixed
       name involved this is the native behaviour: one shared selector for equal types. *)
    val shared =
      T.succeeded thy "selector-name-automatic-shared"
        ("urust_datatype [backend = hol] " ^ pair_item "u32")
    val sugar =
      the (Ctr_Sugar.ctr_sugar_of shared
        (dest_Type_name (body_type (fastype_of (URust_Item_Scope.constructor_scheme
          (the (URust_Item_Scope.lookup_constructor shared "SelectorNamePair::A1")))))))
    val _ =
      if map (map (Long_Name.base_name o dest_Const_name)) (#selss sugar) =
          [["un_A1", "un_A2"], ["un_A1"], ["selector_name_pair_n_v"]] andalso
        hd (hd (#selss sugar)) = hd (nth (#selss sugar) 1)
      then () else error "coinciding automatic selectors were not shared natively"

    (* For different field types the native Ctr_Sugar error stands, at the command. *)
    val mistyped = "urust_datatype [backend = hol] " ^ pair_item "bool"
    val _ =
      T.rejected_at thy "selector-name-automatic-shared-mistyped"
        "Inconsistent range type for selector \"un_A1\""
        (T.source_range mistyped 1 ("", "urust_datatype")) mistyped

    (* A key that targets the shared automatic name is still rejected at the key. *)
    val keyed =
      "urust_datatype [backend = hol, renames = " ^ T.rename_list [("N.v", "un_A1")] ^ "] " ^
        pair_item "u32"
    val _ =
      T.rejected_at thy "selector-name-automatic-shared-keyed"
        ("generated HOL selector \"un_A1\" conflicts with the automatic selector of " ^
          "SelectorNamePair::A.0")
        (T.key_range keyed 1 "un_A1") keyed
  end
\<close>

end
