theory Parser_Datatype_Tests
  imports Parser_Test_Utils
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open> Rust datatype declarations \<close>

urust_datatype parser_point \<open>
  struct ParserPoint {
    x: u32,
    history: \<tau>\<open>32 word list\<close>,
  }
\<close>

urust_datatype \<open>
  struct ParserTuple(u32, bool, \<tau>\<open>nat option\<close>,);
\<close>

urust_datatype \<open>
  struct ParserMarker;
\<close>

urust_datatype \<open>
  struct HTTPServerStatus;
\<close>

urust_datatype \<open>
  struct ParserPrimitives(
    u8, u16, u32, u64, usize, i32, i64, bool, (),
  );
\<close>

urust_datatype \<open>
  enum ParserMessage {
    Empty,
    Data(u32, \<tau>\<open>nat option\<close>,),
    Named {
      code: u32,
      payload: \<tau>\<open>8 word list\<close>,
    },
  }
\<close>

urust_datatype wire_packet_hol \<open>
  struct WirePacket {
    sequence: u64,
    valid: bool,
  }
\<close>

urust_datatype \<open>
  struct ParserNumberBox {
    value: u32,
  }
\<close>

urust_datatype \<open>
  struct ParserFlagBox {
    value: bool,
  }
\<close>

urust_datatype \<open>
  enum FirstSharedChoice {
    SharedIdle,
    SharedPayload(u32),
    SharedNamed {
      value: u32,
    },
  }
\<close>

urust_datatype \<open>
  enum SecondSharedChoice {
    SharedIdle,
    SharedPayload(bool),
    SharedNamed {
      value: bool,
    },
  }
\<close>

urust_datatype \<open>
  struct ParserComposite(
    \<tau>\<open>parser_point\<close>,
    \<tau>\<open>parser_message list\<close>,
    \<tau>\<open>nat \<times> bool option\<close>,
  );
\<close>

urust_datatype \<open>
  struct ParserArity14(
    u32, u32, u32, u32, u32, u32, u32,
    u32, u32, u32, u32, u32, u32, u32,
  );
\<close>

urust_datatype \<open>
  /* leading /* nested */ block comment */
  struct ParserCommented(
    u32, // first field
    bool, /* second field */
  );
\<close>

urust_datatype \<open>
  struct HTTP2ServerState;
\<close>

urust_datatype \<open>
  struct XMLHttpRequest;
\<close>

urust_expr parser_point_value \<open>
  ParserPoint {
    x: 7u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }
\<close>

urust_expr parser_tuple_value \<open>
  ParserTuple(8u32, true, None)
\<close>

urust_expr parser_marker_value \<open>
  ParserMarker
\<close>

urust_expr parser_empty_value \<open>
  ParserMessage::Empty
\<close>

urust_expr parser_data_value \<open>
  ParserMessage::Data(9u32, None)
\<close>

urust_expr parser_tuple_pattern \<open>
  match ParserTuple(10u32, false, None) {
    ParserTuple(value, _, _) \<Rightarrow> value,
  }
\<close>

urust_expr parser_named_variant_pattern \<open>
  match \<llangle>parser_message.Named 11 []\<rrangle> {
    ParserMessage::Named { code, payload: _ } \<Rightarrow> code,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr parser_named_struct_pattern \<open>
  match (ParserPoint {
    x: 12u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }) {
    ParserPoint { x, history: _ } \<Rightarrow> x,
  }
\<close>

urust_expr parser_named_struct_rest_pattern \<open>
  match (ParserPoint {
    x: 24u32,
    history: \<llangle>[] :: 32 word list\<rrangle>,
  }) {
    ParserPoint { x, .. } \<Rightarrow> x,
  }
\<close>

urust_expr parser_named_variant_rest_pattern \<open>
  match \<llangle>undefined :: parser_message\<rrangle> {
    ParserMessage::Named { code, .. } \<Rightarrow> code,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr parser_named_struct_field (point) \<open>
  point.x + 0u32
\<close>

urust_expr parser_named_struct_assignment (point) \<open>
  point.x = 13u32
\<close>

urust_expr wire_packet_value \<open>
  WirePacket {
    sequence: 14u64,
    valid: true,
  }
\<close>

urust_expr wire_packet_field \<open>
  (WirePacket {
    sequence: 15u64,
    valid: false,
  }).sequence
\<close>

urust_expr parser_number_box_field \<open>
  (ParserNumberBox { value: 16u32 }).value
\<close>

urust_expr parser_flag_box_field \<open>
  (ParserFlagBox { value: true }).value
\<close>

urust_expr first_shared_unit \<open>
  FirstSharedChoice::SharedIdle
\<close>

urust_expr second_shared_unit \<open>
  SecondSharedChoice::SharedIdle
\<close>

urust_expr first_shared_payload \<open>
  FirstSharedChoice::SharedPayload(17u32)
\<close>

urust_expr second_shared_payload \<open>
  SecondSharedChoice::SharedPayload(false)
\<close>

urust_expr first_shared_pattern \<open>
  match FirstSharedChoice::SharedPayload(18u32) {
    FirstSharedChoice::SharedPayload(value) \<Rightarrow> value,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr second_shared_pattern \<open>
  match \<llangle>undefined :: second_shared_choice\<rrangle> {
    SecondSharedChoice::SharedNamed { value } \<Rightarrow> value,
    _ \<Rightarrow> false,
  }
\<close>

urust_expr parser_composite_value \<open>
  ParserComposite(
    ParserPoint {
      x: 19u32,
      history: \<llangle>[] :: 32 word list\<rrangle>,
    },
    \<llangle>[] :: parser_message list\<rrangle>,
    \<llangle>(20, None) :: nat \<times> bool option\<rrangle>
  )
\<close>

urust_expr parser_arity14_pattern \<open>
  match ParserArity14(
    1u32, 2u32, 3u32, 4u32, 5u32, 6u32, 7u32,
    8u32, 9u32, 10u32, 11u32, 12u32, 13u32, 14u32
  ) {
    ParserArity14(first, _, _, _, _, _, _, _, _, _, _, _, _, _) \<Rightarrow> first,
  }
\<close>

urust_expr parser_commented_value \<open>
  ParserCommented(21u32, true)
\<close>

urust_expr parser_marker_pattern \<open>
  match ParserMarker {
    ParserMarker \<Rightarrow> (),
  }
\<close>

urust_expr parser_empty_pattern \<open>
  match ParserMessage::Empty {
    ParserMessage::Empty \<Rightarrow> 22u32,
    _ \<Rightarrow> 0u32,
  }
\<close>

urust_expr parser_point_legacy_labels \<open>
  ParserPoint {
    ignored_first: 7u32,
    ignored_second: \<llangle>[] :: 32 word list\<rrangle>,
  }
\<close>

lemma parser_point_legacy_labels_eq:
  \<open>parser_point_legacy_labels = parser_point_value\<close>
  by (simp add: parser_point_legacy_labels_def parser_point_value_def)

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

    val point_x = source_field point_constructor "x"
    val point_history = source_field point_constructor "history"
    val named_code = source_field named_constructor "code"
    val named_payload = source_field named_constructor "payload"

    val (definition_result, definition_markup) =
      capture_reports "definitions"
        (fn () =>
          (I.report_type_definition point_type;
           I.report_type_definition message_type;
           List.app I.report_constructor_definition
             [marker_constructor, tuple_constructor,
              point_constructor, empty_constructor,
              data_constructor, named_constructor];
           List.app I.report_field_definition
             [point_x, point_history, named_code, named_payload]))
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
    val _ =
      failure_case 12 "wrong-generated-struct-role"
        named_expression_text
        [("ParserMessage", named_expression_qualifier),
         ("Named", named_expression_terminal),
         ("code",
          named_expression_terminal + size "Named"),
         ("payload",
          named_expression_terminal + size "Named")]

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
        ("urust_datatype [verbosity = 1] output_enum " ^
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
        ("urust_datatype [verbosity = 2] output_enum_detailed " ^
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

    val function_type =
      cartouche
        "(unit, unit, unit, unit, unit) function_body"
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
        ("urust_fn struct_inside_fn :: " ^ function_type ^ " " ^
          "() " ^ cartouche " struct LocalStruct; ")
    val _ =
      assert_rejected "enum-inside-urust-fn"
        "uRust enum declarations are not expressions; use urust_datatype"
        ("urust_fn enum_inside_fn :: " ^ function_type ^ " " ^
          "() " ^ cartouche " enum LocalEnum { Empty, } ")
    val _ =
      assert_rejected "nested-struct-inside-urust-expr"
        "uRust struct declarations are not expressions; use urust_datatype"
        ("urust_expr nested_struct_inside_expr " ^
          cartouche
            " if true { struct NestedStruct; } else { () } ")
    val _ =
      assert_rejected "nested-enum-inside-urust-fn"
        "uRust enum declarations are not expressions; use urust_datatype"
        ("urust_fn nested_enum_inside_fn :: " ^ function_type ^ " " ^
          "() " ^ cartouche
            " { enum NestedEnum { Ready, } } ")

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
        "type variables are not supported in datatype fields"
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
        "unsupported bare field type \"CustomType\""
        ("urust_datatype unsupported_bare_type " ^
          datatype_source "UnsupportedBareType"
            "value: CustomType,")
    val _ =
      assert_rejected "unsupported-u128"
        "unsupported bare field type \"u128\""
        ("urust_datatype unsupported_u128 " ^
          datatype_source "UnsupportedU128"
            "value: u128,")
    val _ =
      assert_rejected "unsupported-rust-tuple-type"
        "syntax error"
        ("urust_datatype unsupported_rust_tuple " ^
          datatype_source "UnsupportedRustTuple"
            "value: (u32, bool),")
    val _ =
      assert_rejected "unsupported-rust-array-type"
        "syntax error"
        ("urust_datatype unsupported_rust_array " ^
          datatype_source "UnsupportedRustArray"
            "value: [u8; 4],")
    val _ =
      assert_rejected "unsupported-rust-reference-type"
        "syntax error"
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
        "duplicate generated HOL field \"foo_bar\""
        ("urust_datatype generated_field_collision " ^
          datatype_source "GeneratedFieldCollision"
            "fooBar: u32, foo_bar: bool,")
    val _ =
      assert_rejected "generated-selector-name-collision"
        "duplicate generated HOL selector \"foo_bar_value\""
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
      assert_rejected "empty-struct" "syntax error"
        ("urust_datatype empty_struct " ^
          cartouche " struct EmptyStruct {} ")
    val _ =
      assert_rejected "empty-tuple-struct" "syntax error"
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
      assert_rejected "item-conflict" "already mapped"
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
      assert_rejected "named-variant-construction"
        "requires metadata-aware struct construction"
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
        "generic arguments are not supported on generated Rust item paths"
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

end
