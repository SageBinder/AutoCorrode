theory Parser_Slice_Pattern_Syntax_Tests
  imports Parser_Test_Utils
begin

declare [[urust_verbosity = 0]]

section\<open> Slice pattern ASTs and source ranges \<close>

text\<open>
These tests inspect the production parser's unresolved AST directly. Named rests retain three
distinct token ranges, while a slice retains its complete bracket span. Expected positions count
Isabelle symbols, including symbols in comments and embedded HOL before the pattern.
\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>
    val start = Position.make0 17 300 0 "" "" "slice-pattern-syntax-audit"

    fun assert label condition =
      if condition then () else error ("slice pattern syntax audit: " ^ label)
    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source text start) of
         SOME expression => expression
       | NONE => error "slice pattern syntax audit: empty parse")
    fun match_pattern text =
      (case parse text of
         UE_Match (_, _, [UR_Arm (pattern, NONE, _)], _) => pattern
       | _ => error "slice pattern syntax audit: unexpected match AST")
    val prefix = "// \<alpha> before the pattern\nmatch_case \<llangle>undefined\<rrangle> { "
    fun pattern_source pattern = prefix ^ pattern ^ " => () }"
    fun parse_pattern pattern = match_pattern (pattern_source pattern)

    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern syntax audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text needle raw =
      let
        val found = find_from text needle raw
        val left = Position.symbol_explode (String.substring (text, 0, found)) start
      in
        (found, Position.range_position (left, Position.symbol_explode needle left))
      end
    fun same_position actual expected =
      Position.offset_of actual = Position.offset_of expected andalso
      Position.end_offset_of actual = Position.end_offset_of expected andalso
      Position.line_of actual = Position.line_of expected

    fun bound_rests pattern =
      (case pattern of
         P_Slice (items, _) => maps slice_item_rests items
       | P_Constr (_, children) => maps bound_rests children
       | P_Tuple (children, _) => maps bound_rests children
       | P_Group inner => bound_rests inner
       | P_Borrow (_, inner, _) => bound_rests inner
       | P_Alias (_, _, inner, _) => bound_rests inner
       | P_Range (_, lower, upper, _) => bound_rests lower @ bound_rests upper
       | P_Struct (_, fields) =>
           maps (fn SF_Field (_, _, child) => bound_rests child | _ => []) fields
       | P_Or (alternatives, _) => maps bound_rests alternatives
       | _ => [])
    and slice_item_rests (SI_BoundRest rest) = [rest]
      | slice_item_rests (SI_Pat child) = bound_rests child
      | slice_item_rests (SI_Rest _) = []

    fun audit_bound_positions text raw rests =
      fold
        (fn (name, id_pos, alias_pos, rest_pos) => fn after_previous =>
          let
            val (id_raw, expected_id) = token_position text name after_previous
            val (alias_raw, expected_alias) = token_position text "@" (id_raw + size name)
            val (rest_raw, expected_rest) = token_position text ".." (alias_raw + 1)
            val _ = assert (name ^ " identifier span changed") (same_position id_pos expected_id)
            val _ = assert (name ^ " alias span changed") (same_position alias_pos expected_alias)
            val _ = assert (name ^ " rest span changed") (same_position rest_pos expected_rest)
          in rest_raw + 2 end)
        rests raw

    fun item_shape (SI_BoundRest (name, _, _, _)) = "rest:" ^ name
      | item_shape (SI_Rest _) = "bare"
      | item_shape (SI_Pat (P_Ident (name, _))) = "element:" ^ name
      | item_shape (SI_Pat (P_Literal (LP_Integer (lexeme, _)))) = "integer:" ^ lexeme
      | item_shape _ = "other"
    fun audit_slice spelling expected =
      let
        val text = pattern_source spelling
        val pattern = match_pattern text
        val slice_start = Position.symbol_explode prefix start
        val slice_position =
          Position.range_position (slice_start, Position.symbol_explode spelling slice_start)
      in
        (case pattern of
           P_Slice (items, position) =>
             (assert (spelling ^ " item order changed") (map item_shape items = expected);
              assert (spelling ^ " complete slice span changed")
                (same_position position slice_position);
              ignore (fold
                (fn item => fn raw =>
                  let
                    fun token label lexeme actual =
                      let val (found, expected) = token_position text lexeme raw in
                        assert (label ^ " token span changed") (same_position actual expected);
                        found + size lexeme
                      end
                  in
                    case item of
                      SI_BoundRest rest => audit_bound_positions text raw [rest]
                    | SI_Rest position => token "bare rest" ".." position
                    | SI_Pat (P_Ident (name, position)) => token name name position
                    | SI_Pat (P_Literal (LP_Integer (lexeme, position))) =>
                        token "integer" lexeme position
                    | _ => raw
                  end)
                items (size prefix)))
         | _ => error ("slice pattern syntax audit: expected a slice for " ^ quote spelling));
        ignore (audit_bound_positions text (size prefix) (bound_rests pattern))
      end

    val _ =
      List.app (fn (spelling, expected) => audit_slice spelling expected)
        [("[tail@..]", ["rest:tail"]),
         ("[tail @ ..,]", ["rest:tail"]),
         ("[tail@.., last]", ["rest:tail", "element:last"]),
         ("[tail @ .., last,]", ["rest:tail", "element:last"]),
         ("[first, tail@..]", ["element:first", "rest:tail"]),
         ("[first, tail @ ..,]", ["element:first", "rest:tail"]),
         ("[first,tail@..,last]", ["element:first", "rest:tail", "element:last"]),
         ("[first, second, tail @ .., last,]",
           ["element:first", "element:second", "rest:tail", "element:last"]),
         ("[tail'@..]", ["rest:tail'"]),
         ("[first, .., last,]", ["element:first", "bare", "element:last"]),
         ("[..,]", ["bare"]),
         ("[\n first, // \<alpha> trivia\n tail' // binder\n @ // alias\n .., // rest\n last,\n]",
           ["element:first", "rest:tail'", "element:last"]),
         ("[\<comment>\<open>\<alpha>\<close> tail @ \<comment>\<open>gap\<close> ..]",
           ["rest:tail"])]

    val _ =
      (case parse_pattern "[[inside @ ..,], outside @ ..,]" of
         P_Slice
           ([SI_Pat (P_Slice ([SI_BoundRest ("inside", _, _, _)], _)),
             SI_BoundRest ("outside", _, _, _)], _) => ()
       | _ => error "slice pattern syntax audit: nested rest AST changed")
    val _ =
      (case parse_pattern "whole @ [first @ item, middle @ .., last]" of
         P_Alias ("whole", _,
           P_Slice
             ([SI_Pat (P_Alias ("first", _, P_Ident ("item", _), _)),
               SI_BoundRest ("middle", _, _, _),
               SI_Pat (P_Ident ("last", _))], _), _) => ()
       | _ => error "slice pattern syntax audit: whole-list or element alias changed")
    val _ =
      (case parse_pattern "Some(([inside @ ..], Head { field: [outside @ ..], .. }))" of
         P_Constr (path,
           [P_Tuple
             ([P_Slice ([SI_BoundRest ("inside", _, _, _)], _),
               P_Struct (_, [SF_Field ("field", _,
                 P_Slice ([SI_BoundRest ("outside", _, _, _)], _)), SF_Rest _])], _)]) =>
           assert "constructor nesting changed" (render_path path = "Some")
       | _ => error "slice pattern syntax audit: tuple or struct nesting changed")
    val _ =
      (case parse_pattern "&mut [0..=3, middle @ .., last]" of
         P_Borrow (BM_Mut,
           P_Slice
             ([SI_Pat (P_Range (RK_Inclusive, _, _, _)),
               SI_BoundRest ("middle", _, _, _),
               SI_Pat (P_Ident ("last", _))], _), _) => ()
       | _ => error "slice pattern syntax audit: range or reference wrapper changed")
    val _ =
      List.app
        (fn spelling =>
          let
            val text = pattern_source spelling
            val pattern = match_pattern text
          in
            ignore (audit_bound_positions text (size prefix) (bound_rests pattern))
          end)
        ["[[inside @ ..,], outside @ ..,]",
         "Some(([inside @ ..], Head { field: [outside @ ..], .. }))",
         "whole @ [first @ item, middle @ .., last]",
         "&mut [0..=3, middle @ .., last]"]

    val _ =
      List.app
        (fn lexeme =>
          (audit_slice ("[" ^ lexeme ^ ", tail @ .., " ^ lexeme ^ ",]")
             ["integer:" ^ lexeme, "rest:tail", "integer:" ^ lexeme];
           case parse_pattern ("Some(" ^ lexeme ^ ")") of
             P_Constr (path, [P_Literal (LP_Integer (actual, _))]) =>
               assert ("nested integer lexeme changed: " ^ lexeme)
                 (render_path path = "Some" andalso actual = lexeme)
           | _ => error "slice pattern syntax audit: nested integer AST changed"))
        ["0", "17", "0b1_0", "0o1_7", "0xff", "1u8", "2_u16", "3u32", "4_u64",
         "5usize", "0xff_u8"]

    fun consumer_pattern text =
      (case parse text of
         UE_Match (_, _, [UR_Arm (pattern, NONE, _)], _) => pattern
       | UE_IfLet (pattern, _, _, _, _) => pattern
       | UE_LetElse (pattern, _, _, _, _) => pattern
       | UE_WhileLet (_, pattern, _, _, _) => pattern
       | UE_For (pattern, _, _, _) => pattern
       | UE_Let (pattern, _, _) => pattern
       | UE_Const (pattern, _, _) => pattern
       | UE_LetMut (pattern, _, _, _) => pattern
       | UE_Macro (_, _, MP_Matches (_, pattern), _) => pattern
       | _ => error "slice pattern syntax audit: unexpected consumer AST")
    val _ =
      List.app
        (fn text =>
          let val pattern = consumer_pattern text in
            assert "consumer lost its positioned rest"
              (map #1 (bound_rests pattern) = ["tail"]);
            ignore (audit_bound_positions text 0 (bound_rests pattern))
          end)
        ["match \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "match_switch \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "if let [tail @ ..] = \<llangle>undefined\<rrangle> { () } else { () }",
         "let [tail @ ..] = \<llangle>undefined\<rrangle> else { () }; ()",
         "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [tail @ ..] = \<llangle>undefined\<rrangle> { () }",
         "for [tail @ ..] in \<llangle>undefined\<rrangle> { () }",
         "let whole @ outer @ ([tail @ ..], other) = \<llangle>undefined\<rrangle>; ()",
         "const [tail @ ..] = \<llangle>undefined\<rrangle>; ()",
         "let mut [tail @ ..] = \<llangle>undefined\<rrangle>; ()",
         "matches!(\<llangle>undefined\<rrangle>, [tail @ ..,])"]

    val _ =
      (case parse "let whole @ outer @ ([tail @ ..], other) = \<llangle>undefined\<rrangle>; ()" of
         UE_Let
           (P_Alias ("whole", _,
             P_Alias ("outer", _,
               P_Tuple
                 ([P_Slice ([SI_BoundRest ("tail", _, _, _)], _),
                   P_Ident ("other", _)], _), _), _), _, _) => ()
       | _ => error "slice pattern syntax audit: recursive ordinary alias AST changed")

    fun audit_arm_count text expected =
      (case parse text of
         UE_Match (_, _, arms, _) =>
           assert "match arm separator changed" (length arms = expected)
       | _ => error "slice pattern syntax audit: expected match arms")
    val _ =
      List.app (fn text => audit_arm_count text 2)
        ["match_case \<llangle>undefined\<rrangle> { [head, ..] => (), [tail @ ..] => (), }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} , [tail @ ..,] => {} }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} ([tail @ ..]) => {} }"]
  in
  end
\<close>

section\<open> Token markup and binder navigation \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    fun assert label condition =
      if condition then () else error ("slice pattern markup audit: " ^ label)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern markup audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text start needle raw =
      let
        val found = find_from text needle raw
        val left = Position.symbol_explode (String.substring (text, 0, found)) start
      in
        (found, Position.range_position (left, Position.symbol_explode needle left))
      end
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup reports name position =
      exists (fn (actual, properties) =>
        actual = name andalso has_position properties position) reports
    fun entity_id reports property position =
      (case reports
          |> map_filter
            (fn (name, properties) =>
              if name = Markup.entityN andalso
                 Properties.get properties Markup.kindN = SOME "urust_var" andalso
                 has_position properties position
              then Properties.get properties property
              else NONE)
          |> distinct (op =) of
         [id] => id
       | _ => error "slice pattern markup audit: binder entity identity changed")
    fun capture text start =
      #2 (Parser_Test_Reports.markup (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.positioned_content_source text start)))

    val text =
      "match_case \<llangle>[1 :: nat, 4, 9]\<rrangle> { " ^
      "[head, middle' // \<alpha> after binder\n @ // alias trivia\n .., last,] => " ^
      "{ let _ = head; let _ = middle'; let _ = \<llangle>middle'\<rrangle>; let _ = last; () }, _ => () }"
    val start = Position.make0 29 700 0 "" "" "slice-pattern-markup-audit"
    val reports = capture text start
    val (id_raw, definition) = token_position text start "middle'" 0
    val (alias_raw, alias_position) = token_position text start "@" (id_raw + size "middle'")
    val (_, rest_position) = token_position text start ".." (alias_raw + 1)
    val (reference_raw, reference) =
      token_position text start "middle'" (id_raw + size "middle'")
    val (_, antiquotation_reference) =
      token_position text start "middle'" (reference_raw + size "middle'")
    val (_, first_comment) = token_position text start "// \<alpha> after binder" 0
    val (_, second_comment) = token_position text start "// alias trivia" 0

    val _ =
      List.app
        (fn (label, position) =>
          (assert (label ^ " lost operator markup")
             (has_markup reports Markup.operatorN position);
           assert (label ^ " lost typing markup")
             (has_markup reports Markup.typingN position);
           assert (label ^ " acquired bound markup")
             (not (has_markup reports Markup.boundN position))))
        [("rest alias", alias_position), ("rest dots", rest_position)]
    val _ =
      List.app
        (fn position =>
          assert "line comment span or markup changed"
            (has_markup reports Markup.comment1N position))
        [first_comment, second_comment]
    val _ =
      List.app
        (fn position =>
          assert "rest binder or occurrence lost bound markup"
            (has_markup reports Markup.boundN position))
        [definition, reference, antiquotation_reference]
    val _ =
      assert "body reference no longer navigates to its rest binder"
        (entity_id reports Markup.defN definition = entity_id reports Markup.refN reference)
    val _ =
      assert "antiquotation reference no longer navigates to its rest binder"
        (entity_id reports Markup.defN definition =
          entity_id reports Markup.refN antiquotation_reference)
    val _ =
      assert "rest binder was reported as a HOL constant"
        (not (exists (fn (name, properties) =>
          name = Markup.entityN andalso
          Properties.get properties Markup.kindN = SOME Markup.constantN andalso
          has_position properties definition) reports))

    val (_, left_bracket) = token_position text start "[" (find_from text " { " 0)
    val (_, right_bracket) = token_position text start "]" alias_raw
    val (_, comma) = token_position text start "," alias_raw
    val (_, arrow) = token_position text start "=>" alias_raw
    val _ =
      List.app
        (fn position =>
          (assert "slice punctuation lost delimiter markup"
             (has_markup reports Markup.delimiterN position);
           assert "slice punctuation lost typing markup"
             (has_markup reports Markup.typingN position)))
        [left_bracket, right_bracket, comma, arrow]

    val numeral_text =
      "match_case \<llangle>[0 :: nat, 4, 9]\<rrangle> { [0, tail @ .., 9] => " ^
      "{ let _ = tail; () }, _ => () }"
    val numeral_start = Position.make0 37 1100 0 "" "" "slice-pattern-numeral-markup"
    val numeral_reports = capture numeral_text numeral_start
    val pattern_raw = find_from numeral_text " { " 0
    val (_, zero_position) = token_position numeral_text numeral_start "0" pattern_raw
    val (_, nine_position) = token_position numeral_text numeral_start "9" pattern_raw
    val _ =
      List.app
        (fn position =>
          (assert "structural integer lost numeral markup"
             (has_markup numeral_reports Markup.numeralN position);
           assert "structural integer lost typing markup"
             (has_markup numeral_reports Markup.typingN position)))
        [zero_position, nine_position]

    val _ =
      List.app
        (fn (name, spelling) =>
          let
            val text = "match_case \<llangle>[] :: nat list\<rrangle> { [" ^ spelling ^
              "] => { let _ = " ^ name ^ "; () } }"
            val start = Position.make0 39 1200 0 "" "" "slice-pattern-tight-markup"
            val reports = capture text start
            val (id_raw, definition) = token_position text start name 0
            val (alias_raw, alias_position) = token_position text start "@" id_raw
            val (_, rest_position) = token_position text start ".." alias_raw
            val (_, reference) = token_position text start name (id_raw + size name)
          in
            assert "tight or multiline rest binder navigation changed"
              (entity_id reports Markup.defN definition = entity_id reports Markup.refN reference);
            List.app
              (fn position =>
                (assert "tight or multiline operator span changed"
                   (has_markup reports Markup.operatorN position);
                 assert "tight or multiline operator lost typing"
                   (has_markup reports Markup.typingN position)))
              [alias_position, rest_position]
          end)
        [("tail", "tail@.."), ("tail", "tail @ .."),
         ("tail'", "tail'@.."), ("tail'", "tail'\n @\n ..")]

    val alternatives_text =
      "match_case \<llangle>[1 :: nat, 4, 9]\<rrangle> { " ^
      "[head, tail @ ..] | [tail @ .., head] => { let _ = tail; let _ = head; () }, _ => () }"
    val alternatives_start = Position.make0 41 1400 0 "" "" "slice-pattern-alternatives-markup"
    val alternatives_reports = capture alternatives_text alternatives_start
    val (head_raw, head_def) = token_position alternatives_text alternatives_start "head" 0
    val (tail_raw, tail_def) = token_position alternatives_text alternatives_start "tail" head_raw
    val (tail_alt_raw, tail_alt) =
      token_position alternatives_text alternatives_start "tail" (tail_raw + size "tail")
    val (head_alt_raw, head_alt) =
      token_position alternatives_text alternatives_start "head" (tail_alt_raw + size "tail")
    val (tail_body_raw, tail_body) =
      token_position alternatives_text alternatives_start "tail" (head_alt_raw + size "head")
    val (_, head_body) =
      token_position alternatives_text alternatives_start "head" (tail_body_raw + size "tail")
    val _ =
      List.app
        (fn (definition, reference) =>
          assert "repositioned alternative binder lost its canonical entity"
            (entity_id alternatives_reports Markup.defN definition =
              entity_id alternatives_reports Markup.refN reference))
        [(tail_def, tail_alt), (head_def, head_alt), (tail_def, tail_body), (head_def, head_body)]

    val _ =
      List.app
        (fn name =>
          let
            val collision_text =
              "match_case \<llangle>[] :: nat list\<rrangle> { [" ^ name ^
              " @ ..] => { let _ = " ^ name ^ "; () } }"
            val collision_start = Position.make0 53 2000 0 "" "" "slice-pattern-binder-collision"
            val collision_reports = capture collision_text collision_start
            val (raw, definition) = token_position collision_text collision_start name 0
            val (_, reference) =
              token_position collision_text collision_start name (raw + size name)
          in
            assert (name ^ " rest stopped introducing a binder")
              (entity_id collision_reports Markup.defN definition =
                entity_id collision_reports Markup.refN reference)
          end)
        ["Some", "Nil", "length", "True"]
  in
  end
\<close>

section\<open> Atomic validation and positioned failures \<close>

text\<open>
Multiplicity, duplicates, and unequal alternative binder sets fail before local allocation or
guard/body macro resolution. Each failure is followed by a successful elaboration through the same
parser API. Diagnostics retain both primary and secondary source ranges where the existing policy
provides them.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val source_id = "slice-pattern-rejection-audit"
    val start = Position.make0 67 3000 0 "" "" source_id
    val prefix = "// \<alpha> before validation\nmatch_case \<llangle>[] :: nat list\<rrangle> { "
    fun assert label condition =
      if condition then () else error ("slice pattern rejection audit: " ^ label)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern rejection audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun occurrence text needle count =
      let
        fun next 0 raw = find_from text needle raw
          | next n raw = next (n - 1) (find_from text needle raw + size needle)
      in next count (size prefix) end
    fun expected_position text (needle, count) =
      let
        val raw = occurrence text needle count
        val left = Position.symbol_explode (String.substring (text, 0, raw)) start
      in Position.range_position (left, Position.symbol_explode needle left) end
    fun diagnostic_spans message =
      fold Parser_Test_Reports.collect_markup (YXML.parse_body message) []
      |> map_filter (fn (_, properties) =>
        case (Properties.get properties Markup.offsetN,
              Properties.get properties Markup.end_offsetN) of
          (SOME left, SOME right) => SOME (left, right)
        | _ => NONE)
    fun span position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))
    fun recovery () =
      ignore (Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_case \<llangle>[] :: nat list\<rrangle> { [tail @ ..,] => { let _ = tail; () } }"))

    fun reject (pattern, expected, primary, secondary) =
      let
        val text = prefix ^ pattern ^
          " if unknown_slice_guard!() => unknown_slice_body!(), _ => () }"
        val (result, reports) =
          Parser_Test_Reports.markup (fn () =>
            Exn.result (fn () => Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source text start)) ())
        val message =
          (case result of
             Exn.Res _ => error ("slice pattern rejection audit: accepted " ^ quote pattern)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
        val plain = XML.content_of (YXML.parse_body message)
        val spans = diagnostic_spans message
        val _ = assert (pattern ^ " diagnostic changed") (String.isSubstring expected plain)
        val _ = assert (pattern ^ " primary diagnostic range changed")
          (member (op =) spans (span (expected_position text primary)))
        val _ =
          (case secondary of
             NONE => ()
           | SOME token =>
               assert (pattern ^ " secondary diagnostic range changed")
                 (member (op =) spans (span (expected_position text token))))
        (* Report capture is process-wide; concurrent theory commands may also emit entities. *)
        val _ = assert (pattern ^ " allocated a rejected binder")
          (not (exists (fn (name, properties) =>
            name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            Properties.get properties Markup.idN = SOME source_id) reports))
        val _ = assert (pattern ^ " lowered a rejected guard or body")
          (not (String.isSubstring "unknown macro" plain))
        val _ = assert (pattern ^ " leaked a generated identifier")
          (not (String.isSubstring "_urust_" plain))
      in recovery () end

    val multiple = "slice pattern has multiple `..` rest entries"
    val _ =
      List.app reject
        [("[.., ..]", multiple, ("..", 1), NONE),
         ("[left @ .., right @ ..]", multiple, ("..", 1), NONE),
         ("[tail @ .., ..]", multiple, ("..", 1), NONE),
         ("[.., tail @ ..]", multiple, ("..", 1), NONE),
         ("[first, [left @ .., right @ ..], outer @ ..]", multiple, ("..", 1), NONE),
         ("[tail, tail @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[tail @ .., tail]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("whole @ [whole @ ..]", "duplicate pattern binder \"whole\"",
           ("whole", 1), SOME ("whole", 0)),
         ("([tail @ ..], [tail @ ..])", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[item @ tail, tail @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[tail @ ..] | [..]", "or-pattern alternative is missing binder \"tail\"",
           ("|", 0), SOME ("tail", 0)),
         ("[..] | [tail @ ..]", "or-pattern alternative has extra binder \"tail\"",
           ("tail", 0), NONE),
         ("[first, tail @ ..] | [other, tail @ ..]",
           "or-pattern alternative is missing binder \"first\"", ("|", 0), SOME ("first", 0)),
         ("[tail @ ..] | [tail @ .., tail]", "duplicate pattern binder \"tail\"",
           ("tail", 2), SOME ("tail", 1)),
         ("[tail, tail @ ..] | [other @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("Some([tail @ ..] | [..])", "or-pattern alternative is missing binder \"tail\"",
           ("|", 0), SOME ("tail", 0)),
         ("[_ @ ..]", "slice rest binder cannot be `_`", ("_", 0), NONE)]
    val (_, recovery_reports) =
      Parser_Test_Reports.markup (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.positioned_content_source
            (prefix ^ "[tail @ ..] => { let _ = tail; () } }") start))
    val _ = assert "source-scoped report audit lost successful binder reports"
      (exists (fn (name, properties) =>
        name = Markup.entityN andalso
        Properties.get properties Markup.kindN = SOME "urust_var" andalso
        Properties.get properties Markup.idN = SOME source_id) recovery_reports)
  in
  end
\<close>

section\<open> Malformed rest syntax, separators, and recovery \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val start = Position.make0 79 4000 0 "" "" "slice-pattern-malformed-audit"
    fun parse text =
      URust_Parser.parse_source ctxt
        (Parser_Lex_Util.positioned_content_source text start)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern malformed audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text needle count =
      let
        fun occurrence 0 raw = find_from text needle raw
          | occurrence n raw =
              occurrence (n - 1) (find_from text needle raw + size needle)
        val raw = occurrence count 0
        val left = Position.symbol_explode (String.substring (text, 0, raw)) start
      in Position.range_position (left, Position.symbol_explode needle left) end
    fun diagnostic_spans message =
      fold Parser_Test_Reports.collect_markup (YXML.parse_body message) []
      |> map_filter (fn (_, properties) =>
        case (Properties.get properties Markup.offsetN,
              Properties.get properties Markup.end_offsetN) of
          (SOME left, SOME right) => SOME (left, right)
        | _ => NONE)
    fun span position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))
    fun reject text =
      (case Exn.result parse text of
         Exn.Res _ => error ("slice pattern malformed audit: accepted " ^ quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val _ =
                 if String.isSubstring "syntax error" message then ()
                 else error ("slice pattern malformed audit: unexpected diagnostic " ^ message)
               val _ =
                 (case parse "match_case \<llangle>undefined\<rrangle> { [tail@..,] => () }" of
                    SOME (URust_AST.UE_Match
                      (_, _, [URust_AST.UR_Arm
                        (URust_AST.P_Slice
                          ([URust_AST.SI_BoundRest ("tail", _, _, _)], _), NONE, _)], _)) => ()
                  | _ => error "slice pattern malformed audit: parser did not recover")
             in () end)
    fun reject_pattern pattern =
      reject ("match_case \<llangle>undefined\<rrangle> { " ^ pattern ^ " => () }")
    fun reject_positioned (pattern, diagnostic, needle, count) =
      let
        val text = "// \<alpha> before malformed pattern\nmatch_case \<llangle>undefined\<rrangle> { " ^
          pattern ^ " => () }"
        val expected = token_position text needle count
        val _ =
          (case Exn.result parse text of
             Exn.Res _ => error ("slice pattern malformed audit: accepted " ^ quote pattern)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let
                   val message = Runtime.exn_message exn
                   val plain = XML.content_of (YXML.parse_body message)
                   val _ =
                     if String.isSubstring diagnostic plain then ()
                     else error ("slice pattern malformed audit: diagnostic changed: " ^ message)
                 in
                   if member (op =) (diagnostic_spans message) (span expected) then ()
                   else error ("slice pattern malformed audit: token range changed: " ^ message)
                 end)
      in
        ignore (parse "match_case \<llangle>undefined\<rrangle> { [tail @ ..,] => () }")
      end

    val _ =
      List.app reject_positioned
        [("[tail @ .]", "syntax error: deleting  . ] =>", ".", 0),
         ("[tail @ ...]", "syntax error: deleting  . ] =>", ".", 2),
         ("[tail @ ..,,]", "syntax error: deleting  , ] =>", ",", 1),
         ("[Scope::tail @ ..]", "syntax error: deleting  @ .. ]", "@", 0),
         ("[(tail @ ..)]", "syntax error: deleting  .. ) ]", "..", 0),
         ("[outer @ tail @ ..]", "syntax error: deleting  .. ] =>", "..", 0)]

    val _ =
      List.app reject_pattern
        ["[(tail @ ..)]", "[(tail) @ ..]", "[outer @ tail @ ..]", "[tail @ (..)]",
         "[Scope::tail @ ..]", "[tail::Part @ ..]",
         "[mut tail @ ..]", "[ref tail @ ..]", "[ref mut tail @ ..]",
         "[tail @ mut ..]", "[tail @ ref ..]", "[&tail @ ..]",
         "[tail @ .]", "[tail @ ...]", "[tail @ ....]", "[tail @ ..=]",
         "[...]", "[....]", "[..=]",
         "[tail @ ..=last]", "[tail @ .. last]", "[first tail @ ..]",
         "[, tail @ ..]", "[tail @ ..,,]", "[tail @ .., , last]",
         "[tail @ ]", "[@ ..]", "tail @ ..", "Some(tail @ ..)",
         "(tail @ .., other)", "Head { field: tail @ .. }",
         "..", "Some(..)", "(.., other)", "Head { field: .. }"]
    val _ =
      List.app reject
        ["match_case \<llangle>undefined\<rrangle> { [tail @ ..] => () _ => () }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} [tail @ ..] => {} }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => (),, }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..",
         "match_case \<llangle>undefined\<rrangle> { [tail @",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] =>"]

    val eof_text = "// \<alpha> before EOF\nmatch_case \<llangle>undefined\<rrangle> { [tail @ .."
    val eof = Position.symbol_explode eof_text start
    val _ =
      (case Exn.result parse eof_text of
         Exn.Res _ => error "slice pattern malformed audit: incomplete slice accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val plain = XML.content_of (YXML.parse_body message)
               val expected_here = XML.content_of (YXML.parse_body (Position.here eof))
               val _ =
                 if String.isSubstring "syntax error found at end of input" plain andalso
                    String.isSubstring expected_here plain
                 then ()
                 else error ("slice pattern malformed audit: EOF diagnostic moved: " ^ message)
             in () end)
    val _ = ignore (parse "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => (), }")
  in
  end
\<close>

section\<open> Retained binding-site restrictions \<close>

text\<open>
Rest-only slices and recursive aliases are ordinary let/for features. Closure formals, local const,
mutable bindings, and reference binding modes retain their separate policies. A supplied list value
cannot make a pattern requiring an element irrefutable.
\<close>

urust_expr_rejects
  \<open> |[tail @ ..]| () \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> |whole @ value| () \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> let mut [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> invalid mutable binding pattern \<close>

urust_expr_rejects
  \<open> let mut whole @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> invalid mutable binding pattern \<close>

urust_expr_rejects
  \<open> let mut ([tail @ ..], other) = \<llangle>([] :: nat list, (0 :: nat, TNil))\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> const [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> const whole @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [first, tail @ ..] = \<llangle>[1 :: nat, 4, 9]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [tail @ .., last] = \<llangle>[1 :: nat, 4, 9]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [first] = \<llangle>[1 :: nat]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open>
    let (whole @ [first, tail @ ..], other) =
      \<llangle>([1 :: nat, 4, 9], (0 :: nat, TNil))\<rrangle>; ()
  \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> for whole @ [first, tail @ ..] in \<llangle>[[1 :: nat, 4, 9]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> for [tail @ .., last] in \<llangle>[[1 :: nat, 4, 9]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> for whole @ [first] in \<llangle>[[1 :: nat]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> let whole @ &[tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> reference patterns are not implemented \<close>

urust_expr_rejects
  \<open> for whole @ &mut [tail @ ..] in \<llangle>[[] :: nat list]\<rrangle> { () } \<close>
  \<open> reference patterns are not implemented \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>[] :: nat list\<rrangle> { [tail @ ..] \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>

urust_expr_rejects
  \<open> let tail @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> duplicate pattern binder "tail" \<close>

urust_expr_rejects
  \<open> for tail @ [tail @ ..] in \<llangle>[[] :: nat list]\<rrangle> { () } \<close>
  \<open> duplicate pattern binder "tail" \<close>

section\<open> Rest-only slice list type constraints \<close>

text\<open>
Both named and bare rest-only slices require a list at every structural depth, including when the
matcher is total and can use a direct abstraction. These sources use supported patterns and binding
sites; rejection must come from checked type elaboration. The bodies leave captures unconstrained
so they cannot impose the missing list type on behalf of the pattern.
\<close>

urust_expr_rejects
  \<open> let [rest@..] = true; rest \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match true { [rest@..] \<Rightarrow> rest } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match true { [..] \<Rightarrow> () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some([rest@..]) \<Rightarrow> rest,
      _ \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match_case \<llangle>Some True\<rrangle> { Some([..]) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> for [rest@..] in \<llangle>[True]\<rrangle> { let _ = rest; () } \<close>
  \<open> no instances \<close>

urust_expr_rejects
  \<open> for [..] in \<llangle>[True]\<rrangle> { () } \<close>
  \<open> no instances \<close>

text\<open>
Iteration reports this mismatch at checked adhoc overloading: no \<open>into_iter\<close> instance can
iterate booleans with a list-pattern body. The same iterable with an ordinary binder elaborates.
\<close>

ML_val\<open>
  ignore (Parser_Test_Elaboration.expression \<^context>
    (Parser_Lex_Util.text_source "for item in \<llangle>[True]\<rrangle> { () }"))
\<close>

urust_expr_rejects
  \<open> let [rest@..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let outer @ inner @ [rest@..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let outer @ inner @ [..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> if let [rest@..] = true { () } else { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> if let [..] = true { () } else { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [rest@..] = true else { () }; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [..] = true else { () }; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [rest@..] = true { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [..] = true { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(_) | Some([..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(rest) | Some([rest@..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

text\<open>
Every source arm retains its type constraints, including arms covered by an earlier singleton
constructor arm. Captures must also have the same type across alternatives, even when unused.
\<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(_) \<Rightarrow> (),
      Some([..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some [11 :: nat]\<rrangle> {
      Some([rest@..]) | Some([rest]) \<Rightarrow> rest,
      None \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some [11 :: nat]\<rrangle> {
      Some([rest@..]) | Some([rest]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some ([11 :: nat], [True], TNil)\<rrangle> {
      Some(([rest@..], _)) | Some((_, [rest@..])) \<Rightarrow> rest,
      None \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some ([11 :: nat], [True], TNil)\<rrangle> {
      Some(([rest@..], _)) | Some((_, [rest@..])) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

section\<open> Unrelated HOL lambda term shapes \<close>

text\<open>
The native cleanup of generated pattern typing witnesses must preserve ordinary HOL abstractions
and checked applications whose binder names share the witness prefix. These checks use explicitly
named, concretely typed abstractions and hand-built expected syntax trees. Ordinary HOL checking
beta-normalizes applications. Each checked prefix-named term must also agree with its checked
non-prefix reference.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val nat_type = \<^typ>\<open>nat\<close>
    val eleven = \<^term>\<open>11 :: nat\<close>
    val used = Abs ("_urust_pattern_type_probe_used", nat_type, Bound 0)
    val unused = Abs ("_urust_pattern_type_probe_unused", nat_type, \<^term>\<open>True\<close>)
    val used_reference = Abs ("ordinary_lambda_used", nat_type, Bound 0)
    val unused_reference = Abs ("ordinary_lambda_unused", nat_type, \<^term>\<open>True\<close>)

    fun unchanged label raw expected reference =
      let
        val actual = Syntax.check_term ctxt raw |> Term_Position.strip_positions
        val baseline = Syntax.check_term ctxt reference |> Term_Position.strip_positions
      in
        if Term.aconv (actual, expected) andalso Term.aconv (actual, baseline) then ()
        else error ("slice pattern HOL lambda shape audit: " ^ label ^
          "\nactual: " ^ Syntax.string_of_term ctxt actual ^
          "\nbaseline: " ^ Syntax.string_of_term ctxt baseline ^
          "\nexpected: " ^ Syntax.string_of_term ctxt expected)
      end

    val _ = unchanged "used abstraction" used used used_reference
    val _ = unchanged "unused abstraction" unused unused unused_reference
    val _ = unchanged "used application" (used $ eleven) eleven (used_reference $ eleven)
    val _ = unchanged "unused application" (unused $ eleven) \<^term>\<open>True\<close>
      (unused_reference $ eleven)
  in
    val _ = writeln "Unrelated HOL lambda abstractions and applications retain their term shapes"
  end
\<close>

end
