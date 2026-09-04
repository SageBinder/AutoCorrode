(* Language-agnostic lexer and elaborator support for ml_lex_yacc parsers. Per-lexer `set` shadows and
   `Tokens.*` constructors remain inside each generated lexer's SML environment. *)

theory Parser_Utils
  imports Main
begin

text\<open> The generated lexer reports character offsets, while Isabelle positions index symbols. Build one
source layout per parse and use binary search for token positions. \<close>
ML\<open>
structure Parser_Lex_Util =
struct
  type source_layout =
    {source : Input.source,
     text : string,
     symbols : Symbol_Pos.T vector,
     raw_starts : int vector,
     fallback : Position.T,
     raw_length : int,
     eof : Position.T}

  type position_map = source_layout

  fun content_source text range =
    Input.source false text range

  fun positioned_content_source text start =
    content_source text
      (Position.range (start, Position.symbol_explode text start))

  fun text_source text =
    content_source text Position.no_range

  fun comparable_offsets (left, right) =
    (case (Position.offset_of left, Position.offset_of right) of
       (SOME left_offset, SOME right_offset) =>
         SOME (left_offset = right_offset)
     | _ => NONE)

  fun cartouche_source token =
    let
      val content = Token.content_of token
      val token_start = Token.pos_of token
      val token_stop = #2 (Token.range_of [token])
      val content_start =
        Position.symbol_explode Symbol.open_ token_start
      val content_stop =
        Position.symbol_explode content content_start
      val expected_token_stop =
        Position.symbol_explode Symbol.close content_stop
      val _ =
        (case comparable_offsets
            (expected_token_stop, token_stop) of
           SOME false =>
             error
               ("cartouche content range does not match token range" ^
                 Position.here token_start)
         | _ => ())
    in
      content_source content
        (Position.range (content_start, content_stop))
    end

  fun make_source_layout source =
    let
      val symbols =
        Vector.fromList (Input.source_explode source)
      val symbol_count = Vector.length symbols
      fun build index raw_offset starts =
        if index = symbol_count then
          (Vector.fromList (rev (raw_offset :: starts)), raw_offset)
        else
          build (index + 1)
            (raw_offset + size (#1 (Vector.sub (symbols, index))))
            (raw_offset :: starts)
      val (raw_starts, raw_length) = build 0 0 []
    in
      {source = source,
       text = Input.text_of source,
       symbols = symbols,
       raw_starts = raw_starts,
       fallback = Input.pos_of source,
       raw_length = raw_length,
       eof = #2 (Input.range_of source)}
    end

  fun make_position_map source =
    make_source_layout source

  fun source_of ({source, ...} : source_layout) = source
  fun text_of ({text, ...} : source_layout) = text
  fun symbols_of ({symbols, ...} : source_layout) = symbols
  fun symbol_count ({symbols, ...} : source_layout) = Vector.length symbols
  fun source_symbol ({symbols, ...} : source_layout) index =
    Vector.sub (symbols, index)
  fun raw_start ({raw_starts, ...} : source_layout) index =
    Vector.sub (raw_starts, index)
  fun raw_length ({raw_length, ...} : source_layout) = raw_length
  fun fallback_position ({fallback, ...} : source_layout) = fallback
  fun eof_position ({eof, ...} : source_layout) = eof
  fun boundary_position (layout : source_layout) index =
    if index < symbol_count layout
    then #2 (source_symbol layout index)
    else eof_position layout

  fun fixed_pos
      (layout as
        {symbols, raw_starts, fallback, raw_length, eof, ...} : position_map)
      yypos =
    if yypos >= raw_length then eof
    else if Vector.length symbols = 0 then fallback
    else
      let
        val target = Int.max (0, yypos)
        val n = Vector.length symbols
        fun search lo hi =
          if lo + 1 >= hi then lo
          else
            let val mid = (lo + hi) div 2
            in
              if Vector.sub (raw_starts, mid) <= target
              then search mid hi
              else search lo mid
            end
        val i = search 0 n
      in #2 (source_symbol layout i) end

  fun source_slice
      (layout as {text, raw_length, ...} : source_layout)
      left right =
    if 0 <= left andalso left < right andalso right <= raw_length then
      Input.source true
        (String.substring (text, left, right - left))
        (Position.range
          (fixed_pos layout left, fixed_pos layout right))
    else
      error
        ("invalid parser source slice [" ^ string_of_int left ^ ", " ^
          string_of_int right ^ ")")

  fun text_range pos_map (yypos, text) =
    let val start = fixed_pos pos_map yypos
    in Position.range (start, Position.symbol_explode text start) end

  fun exclusive_end pos =
    (case Position.end_offset_of pos of
       SOME stop =>
         let
           val {line, props = {label, file, id}, ...} = Position.dest pos
         in Position.make0 line stop 0 label file id end
     | NONE => pos)

  fun source_line_column_with_layout layout position =
    let
      val symbols = Vector.foldr op :: [] (symbols_of layout)
      val target_offset = Position.offset_of position

      fun at_target (_, symbol_position) =
        (case (Position.offset_of symbol_position, target_offset) of
           (SOME symbol_offset, SOME target) =>
             symbol_offset = target
         | _ => symbol_position = position)

      fun prefix [] accumulated = rev accumulated
        | prefix (symbol :: rest) accumulated =
            if at_target symbol
            then rev accumulated
            else prefix rest (symbol :: accumulated)

      fun advance [] line column = (line, column)
        | advance ((symbol, _) :: rest) line column =
            if symbol = "\n"
            then advance rest (line + 1) 1
            else advance rest line (column + 1)

      val start_line =
        the_default 1
          (Position.line_of (fallback_position layout))
    in
      advance (prefix symbols []) start_line 1
    end

  fun source_line_column source position =
    source_line_column_with_layout
      (make_source_layout source) position

  fun print_error_with_layout layout (message, start, stop) =
    let
      val position =
        Position.range_position
          (Position.range (start, stop))
      val _ = Position.report position Markup.error
      val (line, column) =
        source_line_column_with_layout layout start
    in
      error
        ("Parse Error at line " ^ string_of_int line ^
         ", column " ^ string_of_int column ^ ": " ^
         message ^ Position.here start)
    end

  fun print_error source error =
    print_error_with_layout (make_source_layout source) error

  fun parse_source_with_layout
      parse make_lexer get same_token eof layout =
    let
      val input_text = text_of layout
      val eof_position = eof_position layout

      fun canonical_position position =
        if position = Position.none
        then eof_position
        else position

      fun invoke lexstream =
        parse
          (0, lexstream,
           fn (message, start, stop) =>
             print_error_with_layout layout
               (message,
                canonical_position start,
                canonical_position stop),
           ())

      val parsed = Unsynchronized.ref false
      fun input_string _ =
        if !parsed then ""
        else (parsed := true; input_text)

      val lexer = make_lexer input_string
      val dummy_eof =
        eof (eof_position, eof_position)

      fun loop lexer =
        let
          val (result, lexer') = invoke lexer
          val (next_token, lexer'') = get lexer'
        in
          if same_token (next_token, dummy_eof)
          then result
          else loop lexer''
        end
    in
      loop lexer
    end

  fun parse_source
      parse make_lexer get same_token eof source =
    parse_source_with_layout
      parse make_lexer get same_token eof
      (make_source_layout source)

  fun report_range ((start, stop), markup, typ) =
    let val pos = Position.range_position (start, stop)
    in
      Position.report pos markup;
      Position.report_text pos Markup.typing typ
    end

  fun report_text pos_map (yypos, text, markup, typ) =
    if text = "" then () else report_range (text_range pos_map (yypos, text), markup, typ)

  fun tokF pos_map (yypos, yytext, markup, typ, cons) =
    let val range = text_range pos_map (yypos, yytext)
    in report_range (range, markup, typ); cons range end

  (* Isabelle_Lex-Yacc's tok_val uses the start for both ends; preserve the real right position. *)
  fun tok_valF pos_map (yypos, yytext, markup, typ, cons, value) =
    let val range as (start, stop) = text_range pos_map (yypos, yytext)
    in report_range (range, markup, typ); cons (value, start, stop) end

  fun ranged_value pos_map report markup typ (yypos, yytext) =
    let
      val range as (start, stop) = text_range pos_map (yypos, yytext)
      val value =
        (yytext, pos_map, yypos, yypos + size yytext)
      val _ = if report then report_range (range, markup, typ) else ()
    in (value, start, stop) end

  fun ident_pos pos_map (yypos, yytext) =
    Position.range_position (text_range pos_map (yypos, yytext))
end
\<close>

ML_val\<open>
  val source_start = Position.make0 1 10 0 "" "" ""
  val source_text = "a\<Rightarrow>b"
  val source_stop = Position.symbol_explode source_text source_start
  val source =
    Parser_Lex_Util.content_source source_text
      (Position.range (source_start, source_stop))
  val pos_map = Parser_Lex_Util.make_position_map source
  val arrow = "\<Rightarrow>"
  val (start, stop) = Parser_Lex_Util.text_range pos_map (1, arrow)
  val following = Parser_Lex_Util.fixed_pos pos_map (1 + size arrow)
  val _ =
    if Position.offset_of start = SOME 11 andalso
       Position.end_offset_of start = SOME 12 andalso
       Position.offset_of stop = SOME 12 andalso
       Position.offset_of following = SOME 12 andalso
       Position.offset_of
         (Parser_Lex_Util.fixed_pos pos_map (size source_text)) =
         Position.offset_of source_stop
    then ()
    else error "Parser_Lex_Util did not map raw lexer offsets to Isabelle-symbol ranges"
\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("canonical parser source audit: " ^ message)

    fun offset position =
      the (Position.offset_of position)

    val token_start =
      Position.make0 4 20 0 "" "" ""
    val content = "a\<Rightarrow>b"
    val token_text =
      Symbol.open_ ^ content ^ Symbol.close
    val token =
      (case Token.explode
          Keyword.empty_keywords token_start token_text of
         [single] => single
       | _ => error "cartouche tokenization did not produce one token")
    val source =
      Parser_Lex_Util.cartouche_source token
    val (source_content, source_position) =
      Input.source_content source
    val (content_start, content_stop) =
      Input.range_of source
    val position_map =
      Parser_Lex_Util.make_position_map source
    val arrow_start =
      Parser_Lex_Util.fixed_pos position_map 1
    val arrow_middle =
      Parser_Lex_Util.fixed_pos position_map 2
    val final_start =
      Parser_Lex_Util.fixed_pos position_map
        (1 + size "\<Rightarrow>")
    val eof =
      Parser_Lex_Util.fixed_pos position_map
        (size content)
    val _ =
      assert "Token.content_of was not preserved exactly"
        (Input.text_of source = content andalso
         source_content = content)
    val _ =
      assert "canonical source remained delimited"
        (not (Input.is_delimited source))
    val _ =
      assert "source_content did not report the first content symbol"
        (offset source_position = offset content_start)
    val _ =
      assert "content range did not start after the opening delimiter"
        (offset content_start = offset token_start + 1)
    val _ =
      assert "raw offset zero did not map to the first content symbol"
        (offset
          (Parser_Lex_Util.fixed_pos position_map 0) =
          offset content_start)
    val _ =
      assert "multi-byte Isabelle symbol offsets drifted"
        (offset arrow_start = offset content_start + 1 andalso
         offset arrow_middle = offset arrow_start andalso
         offset final_start = offset arrow_start + 1)
    val _ =
      assert "raw content length did not map to EOF"
        (offset eof = offset content_stop)

    fun audit_short_source text =
      let
        val start =
          Position.make0 1 40 0 "" "" ""
        val stop =
          Position.symbol_explode text start
        val short_source =
          Parser_Lex_Util.positioned_content_source
            text start
        val short_map =
          Parser_Lex_Util.make_position_map short_source
      in
        assert ("short source EOF drifted for " ^ quote text)
          (offset
            (Parser_Lex_Util.fixed_pos short_map
              (size text)) =
            offset stop)
      end

    val _ = audit_short_source "x"
    val _ = audit_short_source "xy"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    fun assert message condition =
      if condition then ()
      else error ("shared parser source-layout audit: " ^ message)

    fun offset position =
      the (Position.offset_of position)

    val physical_club =
      Byte.bytesToString
        (Word8Vector.fromList [0wxE2, 0wx99, 0wxA3])
    val escaped_arrow = "\<Rightarrow>"
    val text = "a" ^ escaped_arrow ^ physical_club ^ "\nb"
    val start =
      Position.make0 11 200 0 "" "" "parser-source-layout-audit"
    val stop = Position.symbol_explode text start
    val source =
      Parser_Lex_Util.positioned_content_source text start
    val layout =
      Parser_Lex_Util.make_source_layout source
    val escaped_raw = 1
    val physical_raw = escaped_raw + size escaped_arrow
    val newline_raw = physical_raw + size physical_club
    val final_raw = newline_raw + 1

    val _ =
      assert "original source or text was not retained"
        (Input.string_of (Parser_Lex_Util.source_of layout) = text andalso
         Parser_Lex_Util.text_of layout = text)
    val _ =
      assert "positioned symbol vector changed source symbols"
        (map #1
          (Vector.foldr (op ::) []
            (Parser_Lex_Util.symbols_of layout)) =
          ["a", escaped_arrow, physical_club, "\n", "b"])
    val _ =
      assert "raw symbol starts or raw length changed"
        (map (Parser_Lex_Util.raw_start layout) (0 upto 5) =
          [0, escaped_raw, physical_raw, newline_raw,
           final_raw, size text] andalso
         Parser_Lex_Util.raw_length layout = size text)
    val _ =
      assert "ASCII raw boundary moved"
        (offset (Parser_Lex_Util.fixed_pos layout 0) = 200)
    val _ =
      assert "escaped-symbol raw interior did not map to one symbol"
        (offset
           (Parser_Lex_Util.fixed_pos layout escaped_raw) = 201 andalso
         offset
           (Parser_Lex_Util.fixed_pos layout
             (physical_raw - 1)) = 201)
    val _ =
      assert "physical-UTF8 raw interior did not map to one symbol"
        (offset
           (Parser_Lex_Util.fixed_pos layout physical_raw) = 202 andalso
         offset
           (Parser_Lex_Util.fixed_pos layout
             (newline_raw - 1)) = 202)
    val _ =
      assert "multiline line/column calculation changed"
        (Parser_Lex_Util.source_line_column_with_layout layout
          (Parser_Lex_Util.fixed_pos layout final_raw) = (12, 1))
    val _ =
      assert "EOF boundary changed"
        (offset
           (Parser_Lex_Util.fixed_pos layout (size text)) =
             offset stop andalso
         offset
           (Parser_Lex_Util.fixed_pos layout (size text + 10)) =
             offset stop andalso
         offset (Parser_Lex_Util.eof_position layout) = offset stop)

    val unpositioned =
      Parser_Lex_Util.make_source_layout
        (Parser_Lex_Util.text_source text)
    val _ =
      assert "unpositioned layout unexpectedly acquired offsets"
        (Position.offset_of
           (Parser_Lex_Util.fallback_position unpositioned) = NONE andalso
         Position.offset_of
           (Parser_Lex_Util.fixed_pos unpositioned physical_raw) =
             NONE andalso
         Position.offset_of
           (Parser_Lex_Util.eof_position unpositioned) = NONE)
    val _ =
      assert "position-map compatibility wrapper changed layout behavior"
        (Parser_Lex_Util.raw_length
           (Parser_Lex_Util.make_position_map source) =
         Parser_Lex_Util.raw_length layout)
  in
    val _ = ()
  end
\<close>

ML\<open>
structure Parser_Utils =
struct

type var_info = { free : term, def_pos : Position.T, id : int }

fun report_def kind ctxt id (x, def_pos) =
  (Context_Position.report ctxt def_pos Markup.bound;
   Context_Position.report ctxt def_pos
     (Position.make_entity_markup {def = true} id kind (x, def_pos)))

fun report_ref kind ctxt id (x, def_pos) use_pos =
  (Context_Position.report ctxt use_pos Markup.bound;
   Context_Position.report ctxt use_pos
     (Position.make_entity_markup {def = false} id kind (x, def_pos)))

fun bind_var kind ctxt (env : var_info Symtab.table) (x, def_pos) =
  let
    val id   = serial ()
    val _    = report_def kind ctxt id (x, def_pos)
    (* Source spelling belongs in the environment and markup, not in Free identity. Distinct
       identities prevent a later Term.lambda for a shadowing binder from capturing an outer
       same-spelled local that has been placed in a shared continuation. *)
    val free =
      Free ("_urust_local_" ^ string_of_int id ^ "_" ^ x, dummyT)
  in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

(* Do not represent anonymous binders with invented Frees: such a name can capture a source binder held
   only in the elaboration environment. *)
fun anon_abs body = Abs (Name.uu, dummyT, body)

(* Overlay binding markup after the HOL parser has marked the antiquotation body. *)
fun mark_bound kind ctxt (env : var_info Symtab.table) src =
  let
    fun is_start c = Symbol.is_ascii_letter c orelse c = "_"
    fun is_cont c  = is_start c orelse Symbol.is_ascii_digit c
    fun span [] = ([], [])
      | span (sp :: r) =
          if is_cont (#1 sp) then let val (a, b) = span r in (sp :: a, b) end else ([], sp :: r)
    fun go [] = ()
      | go (sp :: r) =
          if is_start (#1 sp) then
            let
              val (idsyms, rest) = span (sp :: r)
              val nm = Symbol_Pos.content idsyms
            in
              (case Symtab.lookup env nm of
                 SOME {def_pos, id, ...} =>
                   report_ref kind ctxt id (nm, def_pos) (Position.range_position (Symbol_Pos.range idsyms))
               | NONE => ());
              go rest
            end
          else go r
  in go (Input.source_explode src) end

(* Parse lexical binders through fresh internal fixes, then restore their source Frees. Variants avoid
   collisions with same-named HOL context fixes while still shadowing constants during parsing. *)
fun parse_antiq kind ctxt env src =
  let
    val names = Symtab.keys env
    val (variants, ctxt') = Variable.variant_fixes names ctxt
    fun lexical_free name =
      (case Symtab.lookup env name of
         SOME {free, ...} => free
       | NONE => error ("internal missing antiquotation binder " ^ quote name))
    val replacements =
      Symtab.make (map2 (fn name => fn variant => (variant, lexical_free name)) names variants)
    fun restore (free as Free (name, _)) =
          the_default free (Symtab.lookup replacements name)
      | restore atom = atom
    val t =
      Syntax.parse_term ctxt' (Syntax.implode_input src)
      |> Term.map_aterms restore
  in mark_bound kind ctxt env src; t end

(* Generated parsers share mutable Isabelle_Lex-Yacc runtime state. *)
val parser_lock = Synchronized.var "parser_lock" ()
fun with_parser_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result parser_lock (fn () => (f (), ()))

end
\<close>

end
