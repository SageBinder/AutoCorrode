theory Parser_Impl_Turbofish
  imports
    Parser_Impl_AST
    Parser_Utils
begin

ML\<open>
signature URUST_TURBOFISH =
sig
  type table
  val empty: table
  val scan: Proof.context -> Parser_Lex_Util.source_layout -> table
  val lookup:
    table -> int ->
      {arguments: URust_AST.generic_args,
       open_offset: int,
       close_offset: int,
       comma_offsets: int list} option
end

(*
  Turbofish payloads are unquoted Isabelle/HOL regions. This component discovers those regions without
  parsing them semantically, then records the original positioned argument slices for the generated
  lexer. Exact complete-path notation lookup can therefore precede HOL parsing.

  The abstract table is keyed by the raw lexer offset of `::`. Its representation, outer traversal,
  source slicing, inner token indexing, delimiter balancing, candidate-prefix recovery, and diagnostics
  remain private. Physical Unicode is masked only in the Syntax.tokenize view; all returned sources and
  positions come from the original shared source layout.
*)
structure URust_Turbofish :> URUST_TURBOFISH =
struct
  datatype entry =
    Entry of
      {arguments: URust_AST.generic_args,
       open_offset: int,
       close_offset: int,
       comma_offsets: int list}

  type table = entry Inttab.table

  val empty = Inttab.empty

  fun lookup table offset =
    (case Inttab.lookup table offset of
       SOME (Entry result) => SOME result
     | NONE => NONE)

  type source_view =
    {layout: Parser_Lex_Util.source_layout,
     source_offset: int option}

  type group_result =
    {close_index: int,
     resume_index: int,
     span_stop: Position.T,
     arguments: Input.source list,
     comma_offsets: int list}

  datatype outer_step =
      Advance of int
    | Candidate of {separator_index: int, open_index: int}
    | End

  fun make_source_view layout =
    {layout = layout,
     source_offset =
       Position.offset_of
         (Parser_Lex_Util.boundary_position layout 0)}

  fun layout_of ({layout, ...} : source_view) = layout
  fun symbol_count view =
    Parser_Lex_Util.symbol_count (layout_of view)
  fun source_symbol view index =
    Parser_Lex_Util.source_symbol (layout_of view) index
  fun symbol view index = #1 (source_symbol view index)
  fun boundary_position view index =
    Parser_Lex_Util.boundary_position (layout_of view) index
  fun raw_offset view index =
    Parser_Lex_Util.raw_start (layout_of view) index
  fun source_has_offsets ({source_offset, ...} : source_view) =
    is_some source_offset

  fun starts_pair view index first second =
    index + 1 < symbol_count view andalso
      symbol view index = first andalso
      symbol view (index + 1) = second

  fun blank s =
    member (op =) [" ", "\t", "\r", "\n"] s

  fun skip_blanks view index =
    if index < symbol_count view andalso blank (symbol view index)
    then skip_blanks view (index + 1)
    else index

  fun trim_left view left right =
    if left < right andalso blank (symbol view left)
    then trim_left view (left + 1) right
    else left

  fun trim_right view left right =
    if left < right andalso blank (symbol view (right - 1))
    then trim_right view left (right - 1)
    else right

  fun symbol_slice view left right =
    let
      fun collect index fragments =
        if index >= right then String.concat (rev fragments)
        else collect (index + 1) (symbol view index :: fragments)
    in collect left [] end

  fun original_symbol_list view left right =
    if left >= right then []
    else source_symbol view left :: original_symbol_list view (left + 1) right

  fun source_range view left right =
    let
      val first = trim_left view left right
      val last = trim_right view first right
      val _ =
        if first < last then ()
        else
          error ("urust_expr: empty turbofish argument" ^
            Position.here (boundary_position view left))
    in
      Input.source true
        (symbol_slice view first last)
        (Position.range
          (boundary_position view first, boundary_position view last))
    end

  fun mask_physical_unicode symbols =
    map
      (fn (source as (s, position)) =>
        if Symbol.is_utf8 s then ("x", position) else source)
      symbols

  fun token_symbol_list view left right =
    (if source_has_offsets view then original_symbol_list view left right
     else
       let
         fun collect index =
           if index >= right then []
           else
             (symbol view index,
              Position.make0 1 (index + 1) 0 "" ""
                "urust-turbofish-token-index") ::
               collect (index + 1)
       in collect left end)
    |> mask_physical_unicode

  fun tokenize ctxt view left right =
    Syntax.tokenize (Proof_Context.syntax_of ctxt) {raw = false}
      (token_symbol_list view left right)

  fun token_index view position =
    (case Position.offset_of position of
       SOME offset =>
         if source_has_offsets view
         then offset - the (#source_offset view)
         else offset - 1
     | NONE =>
         error "internal turbofish token lost its source position")

  fun index_tokens view slice_start slice_stop tokens =
    let
      fun build index [] indexed =
            if index = slice_stop then rev indexed
            else error "internal turbofish token/source coverage mismatch"
        | build index (token :: rest) indexed =
            let
              val (token_start, token_stop) =
                apply2 (token_index view) (Lexicon.range_of_token token)
              val _ =
                if token_start = index andalso
                    token_start <= token_stop andalso
                    token_stop <= slice_stop
                then ()
                else error "internal turbofish token/source range mismatch"
            in
              build token_stop rest
                ((token, token_start, token_stop) :: indexed)
            end
    in build slice_start tokens [] end

  fun token_position view token fallback =
    let val position = #1 (Lexicon.range_of_token token)
    in
      if source_has_offsets view
      then position
      else boundary_position view fallback
    end

  fun legal_after_close view index =
    let val next = skip_blanks view (index + 1)
    in
      next = symbol_count view orelse
      starts_pair view next ":" ":" orelse
      member (op =)
        ["(", ".", "[", "?", "!", ",", ")", "]", "}",
         ";", "+", "-", "*", "/", "%", "&", "|", "^"]
        (symbol view next)
    end

  fun closing_delimiter "(" = SOME ")"
    | closing_delimiter "[" = SOME "]"
    | closing_delimiter "{" = SOME "}"
    | closing_delimiter _ = NONE

  fun is_closing_delimiter s =
    member (op =) [")", "]", "}"] s

  fun starts_hol_operand (token, _, _) =
    (case Lexicon.kind_of_token token of
       Lexicon.Ident => true
     | Lexicon.Long_Ident => true
     | Lexicon.Var => true
     | Lexicon.Type_Ident => true
     | Lexicon.Type_Var => true
     | Lexicon.Num => true
     | Lexicon.Float => true
     | Lexicon.Str => true
     | Lexicon.String => true
     | Lexicon.Cartouche => true
     | _ => false)

  fun next_proper [] = NONE
    | next_proper ((indexed as (token, _, _)) :: rest) =
        if Lexicon.is_proper token then SOME indexed
        else next_proper rest

  fun finish_group view close_index resume_index argument_start commas close_token =
    let
      val pieces =
        rev ((argument_start, close_index, NONE) :: commas)
      val arguments =
        map (fn (left, right, _) => source_range view left right) pieces
      val comma_offsets =
        map_filter
          (fn (_, _, comma) => Option.map (raw_offset view) comma)
          pieces
      val token_stop = #2 (Lexicon.range_of_token close_token)
      val span_stop =
        if source_has_offsets view
        then token_stop
        else boundary_position view resume_index
    in
      SOME
        {close_index = close_index,
         resume_index = resume_index,
         span_stop = span_stop,
         arguments = arguments,
         comma_offsets = comma_offsets}
    end

  fun balance_token_group view content_start required_close tokens =
    let
      val indexed =
        index_tokens view content_start
          (case required_close of
             SOME close => close + 1
           | NONE => symbol_count view)
          tokens

      fun mismatch token index =
        error ("urust_expr: mismatched delimiter in turbofish" ^
          Position.here (token_position view token index))

      fun loop _ _ _ [] = NONE
        | loop stack argument_start commas
            ((token, left, right) :: rest) =
            if not (Lexicon.is_literal token) then
              loop stack argument_start commas rest
            else
              let val text = Lexicon.str_of_token token in
                (case closing_delimiter text of
                   SOME expected =>
                     loop (expected :: stack) argument_start commas rest
                 | NONE =>
                     if is_closing_delimiter text then
                       (case stack of
                          expected :: remaining =>
                            if expected = text then
                              loop remaining argument_start commas rest
                            else mismatch token left
                        | [] => mismatch token left)
                     else if text = "," andalso null stack then
                       loop stack right
                         ((argument_start, left, SOME left) :: commas)
                         rest
                     else if text = ">" andalso null stack andalso
                         legal_after_close view left andalso
                         (case required_close of
                            SOME close => left = close
                          | NONE => true) andalso
                         not
                           (case next_proper rest of
                              SOME next => starts_hol_operand next
                            | NONE => false)
                     then
                       finish_group view left right
                         argument_start commas token
                     else
                       loop stack argument_start commas rest)
              end
    in loop [] content_start [] indexed end

  fun candidate_closes view content_start =
    let
      fun collect index closes =
        if index >= symbol_count view then rev closes
        else if symbol view index = ">" andalso
            legal_after_close view index then
          collect (index + 1) (index :: closes)
        else collect (index + 1) closes
    in collect content_start [] end

  fun attempt_candidate_prefix ctxt view content_start close =
    (case Exn.capture
        (fn () => tokenize ctxt view content_start (close + 1)) () of
       Exn.Res tokens =>
         balance_token_group view content_start (SOME close) tokens
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else NONE)

  fun scan_candidate_prefixes ctxt view content_start failed closes =
    (case closes of
       [] => failed ()
     | close :: rest =>
         (case attempt_candidate_prefix ctxt view content_start close of
            SOME result => result
          | NONE =>
              scan_candidate_prefixes ctxt view content_start failed rest))

  fun scan_group ctxt view group_start =
    let
      val content_start = group_start + 1
      fun unterminated () =
        error ("urust_expr: unterminated turbofish" ^
          Position.here (boundary_position view group_start))
      val closes = candidate_closes view content_start
    in
      (case Exn.capture
          (fn () =>
            tokenize ctxt view content_start (symbol_count view)) () of
         Exn.Res tokens =>
           (case
               balance_token_group view content_start NONE tokens of
              SOME result => result
            | NONE =>
                scan_candidate_prefixes ctxt view content_start
                  unterminated closes)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             scan_candidate_prefixes ctxt view content_start
               (fn () => Exn.reraise exn) closes)
    end

  fun skip_line_comment view index =
    let
      fun loop current =
        if current >= symbol_count view orelse
            symbol view current = "\n" then current
        else loop (current + 1)
    in loop (index + 2) end

  fun skip_outer_string view index =
    let
      fun loop current =
        if current >= symbol_count view then symbol_count view
        else if symbol view current = "\\" then
          loop (Int.min (current + 2, symbol_count view))
        else if symbol view current = "\"" then current + 1
        else loop (current + 1)
    in loop (index + 1) end

  val value_open = "\<llangle>"
  val value_close = "\<rrangle>"
  val expression_marker = "\<epsilon>"

  fun skip_value_antiquotation view index =
    let
      fun loop depth current =
        if current >= symbol_count view then
          error ("urust_expr: unterminated value antiquotation" ^
            Position.here (boundary_position view index))
        else if symbol view current = value_open then
          loop (depth + 1) (current + 1)
        else if symbol view current = value_close then
          if depth = 1 then current + 1
          else loop (depth - 1) (current + 1)
        else loop depth (current + 1)
    in loop 1 (index + 1) end

  fun skip_cartouche view index =
    let
      fun loop depth current =
        if current >= symbol_count view then NONE
        else if symbol view current = Symbol.open_ then
          loop (depth + 1) (current + 1)
        else if symbol view current = Symbol.close then
          if depth = 1 then SOME (current + 1)
          else loop (depth - 1) (current + 1)
        else loop depth (current + 1)
    in loop 1 (index + 1) end

  fun classify_outer_step view index =
    if index >= symbol_count view then End
    else if symbol view index = "\"" then
      Advance (skip_outer_string view index)
    else if starts_pair view index "/" "/" then
      Advance (skip_line_comment view index)
    else if symbol view index = value_open then
      Advance (skip_value_antiquotation view index)
    else if symbol view index = expression_marker andalso
        index + 1 < symbol_count view andalso
        symbol view (index + 1) = Symbol.open_ then
      (case skip_cartouche view (index + 1) of
         SOME stop => Advance stop
       | NONE => End)
    else if symbol view index = Symbol.open_ then
      (case skip_cartouche view index of
         SOME stop => Advance stop
       | NONE => End)
    else if starts_pair view index ":" ":" then
      let val open_index = skip_blanks view (index + 2)
      in
        if open_index < symbol_count view andalso
            symbol view open_index = "<" then
          Candidate
            {separator_index = index, open_index = open_index}
        else Advance (index + 2)
      end
    else Advance (index + 1)

  fun record_group view separator_index open_index
      ({close_index, resume_index, span_stop,
        arguments, comma_offsets} : group_result) table =
    let
      val span =
        Position.range_position
          (boundary_position view separator_index, span_stop)
      val entry =
        Entry
          {arguments = URust_AST.Generic_Args (arguments, span),
           open_offset = raw_offset view open_index,
           close_offset = raw_offset view close_index,
           comma_offsets = comma_offsets}
    in
      (resume_index,
       Inttab.update (raw_offset view separator_index, entry) table)
    end

  fun scan ctxt layout =
    let
      val view = make_source_view layout
      fun traverse index table =
        (case classify_outer_step view index of
           End => table
         | Advance next => traverse next table
         | Candidate {separator_index, open_index} =>
             let
               val (next, table') =
                 record_group view separator_index open_index
                   (scan_group ctxt view open_index) table
             in traverse next table' end)
    in traverse 0 empty end
end
\<close>

end
