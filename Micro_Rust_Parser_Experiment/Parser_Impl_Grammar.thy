theory Parser_Impl_Grammar
  imports
    Parser_Impl_AST
    Parser_Utils
    "Isabelle_Lex-Yacc.LexYacc"
begin

SML_import \<open> structure URust_AST = URust_AST \<close>
SML_import \<open> structure Input = struct open Input end \<close>       \<comment>\<open> for the corrected position map \<close>
SML_import \<open> structure Position = struct open Position end \<close> \<comment>\<open> report / range / T \<close>
SML_import \<open> structure Markup = struct open Markup end \<close>     \<comment>\<open> token reports \<close>
SML_import \<open> structure Symbol = struct open Symbol end \<close>     \<comment>\<open> partial lexeme reports \<close>
SML_import \<open> structure Inttab = Inttab \<close>

ML\<open>
signature URUST_GRAMMAR =
sig
  datatype turbofish =
    Turbofish of
      {arguments: URust_AST.generic_args,
       open_offset: int,
       close_offset: int,
       comma_offsets: int list}
  val scan_turbofish: Proof.context -> Input.source -> turbofish Inttab.table
  val lex_error: string -> Position.T -> 'a
  val string_error: Position.T -> 'a
  val antiquotation_error: string -> Position.T -> 'a
end

(*
  URust_Grammar owns the handwritten boundary used by the generated uRust lexer. It exposes the
  per-source turbofish scan and the source-facing failures raised directly by lexer actions. It is the
  boundary between lexer actions, which run in the generated SML environment, and Isabelle's
  positioned ERROR diagnostics.  It does not decide which input is malformed, recover from an error,
  report parser conflicts, or validate the AST; those responsibilities remain with the lexer rules,
  the joined parser, and later elaboration modules.

  The generated lexer may rely on these public, non-returning functions:

    * lex_error text pos raises an ERROR for an unrecognized source fragment.  The message retains the
      `urust_expr` command prefix, quotes text, and appends Position.here pos so the rejection is
      clickable.  In particular, the catch-all lexer rule must call this function rather than skip
      input.
    * string_error pos raises the positioned malformed-or-unterminated-string diagnostic at the
      opening quote.
    * antiquotation_error kind pos raises the positioned unterminated-antiquotation diagnostic at the
      opening delimiter.  Lexer callers supply the source-facing kind, currently "value" or
      "expression".

  All three functions have result type 'a because they always raise via error.  Their exact string
  assembly and use of quote are implementation details, subject to the message and position contracts
  above.  The SML_import below only makes this Isabelle/ML-owned interface available to generated lexer
  code; it does not create a second owner.
*)
structure URust_Grammar :> URUST_GRAMMAR =
struct
  datatype turbofish =
    Turbofish of
      {arguments: URust_AST.generic_args,
       open_offset: int,
       close_offset: int,
       comma_offsets: int list}

  fun scan_turbofish ctxt source =
    let
      val source_symbols =
        Vector.fromList (Input.source_explode source)
      val symbol_count = Vector.length source_symbols
      fun source_symbol index = Vector.sub (source_symbols, index)
      fun symbol index = #1 (source_symbol index)
      fun boundary_position index =
        if index < symbol_count then #2 (source_symbol index)
        else #2 (Input.range_of source)
      fun build_raw_offsets index raw_offset offsets =
        if index = symbol_count then
          Vector.fromList (rev (raw_offset :: offsets))
        else
          build_raw_offsets (index + 1)
            (raw_offset + size (symbol index))
            (raw_offset :: offsets)
      val raw_offsets = build_raw_offsets 0 0 []
      fun raw_offset index = Vector.sub (raw_offsets, index)
      val source_offset =
        Position.offset_of (boundary_position 0)
      val source_has_offsets = is_some source_offset
      fun symbol_slice left right =
        let
          fun collect index fragments =
            if index >= right then String.concat (rev fragments)
            else collect (index + 1) (symbol index :: fragments)
        in collect left [] end
      fun symbol_list left right =
        if left >= right then []
        else source_symbol left :: symbol_list (left + 1) right
      fun mask_physical_unicode symbols =
        map
          (fn (source as (s, position)) =>
            if Symbol.is_utf8 s then ("x", position) else source)
          symbols
      fun token_symbol_list left right =
        (if source_has_offsets then symbol_list left right
         else
           let
             fun collect index =
               if index >= right then []
               else
                 (symbol index,
                  Position.make0 1 (index + 1) 0 "" ""
                    "urust-turbofish-token-index") ::
                   collect (index + 1)
           in collect left end)
        |> mask_physical_unicode
      fun starts_pair index first second =
        index + 1 < symbol_count andalso
          symbol index = first andalso symbol (index + 1) = second
      fun blank s =
        member (op =) [" ", "\t", "\r", "\n"] s
      fun skip_blanks index =
        if index < symbol_count andalso blank (symbol index)
        then skip_blanks (index + 1)
        else index
      fun trim_left left right =
        if left < right andalso blank (symbol left)
        then trim_left (left + 1) right
        else left
      fun trim_right left right =
        if left < right andalso blank (symbol (right - 1))
        then trim_right left (right - 1)
        else right
      fun source_range left right =
        let
          val first = trim_left left right
          val last = trim_right first right
          val _ =
            if first < last then ()
            else
              error ("urust_expr: empty turbofish argument" ^
                Position.here (boundary_position left))
        in
          Input.source true
            (symbol_slice first last)
            (Position.range
              (boundary_position first, boundary_position last))
        end
      fun skip_line_comment index =
        let
          fun loop i =
            if i >= symbol_count orelse symbol i = "\n" then i
            else loop (i + 1)
        in loop (index + 2) end
      fun skip_outer_string index =
        let
          fun loop i =
            if i >= symbol_count then symbol_count
            else if symbol i = "\\" then
              loop (Int.min (i + 2, symbol_count))
            else if symbol i = "\"" then i + 1
            else loop (i + 1)
        in loop (index + 1) end
      val value_open = "\<llangle>"
      val value_close = "\<rrangle>"
      val expression_marker = "\<epsilon>"
      fun skip_value_antiquotation index =
        let
          fun loop depth i =
            if i >= symbol_count then
              error ("urust_expr: unterminated value antiquotation" ^
                Position.here (boundary_position index))
            else if symbol i = value_open then
              loop (depth + 1) (i + 1)
            else if symbol i = value_close then
              if depth = 1 then i + 1
              else loop (depth - 1) (i + 1)
            else loop depth (i + 1)
        in loop 1 (index + 1) end
      fun skip_cartouche index =
        let
          fun loop depth i =
            if i >= symbol_count then NONE
            else if symbol i = Symbol.open_ then
              loop (depth + 1) (i + 1)
            else if symbol i = Symbol.close then
              if depth = 1 then SOME (i + 1)
              else loop (depth - 1) (i + 1)
            else loop depth (i + 1)
        in loop 1 (index + 1) end
      fun legal_after_close index =
        let val i = skip_blanks (index + 1)
        in
          i = symbol_count orelse starts_pair i ":" ":" orelse
          member (op =)
            ["(", ".", "[", "?", "!", ",", ")", "]", "}",
             ";", "+", "-", "*", "/", "%", "&", "|", "^"]
            (symbol i)
        end
      fun closing_delimiter "(" = SOME ")"
        | closing_delimiter "[" = SOME "]"
        | closing_delimiter "{" = SOME "}"
        | closing_delimiter _ = NONE
      fun is_closing_delimiter s =
        member (op =) [")", "]", "}"] s
      fun tokenize left right =
        Syntax.tokenize (Proof_Context.syntax_of ctxt) {raw = false}
          (token_symbol_list left right)
      fun index_tokens slice_start slice_stop tokens =
        let
          fun token_index position =
            (case Position.offset_of position of
               SOME offset =>
                 if source_has_offsets
                 then offset - the source_offset
                 else offset - 1
             | NONE =>
                 error "internal turbofish token lost its source position")
          fun build index [] indexed =
                if index = slice_stop then rev indexed
                else error "internal turbofish token/source coverage mismatch"
            | build index (token :: rest) indexed =
                let
                  val (token_start, token_stop) =
                    apply2 token_index (Lexicon.range_of_token token)
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
      fun token_position token fallback =
        let val position = #1 (Lexicon.range_of_token token)
        in
          if not source_has_offsets
          then boundary_position fallback
          else position
        end
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
      fun scan_token_group content_start required_close tokens =
        let
          val indexed =
            index_tokens content_start
              (case required_close of
                 SOME close => close + 1
               | NONE => symbol_count)
              tokens
          fun mismatch token index =
            error ("urust_expr: mismatched delimiter in turbofish" ^
              Position.here (token_position token index))
          fun finish close_index close_stop argument_start commas close_token =
            let
              val pieces =
                rev ((argument_start, close_index, NONE) :: commas)
              val arguments =
                map (fn (left, right, _) => source_range left right) pieces
              val comma_offsets =
                map_filter
                  (fn (_, _, comma) => Option.map raw_offset comma)
                  pieces
              val token_stop = #2 (Lexicon.range_of_token close_token)
              val span_stop =
                if not source_has_offsets
                then boundary_position close_stop
                else token_stop
            in
              SOME
                {close_index = close_index,
                 close_stop = close_stop,
                 span_stop = span_stop,
                 arguments = arguments,
                 comma_offsets = comma_offsets}
            end
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
                             legal_after_close left andalso
                             (case required_close of
                                SOME close => left = close
                              | NONE => true) andalso
                             not
                               (case next_proper rest of
                                  SOME next => starts_hol_operand next
                                | NONE => false)
                         then
                           finish left right argument_start commas token
                         else
                           loop stack argument_start commas rest)
                  end
        in loop [] content_start [] indexed end
      fun candidate_closes content_start =
        let
          fun collect index closes =
            if index >= symbol_count then rev closes
            else if symbol index = ">" andalso legal_after_close index then
              collect (index + 1) (index :: closes)
            else collect (index + 1) closes
        in collect content_start [] end
      fun scan_group group_start =
        let
          val content_start = group_start + 1
          fun unterminated () =
            error ("urust_expr: unterminated turbofish" ^
              Position.here (boundary_position group_start))
          fun fallback failed [] = failed ()
            | fallback failed (close :: rest) =
                (case Exn.capture
                    (fn () => tokenize content_start (close + 1)) () of
                   Exn.Res tokens =>
                     (case scan_token_group content_start (SOME close) tokens of
                        SOME result => result
                      | NONE => fallback failed rest)
                 | Exn.Exn exn =>
                     if Exn.is_interrupt exn then Exn.reraise exn
                     else fallback failed rest)
          val closes = candidate_closes content_start
        in
          (case Exn.capture
              (fn () => tokenize content_start symbol_count) () of
             Exn.Res tokens =>
               (case scan_token_group content_start NONE tokens of
                  SOME result => result
                | NONE => fallback unterminated closes)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else fallback (fn () => Exn.reraise exn) closes)
        end
      fun scan index table =
        if index >= symbol_count then table
        else if symbol index = "\"" then
          scan (skip_outer_string index) table
        else if starts_pair index "/" "/" then
          scan (skip_line_comment index) table
        else if symbol index = value_open then
          scan (skip_value_antiquotation index) table
        else if symbol index = expression_marker andalso
            index + 1 < symbol_count andalso
            symbol (index + 1) = Symbol.open_ then
          (case skip_cartouche (index + 1) of
             SOME stop => scan stop table
           | NONE => table)
        else if symbol index = Symbol.open_ then
          (case skip_cartouche index of
             SOME stop => scan stop table
           | NONE => table)
        else if starts_pair index ":" ":" then
          let
            val open_index = skip_blanks (index + 2)
          in
            if open_index < symbol_count andalso
                symbol open_index = "<" then
              let
                val
                  {close_index, close_stop, span_stop,
                   arguments, comma_offsets} =
                    scan_group open_index
                val span =
                  Position.range_position
                    (boundary_position index, span_stop)
                val entry =
                  Turbofish
                    {arguments = URust_AST.Generic_Args (arguments, span),
                     open_offset = raw_offset open_index,
                     close_offset = raw_offset close_index,
                     comma_offsets = comma_offsets}
              in
                scan close_stop
                  (Inttab.update (raw_offset index, entry) table)
              end
            else scan (index + 2) table
          end
        else scan (index + 1) table
    in scan 0 Inttab.empty end

  fun lex_error text pos =
    error ("urust_expr: unexpected input " ^ quote text ^ Position.here pos)

  fun string_error pos =
    error ("urust_expr: malformed or unterminated string literal" ^ Position.here pos)

  fun antiquotation_error kind pos =
    error ("urust_expr: unterminated " ^ kind ^ " antiquotation" ^ Position.here pos)
end
\<close>
SML_import \<open> structure URust_Grammar = URust_Grammar \<close>
SML_import \<open> structure Parser_Lex_Util = Parser_Lex_Util \<close>  \<comment>\<open> shared lexer position math \<close>

section\<open> Lexer + grammar \<close>

text\<open>
Lexer start states capture value and expression antiquotation bodies without lexing their
HOL content. Yacc directives reproduce the frontend precedence
(\<open>Micro_Rust_Syntax.thy:559-639\<close>). Only token shims remain lexer-local; positions use
\<open>Parser_Lex_Util\<close>.
\<close>
(*
  This declaration generates the private URust lexer/parser functors used by Parser_Impl_Diagnostics.
  Together they own recognition of one uRust expression source and construction of the unresolved
  URust_AST. Their boundary includes tokenization, PIDE token
  reports, precedence and sequencing policy, and grammar-action construction of AST nodes.  It ends
  before identifier or constructor resolution, site-specific pattern validation, lowering to shallow
  terms, and HOL type checking.

  Parser_Impl_Diagnostics relies on the standard expert-mode Lex/Yacc functor interface:

    * URustLexFun produces the lexer structure accepted by the ML-Yacc Join functor. Its
      UserDeclarations.set source ctxt operation initializes the Isabelle-Lex-Yacc runtime, builds the
      per-source position map, and resets all antiquotation state.
    * URustLrValsFun supplies the generated semantic value/result types, actions, LR table, tokens, and
      recovery data. Parser_Impl_Diagnostics instantiates it once and rejoins that exact data with the
      generated lexer while replacing only terminal rendering.
    * The generated Tokens.EOF constructs the dummy end token required by
      Parser_Lex_Util.parse_source.  Its Position.T * Position.T argument delimits the token.  Other
      generated token constructors are lexer implementation details; terminal additions or reordering
      must still be reflected in Parser_Impl_Diagnostics' exhaustive terminal identity table.
    * The start result is URust_AST.ur_expr option.  NONE represents empty input; SOME ast preserves
      source order and the token/span positions recorded by URust_AST.  Syntax rejection raises a
      positioned ERROR rather than returning NONE.

  Expert mode deliberately generates no unsealed URust structure or default parse_source operation.
  Parser clients use the sealed URust_Diagnostics.parse_source boundary. Lexer refs, start states,
  buffers, position-map helpers, grammar nonterminals, LR states/tables, semantic-value encodings, and
  generated functor names remain implementation details shared only with Parser_Impl_Diagnostics.
  Refactors may change them provided the AST result, source positions/markup, state-initialization rule,
  and diagnostic rejoin points above are preserved.
*)
ml_lex_yacc [verbose, expert] "URust" where
lex_user_declarations\<open>
structure Tokens = Tokens
type pos = Position.T
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

datatype aq_kind = No_AQ | Value_AQ | Expr_AQ
val aq_kind = ref No_AQ
val aq_buf = ref ([] : string list)
val aq_start = ref 0   (* char offset of the antiquotation BODY start (just after the opener) *)
val aq_open = ref 0
val aq_depth = ref 0
val turbofish_table = ref (Inttab.empty : URust_Grammar.turbofish Inttab.table)
val turbofish_close = ref ~1

fun reset_aq () =
  (aq_kind := No_AQ; aq_buf := []; aq_start := 0; aq_open := 0; aq_depth := 0;
   turbofish_close := ~1)
fun start_aq kind open_pos body_pos =
  (aq_kind := kind; aq_buf := []; aq_start := body_pos; aq_open := open_pos; aq_depth := 0)
fun push_aq fragment = aq_buf := fragment :: !aq_buf
fun take_aq () =
  let val body = String.concat (rev (!aq_buf))
  in reset_aq (); body end

(* A suffixed integer literal is deliberately NOT interpreted here: the lexer captures the raw lexeme and
   the elaboration term layer reads it against the single suffix table, so an unknown suffix is a
   POSITIONED elaborator error rather than an unpositioned `raise Fail` in lexer code (D29). The bare-hex
   rule precedes the general digit-plus-identifier rule so equal-length `0xff` is NUM, while longer
   `0xffu8` and unsupported glued suffixes are each one NUMSFX token.

   Per-lexer position-map ref + set-shadow; the position MATH is shared (Parser_Lex_Util). tok_ident emits NO
   colour -- ident_term does that once it knows the name's role, so the markup cannot split (D14). *)
val pos_map =
  ref
    (Parser_Lex_Util.make_position_map
      (Parser_Lex_Util.text_source ""))
fun set source ctxt =
  (Isabelle_lex_yacc.set source ctxt;
   pos_map := Parser_Lex_Util.make_position_map source;
   turbofish_table := URust_Grammar.scan_turbofish ctxt source;
   reset_aq ())

fun fixed_pos yypos = Parser_Lex_Util.fixed_pos (!pos_map) yypos
fun tokF args       = Parser_Lex_Util.tokF (!pos_map) args
fun tok_valF args   = Parser_Lex_Util.tok_valF (!pos_map) args
fun report_text args = Parser_Lex_Util.report_text (!pos_map) args
fun tok_ident (yypos, yytext) =
  let val p = Parser_Lex_Util.ident_pos (!pos_map) (yypos, yytext)
  in Tokens.IDENT (yytext, p, p) end

fun tok_turbofish (yypos, yytext) =
  (case Inttab.lookup (!turbofish_table) yypos of
     SOME (URust_Grammar.Turbofish
       {arguments, open_offset, close_offset, comma_offsets}) =>
       let
         val start = fixed_pos yypos
         val stop = fixed_pos (close_offset + 1)
         val _ = report_text (yypos, "::", Markup.delimiter, "TCOLONCOLON")
         val _ = report_text (open_offset, "<", Markup.delimiter, "TURBO")
         val _ =
           List.app
             (fn offset =>
               report_text (offset, ",", Markup.delimiter, "TURBO"))
             comma_offsets
         val _ = report_text (close_offset, ">", Markup.delimiter, "TURBO")
         val _ = turbofish_close := close_offset
       in Tokens.TURBO (arguments, start, stop) end
   | NONE => URust_Grammar.lex_error yytext (fixed_pos yypos))

fun tok_matches_bang (yypos, yytext) =
  let
    val range as (start, stop) =
      Parser_Lex_Util.text_range (!pos_map) (yypos, yytext)
    val bang_raw = yypos + size yytext - 1
    val bang_pos = fixed_pos bang_raw
    val _ = report_text (yypos, "matches", Markup.keyword1, "TMATCHESBANG")
    val _ = report_text (bang_raw, "!", Markup.operator, "TMATCHESBANG")
  in Tokens.TMATCHESBANG (bang_pos, start, stop) end

fun eof () =
  (case !aq_kind of
     No_AQ => Tokens.EOF (Position.none, Position.none)
   | Value_AQ => URust_Grammar.antiquotation_error "value" (fixed_pos (!aq_open))
   | Expr_AQ => URust_Grammar.antiquotation_error "expression" (fixed_pos (!aq_open)))
\<close>
lex_definitions\<open>
%header (functor URustLexFun(structure Tokens: URust_TOKENS));
%s VAQ EAQ TURBO;
digit=[0-9];
hexdigit=[0-9a-fA-F];
idstart=[A-Za-z_];
idchar=[A-Za-z0-9_];
ws = [\ \t\r];
pathws = [\ \t\r\n];
\<close>
lex_rules\<open>
<INITIAL>\n       => (lex());
<INITIAL>{ws}+    => (lex());
<INITIAL>"//"[^\n]* =>
    (report_text (yypos, yytext, Markup.comment1, "line comment"); lex());
<INITIAL>"0x"{hexdigit}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>{digit}+{idstart}{idchar}* =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUMSFX", Tokens.NUMSFX, yytext));
<INITIAL>{digit}+ =>
    (tok_valF (yypos, yytext, Markup.numeral, "NUM", Tokens.NUM, yytext));
<INITIAL>"true"   => (tokF (yypos, yytext, Markup.keyword1, "TTRUE", Tokens.TTRUE));
<INITIAL>"false"  => (tokF (yypos, yytext, Markup.keyword1, "TFALSE", Tokens.TFALSE));
<INITIAL>"let"    => (tokF (yypos, yytext, Markup.keyword1, "TLET", Tokens.TLET));
<INITIAL>"const"  => (tokF (yypos, yytext, Markup.keyword1, "TCONST", Tokens.TCONST));
<INITIAL>"return" => (tokF (yypos, yytext, Markup.keyword1, "TRETURN", Tokens.TRETURN));
<INITIAL>"if"     => (tokF (yypos, yytext, Markup.keyword1, "TIF", Tokens.TIF));
<INITIAL>"else"   => (tokF (yypos, yytext, Markup.keyword1, "TELSE", Tokens.TELSE));
<INITIAL>"fuel"   => (tokF (yypos, yytext, Markup.keyword1, "TFUEL", Tokens.TFUEL));
<INITIAL>"while"  => (tokF (yypos, yytext, Markup.keyword1, "TWHILE", Tokens.TWHILE));
<INITIAL>"loop"   => (tokF (yypos, yytext, Markup.keyword1, "TLOOP", Tokens.TLOOP));
<INITIAL>"for"    => (tokF (yypos, yytext, Markup.keyword1, "TFOR", Tokens.TFOR));
<INITIAL>"in"     => (tokF (yypos, yytext, Markup.keyword1, "TIN", Tokens.TIN));
<INITIAL>"unsafe" => (tokF (yypos, yytext, Markup.keyword1, "TUNSAFE", Tokens.TUNSAFE));
<INITIAL>"matches""!" => (tok_matches_bang (yypos, yytext));
<INITIAL>"match"        => (tokF (yypos, yytext, Markup.keyword1, "TMATCH", Tokens.TMATCH));
<INITIAL>"match_switch" => (tokF (yypos, yytext, Markup.keyword1, "TMATCHSWITCH", Tokens.TMATCHSWITCH));
<INITIAL>"match_case"   => (tokF (yypos, yytext, Markup.keyword1, "TMATCHCASE", Tokens.TMATCHCASE));
<INITIAL>"mut"    => (tokF (yypos, yytext, Markup.keyword1, "TMUT", Tokens.TMUT));
<INITIAL>"::"{pathws}*"<" =>
    (YYBEGIN TURBO; tok_turbofish (yypos, yytext));
<INITIAL>"::"     => (tokF (yypos, yytext, Markup.delimiter, "TCOLONCOLON", Tokens.TCOLONCOLON));
<INITIAL>"<<="    => (tokF (yypos, yytext, Markup.operator, "TSHLEQ", Tokens.TSHLEQ));
<INITIAL>">>="    => (tokF (yypos, yytext, Markup.operator, "TSHREQ", Tokens.TSHREQ));
<INITIAL>"+="     => (tokF (yypos, yytext, Markup.operator, "TPLUSEQ", Tokens.TPLUSEQ));
<INITIAL>"-="     => (tokF (yypos, yytext, Markup.operator, "TMINUSEQ", Tokens.TMINUSEQ));
<INITIAL>"*="     => (tokF (yypos, yytext, Markup.operator, "TSTAREQ", Tokens.TSTAREQ));
<INITIAL>"%="     => (tokF (yypos, yytext, Markup.operator, "TPERCENTEQ", Tokens.TPERCENTEQ));
<INITIAL>"&="     => (tokF (yypos, yytext, Markup.operator, "TAMPEQ", Tokens.TAMPEQ));
<INITIAL>"|="     => (tokF (yypos, yytext, Markup.operator, "TBAREQ", Tokens.TBAREQ));
<INITIAL>"^="     => (tokF (yypos, yytext, Markup.operator, "TCARETEQ", Tokens.TCARETEQ));
<INITIAL>"=>"     => (tokF (yypos, yytext, Markup.delimiter, "TARROW", Tokens.TARROW));
<INITIAL>"="      => (tokF (yypos, yytext, Markup.delimiter, "TEQ", Tokens.TEQ));
<INITIAL>";"      => (tokF (yypos, yytext, Markup.delimiter, "TSEMI", Tokens.TSEMI));
<INITIAL>"..="    => (tokF (yypos, yytext, Markup.operator, "TDOTDOTEQ", Tokens.TDOTDOTEQ));
<INITIAL>".."     => (tokF (yypos, yytext, Markup.operator, "TDOTDOT", Tokens.TDOTDOT));
<INITIAL>"<<"     => (tokF (yypos, yytext, Markup.operator, "TSHL", Tokens.TSHL));
<INITIAL>">>"     => (tokF (yypos, yytext, Markup.operator, "TSHR", Tokens.TSHR));
<INITIAL>"<="     => (tokF (yypos, yytext, Markup.operator, "TLE", Tokens.TLE));
<INITIAL>">="     => (tokF (yypos, yytext, Markup.operator, "TGE", Tokens.TGE));
<INITIAL>"=="     => (tokF (yypos, yytext, Markup.operator, "TEQEQ", Tokens.TEQEQ));
<INITIAL>"!="     => (tokF (yypos, yytext, Markup.operator, "TNE", Tokens.TNE));
<INITIAL>"&&"     => (tokF (yypos, yytext, Markup.operator, "TAMPAMP", Tokens.TAMPAMP));
<INITIAL>"||"     => (tokF (yypos, yytext, Markup.operator, "TBARBAR", Tokens.TBARBAR));
<INITIAL>"+"      => (tokF (yypos, yytext, Markup.operator, "TPLUS", Tokens.TPLUS));
<INITIAL>"-"      => (tokF (yypos, yytext, Markup.operator, "TMINUS", Tokens.TMINUS));
<INITIAL>"*"      => (tokF (yypos, yytext, Markup.operator, "TSTAR", Tokens.TSTAR));
<INITIAL>"/"      => (tokF (yypos, yytext, Markup.operator, "TSLASH", Tokens.TSLASH));
<INITIAL>"%"      => (tokF (yypos, yytext, Markup.operator, "TPERCENT", Tokens.TPERCENT));
<INITIAL>"<"      => (tokF (yypos, yytext, Markup.operator, "TLT", Tokens.TLT));
<INITIAL>">"      => (tokF (yypos, yytext, Markup.operator, "TGT", Tokens.TGT));
<INITIAL>"&"      => (tokF (yypos, yytext, Markup.operator, "TAMP", Tokens.TAMP));
<INITIAL>"|"      => (tokF (yypos, yytext, Markup.operator, "TBAR", Tokens.TBAR));
<INITIAL>"^"      => (tokF (yypos, yytext, Markup.operator, "TCARET", Tokens.TCARET));
<INITIAL>"!"      => (tokF (yypos, yytext, Markup.operator, "TBANG", Tokens.TBANG));
<INITIAL>"?"      => (tokF (yypos, yytext, Markup.operator, "TQUESTION", Tokens.TQUESTION));
<INITIAL>"\""([^\"\\\n]|\\.)*"\"" =>
    (tok_valF (yypos, yytext, Markup.inner_string, "STRING", Tokens.STRING, yytext));
<INITIAL>"\""     => (URust_Grammar.string_error (fixed_pos yypos));
<INITIAL>{idstart}{idchar}* => (tok_ident (yypos, yytext));
<INITIAL>"("      => (tokF (yypos, yytext, Markup.delimiter, "LPAR", Tokens.LPAR));
<INITIAL>")"      => (tokF (yypos, yytext, Markup.delimiter, "RPAR", Tokens.RPAR));
<INITIAL>","      => (tokF (yypos, yytext, Markup.delimiter, "COMMA", Tokens.COMMA));
<INITIAL>"."      => (tokF (yypos, yytext, Markup.delimiter, "TDOT", Tokens.TDOT));
<INITIAL>":"      => (tokF (yypos, yytext, Markup.delimiter, "TCOLON", Tokens.TCOLON));
<INITIAL>"@"      => (tokF (yypos, yytext, Markup.operator, "TAT", Tokens.TAT));
<INITIAL>"#"      => (tokF (yypos, yytext, Markup.delimiter, "THASH", Tokens.THASH));
<INITIAL>"["      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACK", Tokens.TLBRACK));
<INITIAL>"]"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACK", Tokens.TRBRACK));
<INITIAL>"{"      => (tokF (yypos, yytext, Markup.delimiter, "TLBRACE", Tokens.TLBRACE));
<INITIAL>"}"      => (tokF (yypos, yytext, Markup.delimiter, "TRBRACE", Tokens.TRBRACE));
<INITIAL>\\"<llangle>"          => (report_text (yypos, yytext, Markup.delimiter, "VALAQ"); start_aq Value_AQ yypos (yypos + size yytext); YYBEGIN VAQ; lex());
<INITIAL>\\"<epsilon>"\\"<open>" => (report_text (yypos, hd (Symbol.explode yytext), Markup.literal, "EXPRAQ"); start_aq Expr_AQ yypos (yypos + size yytext); YYBEGIN EAQ; lex());
<INITIAL>\\"<Rightarrow>" => (tokF (yypos, yytext, Markup.delimiter, "TARROW", Tokens.TARROW));
<INITIAL>.        => (URust_Grammar.lex_error yytext (fixed_pos yypos));
<VAQ>\\"<llangle>" => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<VAQ>\\"<rrangle>" =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_text (yypos, yytext, Markup.delimiter, "VALAQ");
       let val p = fixed_pos (!aq_start) val q = fixed_pos yypos val body = take_aq ()
       in Tokens.VALAQ (Input.source true body (Position.range (p, q)), p, q) end));
<VAQ>\n           => (push_aq "\n"; lex());
<VAQ>.            => (push_aq yytext; lex());
<EAQ>\\"<open>"    => (aq_depth := !aq_depth + 1; push_aq yytext; lex());
<EAQ>\\"<close>"   =>
    (if !aq_depth > 0 then (aq_depth := !aq_depth - 1; push_aq yytext; lex())
     else (YYBEGIN INITIAL; report_text (yypos, yytext, Markup.delimiter, "EXPRAQ");
       let val p = fixed_pos (!aq_start) val q = fixed_pos yypos val body = take_aq ()
       in Tokens.EXPRAQ (Input.source true body (Position.range (p, q)), p, q) end));
<EAQ>\n           => (push_aq "\n"; lex());
<EAQ>.            => (push_aq yytext; lex());
<TURBO>\n         => (lex());
<TURBO>.          =>
    (if yypos = !turbofish_close
     then (turbofish_close := ~1; YYBEGIN INITIAL; lex())
     else lex());
\<close>
and yacc_user_declarations\<open>
open URust_AST

datatype binding_head =
    BH_Let of ur_pat * ur_expr
  | BH_LetMut of ur_pat * ur_expr * Position.T
  | BH_Const of ur_pat * ur_expr
  | BH_LetElse of ur_pat * ur_expr * ur_expr * Position.T

fun finish_binding (BH_Let (pattern, value), body, _) =
      UE_Let (pattern, value, body)
  | finish_binding (BH_LetMut (pattern, value, pos), body, _) =
      UE_LetMut (pattern, value, body, pos)
  | finish_binding (BH_Const (pattern, value), body, _) =
      UE_Const (pattern, value, body)
  | finish_binding
      (BH_LetElse (pattern, value, fallback, pos), body, body_right) =
      mk_let_else
        (pattern, value, fallback, body, pos, body_right)

datatype if_head =
    IH_If of ur_expr * Position.T
  | IH_IfLet of ur_pat * ur_expr * Position.T

fun finish_conditional
      (IH_If (condition, pos), success, fallback, _) =
      UE_If (condition, success, fallback, pos)
  | finish_conditional
      (IH_IfLet (pattern, value, pos), success, fallback, stop) =
      UE_IfLet
        (pattern, value, success, fallback,
         Position.range_position (pos, stop))

fun segment_position (Path_Segment (_, pos, NONE)) = pos
  | segment_position (Path_Segment (_, _, SOME (Generic_Args (_, pos)))) = pos

fun exclusive_end pos =
  (case Position.end_offset_of pos of
     SOME stop =>
       let
         val {line, props = {label, file, id}, ...} = Position.dest pos
       in Position.make0 line stop 0 label file id end
   | NONE => pos)

fun make_path segment =
  UR_Path ([segment], segment_position segment)

fun append_path (UR_Path (segments, pos), segment) =
  UR_Path
    (segments @ [segment],
     Position.range_position
       (pos, exclusive_end (segment_position segment)))
\<close>
yacc_definitions\<open>
%name URust
%pos Position.T
%eop EOF
%noshift EOF

(* Operator precedence, loosest -> tightest (the frontend's infix priorities). Return is below
   with-block expressions, so `return { e }` takes the block as its operand instead of becoming an
   operandless return followed by a block statement. Comparisons are non-associative (Rust rejects
   `a == b == c`). Ranges and assignment use structural tiers below. Reference prefixes and `!` use
   structural tiers too; these directives keep the ambiguous `uexp OP uexp` productions
   conflict-free. *)
%right TRETURN
%right TIF TELSE TLBRACE TLBRACK TUNSAFE TWHILE TLOOP TFOR
%nonassoc TDOTDOT TDOTDOTEQ
%left TBARBAR
%left TAMPAMP
%nonassoc TEQEQ TNE TLT TLE TGT TGE
%nonassoc TPATCONTEXT
%left TBAR
%left TCARET
%left TAMP
%left TSHL TSHR
%left TPLUS TMINUS
%left TSTAR TSLASH TPERCENT
%right TBANG

%term NUM of string | NUMSFX of string | STRING of string | IDENT of string | LPAR | RPAR
    | VALAQ of Input.source | EXPRAQ of Input.source
    | TURBO of URust_AST.generic_args
    | TTRUE | TFALSE | TLET | TCONST | TRETURN | TEQ | TSEMI | EOF
    | TIF | TELSE | TLBRACE | TRBRACE | TLBRACK | TRBRACK | COMMA | TDOT
    | TCOLON | TCOLONCOLON | TAT
    | TPLUS | TMINUS | TSTAR | TSLASH | TPERCENT
    | TSHL | TSHR | TAMP | TBAR | TCARET
    | TPLUSEQ | TMINUSEQ | TSTAREQ | TPERCENTEQ
    | TAMPEQ | TBAREQ | TCARETEQ | TSHLEQ | TSHREQ
    | TEQEQ | TNE | TLT | TLE | TGT | TGE
    | TAMPAMP | TBARBAR | TBANG | TQUESTION
    | TUNSAFE | TFUEL | TWHILE | TLOOP | TFOR | TIN | THASH
    | TMATCH | TMATCHSWITCH | TMATCHCASE | TARROW
    | TDOTDOT | TDOTDOTEQ | TMUT | TPATCONTEXT
    | TMATCHESBANG of Position.T
%nonterm ustart of URust_AST.ur_expr option
       | ubody of URust_AST.ur_expr
       | ubinding_head of binding_head
       | uval of URust_AST.ur_expr
       | uclosure_arg of URust_AST.ur_expr
       | uclosure of URust_AST.ur_expr
       | uclosure_formals of URust_AST.ur_pat list
       | uclosure_body of URust_AST.ur_expr
       | uclosure_if_head of if_head
       | uclosure_conditional of URust_AST.ur_expr
       | uassign of URust_AST.ur_expr
       | uassignop of URust_AST.assignop * Position.T
       | urange of URust_AST.ur_expr
       | uexp of URust_AST.ur_expr
       | urefprefix of URust_AST.ur_expr
       | unotprefix of URust_AST.ur_expr
       | upostfix of URust_AST.ur_expr
       | uatom of URust_AST.ur_expr
       | upath_segment of URust_AST.path_segment
       | upath of URust_AST.ur_path
       | arglist of URust_AST.ur_expr list
       | ucallargs of URust_AST.ur_expr list
       | umacroargs of URust_AST.ur_expr list
       | umacrocallargs of URust_AST.ur_expr list
       | ublock of URust_AST.ur_expr
       | uunsafe of URust_AST.ur_expr
       | uwith_block_atom of URust_AST.ur_expr
       | ucontrol_expr of URust_AST.ur_expr
       | usemi_free_stmt of URust_AST.ur_expr
       | uconditional of URust_AST.ur_expr
       | uif_head of if_head
       | ufuel of Input.source * Position.T
       | uloop_expr of URust_AST.ur_expr
       | umatch_kind of URust_AST.match_flavour * Position.T
       | umatch of URust_AST.ur_expr
       | uguard of URust_AST.ur_expr
       | uarm of URust_AST.ur_arm
       | uarms of URust_AST.ur_arm list
       | upat of URust_AST.ur_pat
       | upat_range of URust_AST.ur_pat
       | upat_alias of URust_AST.ur_pat
       | upat_prefix of URust_AST.ur_pat
       | upat_atom of URust_AST.ur_pat
       | upat_ident of string * Position.T
       | upats of URust_AST.ur_pat list
       | uslice_item of URust_AST.slice_item
       | uslice_items of URust_AST.slice_item list
       | ustruct_field of URust_AST.struct_field
       | ustruct_fields of URust_AST.struct_field list
\<close>
yacc_rules\<open>
  ustart : ubody (SOME ubody)
         | (NONE)
  (* A body is a value, semicolon sequencing, a policy-approved semicolon-free statement followed by
     another body, or a binding head followed by its required semicolon and continuation. The same
     nonterminal is used for block contents and match guards, matching the old frontend's unrestricted
     `urust` guard slot without duplicating statement syntax. *)
  ubody : uval                              (uval)
        | uclosure                          (uclosure)
        | uval TSEMI ubody                  (UE_Seq (uval, ubody))
        | uval TSEMI                        (finish_statement (uval, TSEMIleft))
        | usemi_free_stmt                   (usemi_free_stmt)
        | ubinding_head TSEMI ubody
            (finish_binding (ubinding_head, ubody, ubodyright))
  (* Binding heads are grammar-private. The binder is the shared `upat`, so every site continues to use
     the existing pattern validation and lowering policies. *)
  ubinding_head : TLET upat TEQ uval
                    (BH_Let (upat, uval))
                | TLET TMUT upat TEQ uval
                    (BH_LetMut (upat, uval, TMUTleft))
                | TCONST upat TEQ uval
                    (BH_Const (upat, uval))
                | TLET upat TEQ uval TELSE ublock
                    (BH_LetElse (upat, uval, ublock, TLETleft))
  (* Value position: an operand OR a with-block control-flow expr. `uval` is where `if`/`match` (later
     loops) are admitted -- let-RHS, condition, call args, parens -- WITHOUT being a bare binary-operator
     operand (that stays `uexp`, closing divergence D-1 -- D25). *)
  uval : uassign (uassign)
       | TRETURN (UE_Return (NONE, TRETURNleft))
       | TRETURN uclosure_arg
           (UE_Return (SOME uclosure_arg, TRETURNleft))
       | ucontrol_expr %prec TIF (ucontrol_expr)
  (* Bare closures deliberately remain outside uval, uassign, and uexp. This delimiter-level category
     is used only by the grammar sites where a closure may appear without grouping. Parentheses turn
     the resulting closure node back into an ordinary atom. *)
  uclosure_arg : uval                       (uval)
               | uclosure                   (uclosure)
  uclosure : TBARBAR uclosure_body
                (mk_closure
                  ([], uclosure_body,
                   TBARBARleft, uclosure_bodyright))
           | TBAR uclosure_formals TBAR uclosure_body
                (mk_closure
                  (uclosure_formals, uclosure_body,
                   TBAR1left, uclosure_bodyright))
  (* Closure formals share the pattern representation, but this grammar accepts identifier spellings
     only. mk_bare_ident_pat normalizes `_` to P_Wild so the closure-formal elaboration gate can issue
     the positioned semantic rejection. Repeated identifiers and arbitrarily long lists are retained. *)
  uclosure_formals : IDENT
                       ([mk_bare_path_pat
                           (make_single_path (IDENT, IDENTleft))])
                   | IDENT COMMA uclosure_formals
                       (mk_bare_path_pat
                          (make_single_path (IDENT, IDENTleft)) ::
                          uclosure_formals)
  (* This is the old frontend's priority-20 closure-body boundary: assignments and pure expressions,
     ordinary conditionals, matches, blocks/unsafe blocks through uassign, and legacy semicolon-bearing
     returns. Bindings, if-let, loops, sequencing, direct nested closures, and semicolon-free returns
     enter only through an explicit block or another admitted delimiter context. *)
  uclosure_body : uassign                   (uassign)
                | uclosure_conditional      (uclosure_conditional)
                | umatch                    (umatch)
                | TRETURN TSEMI
                    (UE_Return (NONE, TRETURNleft))
                | TRETURN uclosure_arg TSEMI
                    (UE_Return (SOME uclosure_arg, TRETURNleft))
  (* This head deliberately does not reuse uif_head: closure-body priority admits only ordinary if,
     and the recursive closure conditional must exclude if-let from every later else-if arm too. *)
  uclosure_if_head : TIF uval
                       (IH_If (uval, TIFleft))
  uclosure_conditional : uclosure_if_head ublock %prec TIF
                           (finish_conditional
                             (uclosure_if_head, ublock, NONE, ublockright))
                       | uclosure_if_head ublock TELSE ublock
                           (finish_conditional
                             (uclosure_if_head, ublock1, SOME ublock2,
                              ublock2right))
                       | uclosure_if_head ublock TELSE uclosure_conditional
                           (finish_conditional
                             (uclosure_if_head, ublock,
                              SOME uclosure_conditional,
                              uclosure_conditionalright))
  (* Assignment is below ranges and every pure operator and recurses through its own tier on the right.
     Blocks remain ordinary expression atoms, while lower-priority `if`/`match` forms require
     parentheses on the RHS, matching the frontend's priority-40 boundary. The LHS crosses
     expr_to_place exactly once. *)
  uassign : urange (urange)
          | urange uassignop uassign (mk_assign uassignop urange uassign)
  uassignop : TEQ        ((Assign, TEQleft))
            | TPLUSEQ    ((AssignAdd, TPLUSEQleft))
            | TMINUSEQ   ((AssignBin AssignSub, TMINUSEQleft))
            | TSTAREQ    ((AssignBin AssignMul, TSTAREQleft))
            | TPERCENTEQ ((AssignBin AssignMod, TPERCENTEQleft))
            | TAMPEQ     ((AssignBin AssignBAnd, TAMPEQleft))
            | TBAREQ     ((AssignBin AssignBOr, TBAREQleft))
            | TCARETEQ   ((AssignBin AssignBXor, TCARETEQleft))
            | TSHLEQ     ((AssignBin AssignShl, TSHLEQleft))
            | TSHREQ     ((AssignBin AssignShr, TSHREQleft))
  (* Bounded ranges form one non-associative tier between logical OR and assignment. Their endpoints
     are complete pure expressions, so every tighter binary operator remains inside the endpoint. *)
  urange : uexp (uexp)
         | uexp TDOTDOT uexp
             (UE_Range (RK_Exclusive, uexp1, uexp2, TDOTDOTleft))
         | uexp TDOTDOTEQ uexp
             (UE_Range (RK_Inclusive, uexp1, uexp2, TDOTDOTEQleft))
  (* Postfixes form a structural tier above atoms, so `?`, field access, and methods compose
     left-to-right and bind tighter than prefix/binary operators. Indexing shares this tier. A dotted
     identifier followed by parentheses is a method; without parentheses it is an NField lens access. *)
  upostfix : uatom (uatom)
           | upostfix TQUESTION
               (UE_Unary (U_Propagate, upostfix, TQUESTIONleft))
           | upostfix TDOT IDENT
               (UE_Field (upostfix, IDENT, IDENTleft))
           | upostfix TDOT upath_segment LPAR ucallargs RPAR
               (mk_method_call
                  (upostfix, upath_segment, ucallargs, upostfixleft, RPARright))
           | upostfix TLBRACK uclosure_arg TRBRACK
               (UE_Index
                 (upostfix, uclosure_arg,
                  Position.range_position (upostfixleft, TRBRACKright)))
  uatom : NUM        (UE_Literal (LP_Integer (NUM, NUMleft)))
        | NUMSFX     (UE_Literal (LP_Integer (NUMSFX, NUMSFXleft)))
        | TTRUE      (UE_Literal (LP_Bool (true, TTRUEleft)))
        | TFALSE     (UE_Literal (LP_Bool (false, TFALSEleft)))
        | STRING     (UE_Literal (LP_String (STRING, STRINGleft)))
        | upath      (UE_Path upath)
        | upath LPAR ucallargs RPAR
            (mk_call (upath, ucallargs, upathleft, RPARright))
        | upath TBANG LPAR umacrocallargs RPAR
            (UE_Macro
              (upath, TBANGleft,
               MP_Arguments umacrocallargs,
               Position.range_position (upathleft, RPARright)))
        | upath TBANG TLBRACK umacrocallargs TRBRACK
            (UE_Macro
              (upath, TBANGleft,
               MP_Arguments umacrocallargs,
               Position.range_position (upathleft, TRBRACKright)))
        | TMATCHESBANG LPAR uclosure_arg COMMA upat RPAR
            (UE_Macro
              (make_single_path
                 ("matches",
                  Position.range_position (TMATCHESBANGleft, TMATCHESBANG)),
               TMATCHESBANG,
               MP_Matches (uclosure_arg, upat),
               Position.range_position (TMATCHESBANGleft, RPARright)))
        | LPAR RPAR  (UE_Unit LPARleft)
        | LPAR uclosure_arg COMMA arglist RPAR
            (UE_Tuple
              (uclosure_arg :: arglist,
               Position.range_position (LPARleft, RPARright)))
        | LPAR uclosure_arg RPAR
            (UE_Group
              (uclosure_arg,
               Position.range_position (LPARleft, RPARright)))
        | TLBRACK TRBRACK
            (UE_Array ([], Position.range_position (TLBRACKleft, TRBRACKright)))
        | TLBRACK arglist TRBRACK
            (UE_Array (arglist, Position.range_position (TLBRACKleft, TRBRACKright)))
        | VALAQ      (UE_Literal (LP_ValAntiq VALAQ))
        | EXPRAQ     (UE_ExprAntiq EXPRAQ)
        | uwith_block_atom %prec TIF (uwith_block_atom)
  upath_segment : IDENT
                    (Path_Segment (IDENT, IDENTleft, NONE))
                | IDENT TURBO
                    (Path_Segment (IDENT, IDENTleft, SOME TURBO))
  upath : upath_segment
            (make_path upath_segment)
        | upath TCOLONCOLON upath_segment
            (append_path (upath, upath_segment))
  (* Reference prefixes bind tighter than every binary operator and looser than `!`, matching the
     frontend priorities. Recursing through this tier makes `**x` two ordinary dereference nodes while
     preserving the binary meanings of `*` and `&`; mixed and deeper recursion is a documented
     accepted-surface improvement over the frontend's fixed prefix productions. *)
  unotprefix : upostfix (upostfix)
             | TBANG unotprefix (UE_Unary (U_Not, unotprefix, TBANGleft))
  urefprefix : unotprefix (unotprefix)
             | TAMP urefprefix
                 (UE_Unary (U_Borrow BM_Imm, urefprefix, TAMPleft))
             | TAMP TMUT urefprefix
                 (UE_Unary (U_Borrow BM_Mut, urefprefix, TAMPleft))
             | TSTAR urefprefix
                 (UE_Unary (U_Deref, urefprefix, TSTARleft))
  uexp : urefprefix (urefprefix)
       (* `ucontrol_expr` is deliberately NOT a `uexp` alternative (closes D-1): it reaches value
          position via `uval` and operand position only when parenthesized. *)
       | uexp TPLUS uexp     (UE_Bin (Add,  uexp1, uexp2, TPLUSleft))
       | uexp TMINUS uexp    (UE_Bin (Sub,  uexp1, uexp2, TMINUSleft))
       | uexp TSTAR uexp     (UE_Bin (Mul,  uexp1, uexp2, TSTARleft))
       | uexp TSLASH uexp    (UE_Bin (Div,  uexp1, uexp2, TSLASHleft))
       | uexp TPERCENT uexp  (UE_Bin (Mod,  uexp1, uexp2, TPERCENTleft))
       | uexp TSHL uexp      (UE_Bin (Shl,  uexp1, uexp2, TSHLleft))
       | uexp TSHR uexp      (UE_Bin (Shr,  uexp1, uexp2, TSHRleft))
       | uexp TAMP uexp      (UE_Bin (BAnd, uexp1, uexp2, TAMPleft))
       | uexp TBAR uexp      (UE_Bin (BOr,  uexp1, uexp2, TBARleft))
       | uexp TCARET uexp    (UE_Bin (BXor, uexp1, uexp2, TCARETleft))
       | uexp TEQEQ uexp     (UE_Bin (Eq,   uexp1, uexp2, TEQEQleft))
       | uexp TNE uexp       (UE_Bin (Ne,   uexp1, uexp2, TNEleft))
       | uexp TLT uexp       (UE_Bin (Lt,   uexp1, uexp2, TLTleft))
       | uexp TLE uexp       (UE_Bin (Le,   uexp1, uexp2, TLEleft))
       | uexp TGT uexp       (UE_Bin (Gt,   uexp1, uexp2, TGTleft))
       | uexp TGE uexp       (UE_Bin (Ge,   uexp1, uexp2, TGEleft))
       | uexp TAMPAMP uexp   (UE_Bin (And,  uexp1, uexp2, TAMPAMPleft))
       | uexp TBARBAR uexp   (UE_Bin (Or,   uexp1, uexp2, TBARBARleft))
  (* Branches are brace-delimited, and right-associative TIF/TELSE precedence preserves nearest-else
     association through recursive mixed chains. The whole grammar is verified conflict-free via the
     [verbose] grm.desc export -- RE-CHECK IT after any grammar change. *)
  ublock : TLBRACE ubody TRBRACE            (UE_Block (ubody, TLBRACEleft))
         | TLBRACE TRBRACE                  (UE_Block (UE_Unit TLBRACEleft, TLBRACEleft))
  (* Unsafe is block-like in operand and statement positions, but deliberately remains distinct from
     `ublock`: branch delimiters still require ordinary braces. Its frontend semantics are block erasure. *)
  uunsafe : TUNSAFE ublock                  (ublock)
  (* Placement and semicolon policy are independent: with-block atoms are ordinary operands, control
     expressions are values, and either category may be sequenced without a semicolon when another
     body follows. *)
  uwith_block_atom : ublock                 (ublock)
                   | uunsafe                (uunsafe)
  usemi_free_stmt : uwith_block_atom ubody
                      (UE_Seq (uwith_block_atom, ubody))
                  | ucontrol_expr ubody
                      (UE_Seq (ucontrol_expr, ubody))
  ucontrol_expr : uconditional              (uconditional)
                | uloop_expr                (uloop_expr)
                | umatch                    (umatch)
  (* Conditional heads are grammar-private. One fallback grammar preserves nearest-else association,
     mixed `else if` / `else if let` chains, and the existing AST/span representation. *)
  uif_head : TIF uval
                (IH_If (uval, TIFleft))
           | TIF TLET upat TEQ uval
                (IH_IfLet (upat, uval, TIFleft))
  uconditional : uif_head ublock %prec TIF
                    (finish_conditional
                      (uif_head, ublock, NONE, ublockright))
               | uif_head ublock TELSE ublock
                    (finish_conditional
                      (uif_head, ublock1, SOME ublock2, ublock2right))
               | uif_head ublock TELSE uconditional
                    (finish_conditional
                      (uif_head, ublock, SOME uconditional,
                       uconditionalright))
  ufuel : THASH TLBRACK TFUEL LPAR EXPRAQ RPAR TRBRACK
              ((EXPRAQ, THASHleft))
  uloop_expr : ufuel TWHILE LPAR uval RPAR ublock
              (UE_While (#1 ufuel, uval, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | ufuel TLOOP ublock
              (UE_Loop (#1 ufuel, ublock,
                Position.range_position (#2 ufuel, ublockright)))
             | TFOR upat TIN uval ublock
              (UE_For (upat, uval, ublock,
                Position.range_position (TFORleft, ublockright)))
             | ufuel TWHILE TLET upat TEQ uval ublock
              (UE_WhileLet (#1 ufuel, upat, uval, ublock,
                Position.range_position (#2 ufuel, ublockright)))
  (* Comma lists stay nonempty and right-nested (source order preserved). Each list has an explicit terminal
     comma production, so a trailing separator cannot create an empty element. Call productions are
     path-headed, so LPAR is never in FOLLOW(uexp) as a postfix operator -- no precedence directive
     is needed here (D23). *)
  arglist : uclosure_arg
              ([uclosure_arg])
          | uclosure_arg COMMA
              ([uclosure_arg])
          | uclosure_arg COMMA arglist
              (uclosure_arg :: arglist)
  ucallargs : ([])
            | arglist (arglist)
  (* Macro argument lists deliberately do not share call trailing-comma support. The legacy frontend
     accepts empty lists and comma-separated values, but rejects a terminal comma. *)
  umacroargs : uclosure_arg
                 ([uclosure_arg])
             | uclosure_arg COMMA umacroargs
                 (uclosure_arg :: umacroargs)
  umacrocallargs : ([])
                 | umacroargs             (umacroargs)
  (* A tuple has one element before the comma and a nonempty `arglist` after it. Even when `arglist` has a
     terminal comma, this requires at least two elements and keeps `(x,)` outside the grammar. *)
  (* All match spellings share one production and differ only in the existing flavour tag. Guards reuse
     the complete body grammar, as in the old frontend. One arm production plus the ordinary nonempty
     trailing-comma list keeps guarded and unguarded termination identical. *)
  umatch_kind : TMATCH       ((MF_Auto, TMATCHleft))
              | TMATCHSWITCH ((MF_Switch, TMATCHSWITCHleft))
              | TMATCHCASE   ((MF_Case, TMATCHCASEleft))
  umatch : umatch_kind uval TLBRACE uarms TRBRACE
              (UE_Match
                (#1 umatch_kind, uval, uarms,
                 Position.range_position (#2 umatch_kind, TRBRACEright)))
  uguard : ubody (ubody)
  uarm : upat TARROW uval
            (UR_Arm (upat, NONE, uval))
       | upat TIF uguard TARROW uval
            (UR_Arm (upat, SOME (uguard, TIFleft), uval))
  uarms : uarm                  ([uarm])
        | uarm COMMA            ([uarm])
        | uarm COMMA uarms      (uarm :: uarms)
  (* The single pattern grammar, shared by every binding site above (D28). Its own nonterminals, disjoint
     from `uexp`, so the constructor pattern cannot clash with the call production nor or-`|` with bitwise
     or. It deliberately ACCEPTS more than any one site can lower (a numeral in `let`, a constructor under
     `match_switch`); each site's elaborator rejects the rest WITH A POSITION, which beats a bare "syntax
     error" and keeps one grammar for one language. *)
  (* Pattern precedence is explicit rather than yacc-directed. A chained range is retained long enough
     for a positioned non-associativity diagnostic; disjunctions flatten in source order. *)
  upat : upat_alias               (upat_alias)
        | upat_alias TBAR upat
            (mk_or_pat (upat_alias, upat, TBARleft))
  upat_alias : upat_range         (upat_range)
              | upat_ident TAT upat_alias
                  (mk_alias_pat (upat_ident, upat_alias, TATleft))
  upat_range : upat_prefix        (upat_prefix)
              | upat_range TDOTDOT upat_prefix
                  (P_Range (RK_Exclusive, upat_range, upat_prefix, TDOTDOTleft))
              | upat_range TDOTDOTEQ upat_prefix
                  (P_Range (RK_Inclusive, upat_range, upat_prefix, TDOTDOTEQleft))
  upat_prefix : upat_atom         (upat_atom)
               | TAMP upat_prefix
                   (P_Borrow (BM_Imm, upat_prefix, TAMPleft))
               | TAMP TMUT upat_prefix
                   (P_Borrow (BM_Mut, upat_prefix, TAMPleft))
  upat_atom : upath               (mk_bare_path_pat upath)
             | NUM                (P_Literal (LP_Integer (NUM, NUMleft)))
             | TTRUE              (P_Literal (LP_Bool (true, TTRUEleft)))
             | TFALSE             (P_Literal (LP_Bool (false, TFALSEleft)))
             | STRING             (P_Literal (LP_String (STRING, STRINGleft)))
             | VALAQ              (P_Literal (LP_ValAntiq VALAQ))
             | upath LPAR upats RPAR
                 (mk_ctor_pat (upath, upats))
             | LPAR upat RPAR
                 (P_Group upat)
             | LPAR upat COMMA upats RPAR
                 (P_Tuple (upat :: upats, Position.range_position (LPARleft, RPARright)))
             | TLBRACK TRBRACK
                 (P_Slice ([], Position.range_position (TLBRACKleft, TRBRACKright)))
             | TLBRACK uslice_items TRBRACK
                 (P_Slice (uslice_items, Position.range_position (TLBRACKleft, TRBRACKright)))
             | upath TLBRACE ustruct_fields TRBRACE
                 (mk_struct_pat (upath, ustruct_fields))
  upat_ident : IDENT              ((IDENT, IDENTleft))
  upats : upat %prec TPATCONTEXT ([upat])
        | upat COMMA              ([upat])
        | upat COMMA upats        (upat :: upats)
  uslice_item : upat %prec TPATCONTEXT
                                      (SI_Pat upat)
               | TDOTDOT          (SI_Rest TDOTDOTleft)
  uslice_items : uslice_item      ([uslice_item])
                | uslice_item COMMA
                    ([uslice_item])
                | uslice_item COMMA uslice_items
                    (uslice_item :: uslice_items)
  ustruct_field : IDENT TCOLON upat %prec TPATCONTEXT
                      (SF_Field (IDENT, IDENTleft, upat))
                | IDENT
                      (SF_Shorthand (IDENT, IDENTleft))
                | TDOTDOT
                      (SF_Rest TDOTDOTleft)
  ustruct_fields : ustruct_field  ([ustruct_field])
                 | ustruct_field COMMA
                      ([ustruct_field])
                 | ustruct_field COMMA ustruct_fields
                      (ustruct_field :: ustruct_fields)
\<close>

end
