(* Language-agnostic lexer and elaborator support for ml_lex_yacc parsers. Per-lexer `set` shadows and
   `Tokens.*` constructors remain inside each generated lexer's SML environment. *)

theory Parser_Utils
  imports Main
begin

text\<open> The generated lexer reports character offsets, while Isabelle positions index symbols. Build one
character-to-symbol map per source and use binary search for token positions. \<close>
ML\<open>
structure Parser_Lex_Util =
struct
  type position_map = {fallback : Position.T, spans : (int * Position.T) vector}

  fun inner_syms src =
    let val syms = Input.source_explode src
    in if length syms >= 2 then List.take (tl syms, length syms - 2) else syms end

  fun make_position_map src =
    let
      fun build _ [] = []
        | build offset ((s, pos) :: rest) =
            let val stop = offset + size s
            in (stop, pos) :: build stop rest end
    in {fallback = Input.pos_of src, spans = Vector.fromList (build 0 (inner_syms src))} end

  fun fixed_pos ({fallback, spans} : position_map) yypos =
    if Vector.length spans = 0 then fallback
    else
      let
        val target = yypos - 1
        val n = Vector.length spans
        fun search lo hi =
          if lo >= hi then lo
          else
            let val mid = (lo + hi) div 2
            in if target < #1 (Vector.sub (spans, mid))
               then search lo mid
               else search (mid + 1) hi
            end
        val i = search 0 n
      in #2 (Vector.sub (spans, Int.min (i, n - 1))) end

  (* Derive the report end from the token length. Looking up yypos+len would select the next symbol. *)
  fun report_fixed pos_map (yypos, len, markup, typ) =
    if 0 < len then
      let
        val {line, offset, props, ...} = Position.dest (fixed_pos pos_map yypos)
        val p = Position.make {line = line, offset = offset, end_offset = offset + len, props = props}
      in
        Position.report p markup;
        Position.report_text p Markup.typing typ
      end
    else ()

  fun tokF pos_map (yypos, yytext, markup, typ, cons) =
    (report_fixed pos_map (yypos, size yytext, markup, typ);
     cons (fixed_pos pos_map yypos, fixed_pos pos_map (yypos + size yytext)))

  (* Isabelle_Lex-Yacc's tok_val uses the start for both ends; preserve the real right position. *)
  fun tok_valF pos_map (yypos, yytext, markup, typ, cons, value) =
    (report_fixed pos_map (yypos, size yytext, markup, typ);
     cons (value, fixed_pos pos_map yypos, fixed_pos pos_map (yypos + size yytext)))

  fun ident_pos pos_map (yypos, yytext) =
    let val {line, offset, props, ...} = Position.dest (fixed_pos pos_map yypos)
    in Position.make {line = line, offset = offset, end_offset = offset + size yytext, props = props} end
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
    val free = Free (x, dummyT)
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
