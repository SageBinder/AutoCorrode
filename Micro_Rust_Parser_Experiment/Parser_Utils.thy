(* Parser_Utils: elaborator helpers shared between the toy sandbox (Toy_Lex_Yacc.thy) and the real
   uRust parser (Micro_Rust_Parser.thy). These were byte-identical copies in both (they had already
   caused double-maintenance -- the green-colour fix, mark_bound, the report_fixed end-offset were each
   applied twice), so they live here once. They are PLAIN Isabelle/ML (no ml_lex_yacc / SML env
   coupling) and are called from each theory's `*_Translate` elaborator (an ordinary ML block), which
   is why a single shared ML structure works -- ML defs are cumulative across theory imports.

   NOT shared: the lexer position layer (the_src / fixed_pos / report_fixed / tokF / tok_valF /
   tok_ident) lives inside each `ml_lex_yacc` block's `lex_user_declarations`, which runs in the SML
   environment and is scoped to that one generated lexer (it does not carry to another ml_lex_yacc
   block, even in the same theory). So that layer stays duplicated by necessity; see the pointer
   comments at each lexer.

   The only per-language difference here is the def/ref entity-KIND string ("urust_var" / "toy_var"),
   threaded as the first argument; each caller partially applies it once. ASCII escape form throughout
   (isabelle build rejects raw UTF-8 cartouche delimiters). *)

theory Parser_Utils
  imports Main
begin

text\<open> The lexer position layer, shared across every ml_lex_yacc-based parser (uRust today, the toy, a
future C parser). It corrects the framework's char-vs-symbol position drift: the AFP get_pos indexes a
per-symbol vector with the per-character yypos, so markup after a multi-char Isabelle-symbol escape
drifts. Each generated lexer keeps a tiny \<open>the_src\<close> ref + a \<open>set\<close> shadow (both are
SML-environment / per-lexer, and each lexer's Tokens constructor differs), then delegates the position
MATH here by passing its current source. Kept in Isabelle/ML and SML_imported into each lexer. \<close>
ML\<open>
structure Parser_Lex_Util =
struct
  (* Symbols of the source with the two cartouche-delimiter markers dropped. *)
  fun inner_syms src =
    let val syms = Input.source_explode src
    in if length syms >= 2 then List.take (tl syms, length syms - 2) else syms end

  (* Map a per-CHARACTER yypos to the Position.T of the containing Isabelle symbol. *)
  fun fixed_pos src yypos =
    let
      val syms = inner_syms src
      val target = yypos - 1
      fun go _ [] = Input.pos_of src
        | go _ [(_, p)] = p
        | go acc ((s, p) :: rest) = if target < acc + size s then p else go (acc + size s) rest
    in
      if null syms then Input.pos_of src
      else if target < 0 then #2 (hd syms)
      else go 0 syms
    end

  (* Report colour + typing/sorting markup over [start, start+len). The end is start_offset + len, NOT
     a second fixed_pos (yypos+len): that maps to the symbol FOLLOWING the token (result depends on the
     trailing char, leaving the last char uncoloured / shifting with whitespace). ASCII tokens => symbol
     count = len and end_offset is exclusive. *)
  fun report_fixed src (yypos, len, markup, typ, sort) =
    if 0 < len then
      let
        val {line, offset, props, ...} = Position.dest (fixed_pos src yypos)
        val p = Position.make {line = line, offset = offset, end_offset = offset + len, props = props}
      in Position.report p markup;
         Position.report_text p Markup.typing typ;
         Position.report_text p Markup.sorting sort
      end
    else ()

  (* Report ONLY colour markup over [start, start+len) symbols -- no typing/sorting. This matches how
     Isabelle marks an inner-syntax literal delimiter (lexicon.ML reports_of_token: literals get the
     colour alone, no typing). Used for a letter-symbol delimiter that is consumed as part of a larger
     lexeme and so gets no token of its own -- e.g. the leading \<epsilon> of the expression antiquotation,
     which the frontend renders Markup.literal (keyword1) because \<epsilon> is a letter symbol. len is a
     SYMBOL count (== char count for ASCII); pass 1 to colour a single leading symbol. *)
  fun report_colour src (yypos, len, markup) =
    if 0 < len then
      let
        val {line, offset, props, ...} = Position.dest (fixed_pos src yypos)
        val p = Position.make {line = line, offset = offset, end_offset = offset + len, props = props}
      in Position.report p markup end
    else ()

  (* Token builders: `cons` is the (parser-specific) Tokens constructor, passed in, so these stay
     language-agnostic. tokF for value-less tokens, tok_valF for value-carrying ones. *)
  fun tokF src (yypos, yytext, markup, typ, sort, cons) =
    (report_fixed src (yypos, size yytext, markup, typ, sort);
     cons (fixed_pos src yypos, fixed_pos src (yypos + size yytext)))

  fun tok_valF src (yypos, yytext, markup, typ, sort, cons, value) =
    (report_fixed src (yypos, size yytext, markup, typ, sort);
     cons (value, fixed_pos src yypos, fixed_pos src yypos))

  (* Full-range identifier position, with NO colour markup emitted here -- the elaborator colours each
     identifier once it knows its role (bound / const / free). The caller applies its own Tokens
     constructor (Tokens.IDENT / Tokens.TID) to this position. *)
  fun ident_pos src (yypos, yytext) =
    let val {line, offset, props, ...} = Position.dest (fixed_pos src yypos)
    in Position.make {line = line, offset = offset, end_offset = offset + size yytext, props = props} end
end
\<close>

ML\<open>
structure Parser_Utils =
struct

(* Per-binder record stored in the elaboration env: the binder's source-named Free, the position of
   its name (the click-to-def target), and a fresh serial linking a use (ref) to its binder (def). *)
type var_info = { free : term, def_pos : Position.T, id : int }

(* A bound name -- at its binder and at every use, including inside antiquotations -- is coloured GREEN
   (Markup.bound, like Isabelle's own bound variables / the frontend's resolve_bound) and carries a
   def/ref entity pair (shared serial `id`) for ctrl-click navigation. `kind` is the entity-kind string
   ("urust_var" / "toy_var"). Same recipe Isabelle's calculation.ML uses. *)
fun report_def kind ctxt id (x, def_pos) =
  (Context_Position.report ctxt def_pos Markup.bound;
   Context_Position.report ctxt def_pos
     (Position.make_entity_markup {def = true} id kind (x, def_pos)))

fun report_ref kind ctxt id (x, def_pos) use_pos =
  (Context_Position.report ctxt use_pos Markup.bound;
   Context_Position.report ctxt use_pos
     (Position.make_entity_markup {def = false} id kind (x, def_pos)))

(* Register a binder occurrence: fresh serial, def markup at its name position, env entry; returns
   (its Free, the extended env). EVERY binding construct should go through this -- `let`/`const` today,
   and future closures / for-loops / match patterns -- so colour, click-to-def, capture, and
   antiquotation handling are uniform and binder-generic. *)
fun bind_var kind ctxt (env : var_info Symtab.table) (x, def_pos) =
  let
    val id   = serial ()
    val _    = report_def kind ctxt id (x, def_pos)
    val free = Free (x, dummyT)
  in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

(* Multi-variable binders (tuple `let (a, b) = ...`, a match arm `Some(x, y) => ...`) register EACH
   bound variable through bind_var, threading the env; this returns the Frees (binder order) and the
   env extended with all of them. NOTE: only the per-variable REGISTRATION is generic; how the N Frees
   are abstracted into the term (nested Term.lambda, case_prod, a pattern combinator, ...) is
   necessarily construct-specific and is the binder's own job. *)
fun bind_vars kind ctxt xps env = fold_map (fn xp => fn e => bind_var kind ctxt e xp) xps env

(* Colour every enclosing bound variable GREEN + click-to-def wherever it occurs in an antiquotation
   body -- at ANY depth (\<open>\<llangle>x\<rrangle>\<close>, \<open>\<llangle>x + 1\<rrangle>\<close>,
   \<open>\<llangle>f x (g y)\<rrangle>\<close>). Syntax.parse_term gives the correct term and full inner-HOL
   highlighting, but colours a captured variable blue: it parses the body in isolation, unaware of the
   enclosing binder. So after parsing we overlay Markup.bound (via report_ref) at each bound-variable
   occurrence, computed from the body's OWN per-symbol positions (Input.source_explode) -- no position
   surgery, general for arbitrary bodies. Reported after the parse, it is the innermost markup and so
   wins over parse_term's blue (Rendering.select picks the innermost). Markup-only: the term is exactly
   parse_term's, so capture / conformance is unaffected. *)
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
                 SOME {def_pos, id, ...} =>   (* green + click-to-def, like an ordinary bound use *)
                   report_ref kind ctxt id (nm, def_pos) (Position.range_position (Symbol_Pos.range idsyms))
               | NONE => ());
              go rest
            end
          else go r
  in go (Input.source_explode src) end

(* Parse an antiquotation body (HOL) as a POSITIONED source (so the inner HOL is syntax-highlighted),
   then overlay the green/click markup for any enclosing bound variable it mentions. *)
fun parse_antiq kind ctxt env src =
  let val t = Syntax.parse_term ctxt (Syntax.implode_input src)
  in mark_bound kind ctxt env src; t end

(* A SINGLE mutex shared by every ml_lex_yacc parser command (uRust, the toy, a future C parser). It
   MUST be shared, not per-parser: the Isabelle_lex_yacc runtime holds GLOBAL refs (src / ctxt) set per
   parse, so two concurrent parses in DIFFERENT generated parsers would clobber each other. *)
val parser_lock = Synchronized.var "parser_lock" ()
fun with_parser_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result parser_lock (fn () => (f (), ()))

end
\<close>

end
