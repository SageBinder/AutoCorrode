(* Parser_Utils: the language-agnostic layer shared by every ml_lex_yacc-based parser here -- the toy
   sandbox (Toy_Lex_Yacc.thy), the uRust parser (Micro_Rust_Parser.thy), and a future C frontend. Two
   structures: `Parser_Lex_Util` (lexer position math, SML_imported into each generated lexer) and
   `Parser_Utils` (elaborator helpers: binders, markup, antiquotations, the parser mutex). The only
   per-language parameter is the def/ref entity-KIND string ("urust_var" / "toy_var"), threaded first so
   each caller partially applies it once.

   NOT shared: each lexer's `the_src` ref + `set` shadow + `Tokens.*` wrappers, which live inside its
   `ml_lex_yacc` block's SML environment and do not carry to another block. Rationale + history:
   notes/claude/urust-parser-design-decisions.md (D19, D28, D29). ASCII escape form throughout. *)

theory Parser_Utils
  imports Main
begin

text\<open> Lexer position math, shared by every ml_lex_yacc parser. It corrects a char-vs-symbol drift in the
\<open>Isabelle_Lex-Yacc\<close> AFP entry, whose \<open>get_pos\<close> indexes a per-symbol vector with the per-character
\<open>yypos\<close>, so markup after a multi-char Isabelle-symbol escape drifts (D19; isabelle-lex-yacc-notes.md
\<open>\<section>2\<close>). Each lexer keeps its own \<open>the_src\<close> ref and passes the source in. \<close>
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

  (* Report colour + typing/sorting markup over [start, start+len) symbols. WARNING: the end must be
     start_offset + len, NOT a second fixed_pos (yypos+len) -- that maps to the symbol FOLLOWING the
     token, so the result depends on the trailing character (last char uncoloured, span shifting with
     whitespace). ASCII tokens => symbol count = len. *)
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

  (* Token builders; `cons` is the parser-specific Tokens constructor, so these stay language-agnostic.
     tokF for value-less tokens, tok_valF for value-carrying ones. tok_valF deliberately passes the REAL
     end position: Isabelle_Lex-Yacc's own tok_val passes the start for both ends, collapsing `Xright` to
     `Xleft` and any span built from it (D29). *)
  fun tokF src (yypos, yytext, markup, typ, sort, cons) =
    (report_fixed src (yypos, size yytext, markup, typ, sort);
     cons (fixed_pos src yypos, fixed_pos src (yypos + size yytext)))

  fun tok_valF src (yypos, yytext, markup, typ, sort, cons, value) =
    (report_fixed src (yypos, size yytext, markup, typ, sort);
     cons (value, fixed_pos src yypos, fixed_pos src (yypos + size yytext)))

  (* Full-range identifier position with NO markup: the elaborator colours an identifier once it knows
     its role (bound / const / free), so it emits exactly one correctly-ranged report (D14). *)
  fun ident_pos src (yypos, yytext) =
    let val {line, offset, props, ...} = Position.dest (fixed_pos src yypos)
    in Position.make {line = line, offset = offset, end_offset = offset + size yytext, props = props} end
end
\<close>

ML\<open>
structure Parser_Utils =
struct

(* Per-binder record in the elaboration env: the binder's source-named Free, its name position (the
   click-to-def target), and a serial linking each use (ref) to that def. *)
type var_info = { free : term, def_pos : Position.T, id : int }

(* A bound name -- at its binder and at every use, including inside antiquotations -- is GREEN
   (Markup.bound) and carries a def/ref entity pair for ctrl-click nav; same recipe as Isabelle's
   calculation.ML. `kind` is the entity-kind string. *)
fun report_def kind ctxt id (x, def_pos) =
  (Context_Position.report ctxt def_pos Markup.bound;
   Context_Position.report ctxt def_pos
     (Position.make_entity_markup {def = true} id kind (x, def_pos)))

fun report_ref kind ctxt id (x, def_pos) use_pos =
  (Context_Position.report ctxt use_pos Markup.bound;
   Context_Position.report ctxt use_pos
     (Position.make_entity_markup {def = false} id kind (x, def_pos)))

(* Register a NAMED binder occurrence: fresh serial, def markup, env entry; returns its Free and the
   extended env. Every binding construct goes through this, so colour / nav / capture / antiquotation
   handling is uniform and binder-generic. *)
fun bind_var kind ctxt (env : var_info Symtab.table) (x, def_pos) =
  let
    val id   = serial ()
    val _    = report_def kind ctxt id (x, def_pos)
    val free = Free (x, dummyT)
  in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

(* ANONYMOUS binders (a `_` pattern, or one a desugaring invents) get NO name: build the abstraction
   directly as `Abs`, with a `Bound` index at each reference. TRAP -- do not "improve" this into a fresh
   INVENTED name: the enclosing uRust binders live in this env as source-named Frees, NOT in the proof
   context, so any name-seeding scheme can pick one of them and silently capture (it did: D28). Nameless
   makes capture structurally impossible. `Abs`'s name is a printing hint only (alpha-irrelevant, so
   `refl` conformance is unaffected); Name.uu is Isabelle's own internal-anonymous convention. *)
fun anon_abs body = Abs (Name.uu, dummyT, body)

(* Colour every enclosing bound variable GREEN + click-to-def wherever it occurs in an antiquotation
   body, at any depth. Syntax.parse_term gives the right term and full inner-HOL highlighting but paints
   a captured variable blue (it parses the body in isolation); we overlay Markup.bound afterwards from
   the body's OWN per-symbol positions, so it is the innermost markup and wins. Markup-only. *)
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

(* Parse an antiquotation body as a POSITIONED source (so the inner HOL is highlighted), then overlay the
   bound-variable markup. Enclosing binder names are FIXED in the context before parsing: that reproduces
   the frontend's single-context HOAS, where a binder shadows a same-named const / registered notation --
   without it such a name promotes to that Const and the enclosing Term.lambda cannot capture it
   (divergence D-3). Markup context stays the original ctxt. *)
fun parse_antiq kind ctxt env src =
  let
    val ctxt' = Variable.add_fixes_direct (Symtab.keys env) ctxt
    val t = Syntax.parse_term ctxt' (Syntax.implode_input src)
  in mark_bound kind ctxt env src; t end

(* ONE mutex for every ml_lex_yacc parser command. It MUST be shared, not per-parser: the
   Isabelle_lex_yacc runtime holds GLOBAL refs set per parse, so concurrent parses in DIFFERENT generated
   parsers would clobber each other. *)
val parser_lock = Synchronized.var "parser_lock" ()
fun with_parser_lock (f : unit -> 'a) : 'a =
  Synchronized.change_result parser_lock (fn () => (f (), ()))

end
\<close>

end
