theory Micro_Rust_Parser_Elaboration
  imports
    Micro_Rust_Parser_AST
    Parser_Utils
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
begin

section\<open> Elaborator (AST -> shallow terms) \<close>

text\<open>
Each node lowers to the existing shallow HOL constants listed in
\<open>urust-parser-design-decisions.md\<close> \<open>\<section>2\<close>. Bare numerals remain
polymorphic; suffixes pin \<open>N word\<close>. One final \<open>Syntax.check_term\<close> resolves
the \<open>dummyT\<close>-based term.
\<close>
ML\<open>
structure URust_Translate =
struct
  open URust_AST

  (* Generic term construction *)
  (* All Core terms are built with dummyT; a single Syntax.check_term (in the command) resolves types. *)
  fun mk_const name args = Term.list_comb (Const (name, dummyT), args)
  (* Direct check_term input uses the post-parse representation of source positions: an internal type
     constraint whose TFree is decoded by Type_Infer_Context.prepare_positions. *)
  fun mk_const_at name pos args =
    let val posT = TFree (Term_Position.encode_syntax [pos], dummyS)
    in Term.list_comb (Type.constraint posT (Const (name, dummyT)), args) end
  fun mk_literal v = mk_const \<^const_name>\<open>literal\<close> [v]
  fun mk_bindlift1 f e = mk_const \<^const_name>\<open>bindlift1\<close> [f, e]

  (* Calls and integer literals *)
  (* The frontend surface supports arities 0..14. Keep every HOL target compile-checked. *)
  val funcall_consts = Vector.fromList
    [\<^const_name>\<open>funcall0\<close>,  \<^const_name>\<open>funcall1\<close>,
     \<^const_name>\<open>funcall2\<close>,  \<^const_name>\<open>funcall3\<close>,
     \<^const_name>\<open>funcall4\<close>,  \<^const_name>\<open>funcall5\<close>,
     \<^const_name>\<open>funcall6\<close>,  \<^const_name>\<open>funcall7\<close>,
     \<^const_name>\<open>funcall8\<close>,  \<^const_name>\<open>funcall9\<close>,
     \<^const_name>\<open>funcall10\<close>, \<^const_name>\<open>funcall11\<close>,
     \<^const_name>\<open>funcall12\<close>, \<^const_name>\<open>funcall13\<close>,
     \<^const_name>\<open>funcall14\<close>]
  val max_funcall_arity = Vector.length funcall_consts - 1

  fun funcall_const pos n =
    if 0 <= n andalso n <= max_funcall_arity then Vector.sub (funcall_consts, n)
    else error ("urust_expr: unsupported call arity " ^ string_of_int n ^ " (max " ^
                string_of_int max_funcall_arity ^
                "; the frontend's surface lowering caps here)" ^ Position.here pos)

  (* Integer-literal SUFFIX -> HOL type: the SINGLE place suffix knowledge lives, so adding `u128` or the
     signed `i*` types is ONE row here + a conformance golden (D29). *)
  fun int_suffix_typ "u8"    = SOME \<^typ>\<open>8 word\<close>
    | int_suffix_typ "u16"   = SOME \<^typ>\<open>16 word\<close>
    | int_suffix_typ "u32"   = SOME \<^typ>\<open>32 word\<close>
    | int_suffix_typ "u64"   = SOME \<^typ>\<open>64 word\<close>
    | int_suffix_typ "usize" = SOME \<^typ>\<open>64 word\<close>   (* usize is modelled as 64-bit *)
    | int_suffix_typ _       = NONE

  (* A decimal/hex lexeme, optionally followed by a uRust width suffix. *)
  fun parse_int_lit pos lexeme =
    let
      val (numstr, sfx) =
        (case first_field "_" lexeme of
           SOME (a, b) => (a, SOME b)
         | NONE => (lexeme, NONE))
      val value =
        (case (if String.isPrefix "0x" numstr
               then StringCvt.scanString (Int.scan StringCvt.HEX) (String.extract (numstr, 2, NONE))
               else Int.fromString numstr) of
           SOME v => v
         | NONE => error ("urust_expr: cannot read integer literal " ^ quote numstr ^ Position.here pos))
    in
      (case sfx of
         NONE => (value, NONE)
       | SOME suffix =>
           (case int_suffix_typ suffix of
              SOME T => (value, SOME T)
            | NONE => error ("urust_expr: unsupported integer-literal suffix " ^
                quote ("_" ^ suffix) ^ " (supported: _u8 _u16 _u32 _u64 _usize)" ^
                Position.here pos)))
    end

  (* Name resolution and markup *)
  (* Peel the `_type_constraint_` wrapper (and positions) to reach the leaf a name resolved to. TRAP:
     `Syntax.parse_term` wraps a resolved constant in `_type_constraint_` and `Term_Position.strip_positions`
     does NOT remove it, so a naive `Const (c,_)` match falls through and mis-paints `True`/`None`/... as a
     blue free. Markup only -- the returned `t` keeps the wrapper for check_term (D14). *)
  fun ident_leaf t =
    (case Term_Position.strip_positions t of
       Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ u => ident_leaf u
     | u => u)

  (* Resolve a bare identifier in a dispatch CONTEXT (`kind`): NLiteral at value position, NFunction for a
     call callee, or NField after `.`; the CALLER decides the `literal` wrapper (value position wraps, a
     callee/field does not). Three things here are load-bearing (D13/D14; full rationale in the
     design-decisions doc):
       - REGISTERED -> the frontend's urust_dispatch marker, resolved by its globally-installed term_check
         phases (reused, not reimplemented). Its witness must stay a bare `Free`, NOT parse_term'd, so an
         enclosing `Term.lambda` can capture it into a `Bound` -- that is what makes a binder outrank the
         notation table (witness precedence).
       - UNREGISTERED -> `Syntax.parse_term`, because building terms directly bypasses
         `Syntax_Phases.decode_term`, which is what promotes a bare `Free name` to the HOL `Const` (or the
         context-fixed variable). A raw Free would survive as an extra free variable and be rejected.
       - MARKUP is emitted HERE, once, over the token's full range: the token carries none (tok_ident), and
         decode_term's own report lands at Position.none because we hand parse_term a positionless name. *)
  fun ident_term ctxt kind name pos =
    (case Micro_Rust_Names.lookups ctxt kind name of
       [] =>
         let val t = Syntax.parse_term ctxt name in
           (case ident_leaf t of
              Const (c, _) =>
                Context_Position.report ctxt pos
                  (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
            | Free (a, _) =>
                (* decode_term's Free case, reproduced (syntax_phases.ML:304-313): a context-fixed free gets
                   markup_free = nav-to-`fixes` + colour; a genuine free just Markup.free. *)
                (case Proof_Context.lookup_free ctxt a of
                   SOME x =>
                     List.app (Context_Position.report ctxt pos)
                       (Syntax_Phases.markup_free ctxt x)
                 | NONE => Context_Position.report ctxt pos Markup.free)
            | _ => Context_Position.report ctxt pos Markup.free);
           t
         end
     | _  => Micro_Rust_Dispatch.mk_marker kind name pos (Free (name, dummyT)))

  (* Is a bare pattern identifier a data constructor? `Code.is_constr` is the SAME oracle the frontend's
     resolve_constructor_id uses. A constructor resolves to its RAW Const -- not the value embedding a
     value-position id gets, since a pattern head must be the bare constructor; anything else is NONE = a
     variable binder (D27). *)
  fun resolve_ctor ctxt name =
    let val thy = Proof_Context.theory_of ctxt in
      (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
         SOME (Const (full, _)) => if Code.is_constr thy full then SOME (Const (full, dummyT)) else NONE
       | _ => NONE)
    end

  (* Const entity markup (colour + ctrl-click-to-definition) for a resolved pattern constructor head, so
     `Some`/`Ok`/a user ctor navigates like any const. Emitted here rather than in `resolve_ctor`, which
     stays pure because it is also used merely to CLASSIFY (C1). *)
  fun report_ctor_markup ctxt pos (Const (c, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) c)
    | report_ctor_markup _ _ _ = ()

  (* A wildcard binds nothing, so bind_var's colour/nav do not apply -- but it must still get a typing
     tooltip, or ctrl-hover falls through to the enclosing command span (rule C3). *)
  fun report_wildcard ctxt pos = Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

  (* Binding environment *)
  (* Shared binder / markup / antiquotation helpers (Parser_Utils, see there); the entity-kind string is
     partially applied once so the call sites below read unchanged. *)
  val vkind       = "urust_var"
  val report_ref  = Parser_Utils.report_ref vkind
  val bind_var    = Parser_Utils.bind_var vkind
  val parse_antiq = Parser_Utils.parse_antiq vkind
  val anon_abs    = Parser_Utils.anon_abs

  fun literal_pos (LP_Bool (_, pos)) = pos
    | literal_pos (LP_String (_, pos)) = pos
    | literal_pos (LP_ValAntiq src) = Input.pos_of src

  fun mk_string_value raw pos =
    let
      fun mk_bit b =
        Const (if b = 1 then \<^const_name>\<open>True\<close> else \<^const_name>\<open>False\<close>, dummyT)
      fun mk_char c =
        mk_const \<^const_name>\<open>Char\<close>
          (map mk_bit (Integer.radicify 2 8 (String_Syntax.ascii_ord_of c)))
      val chars = map fst (Lexicon.explode_string (raw, pos))
      val list = fold_rev (fn c => fn cs =>
          mk_const \<^const_name>\<open>List.Cons\<close> [mk_char c, cs])
        chars (Const (\<^const_name>\<open>List.Nil\<close>, dummyT))
    in mk_const \<^const_name>\<open>String.implode\<close> [list] end

  fun literal_value ctxt env payload =
    (case payload of
       LP_Bool (b, _) => if b then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>
     | LP_String (raw, pos) => mk_string_value raw pos
     | LP_ValAntiq src => parse_antiq ctxt env src)

  fun literal_expr _ _ (LP_Bool (b, _)) =
        Const (if b then \<^const_name>\<open>Bool_Type.true\<close>
               else \<^const_name>\<open>Bool_Type.false\<close>, dummyT)
    | literal_expr ctxt env payload = mk_literal (literal_value ctxt env payload)

  fun canonical_name name = Long_Name.base_name name
  fun name_matches a b = a = b orelse canonical_name a = canonical_name b
  fun term_name_of (Const (name, _)) = SOME name
    | term_name_of (Free (name, _)) = SOME name
    | term_name_of _ = NONE
  fun type_name_of (Type (name, _)) = SOME name
    | type_name_of _ = NONE

  datatype struct_candidate =
      Constructor_Candidate of {ctor: term, selectors: term list}
    | Record_Candidate of {record_name: string, fields: term list}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of term * (term * Position.T option * ur_pat) list
    | Resolved_Record_Struct of string * (term * Position.T option * ur_pat) list

  (* Struct heads accept either a constructor name or the type name of a single-constructor datatype.
     Records come only from Record.get_info; Ctr_Sugar's record entry describes a different lowering
     domain and must not compete with ordinary constructor candidates. *)
  fun resolve_struct_constructor ctxt (id_name, pos) =
    let
      val id_name' = canonical_name id_name
      val thy = Proof_Context.theory_of ctxt
      val sugars = Ctr_Sugar.ctr_sugars_of ctxt

      fun named_const role term =
        (case term_name_of term of
           SOME name => Const (name, dummyT)
         | NONE =>
             error ("urust_expr: unnamed " ^ role ^ " in constructor metadata" ^
               Position.here pos))
      fun constructor_candidate ctor_name selectors =
        Constructor_Candidate
          {ctor = Const (ctor_name, dummyT),
           selectors = map (named_const "selector") selectors}
      fun from_sugar ({kind = Ctr_Sugar.Record, ...} : Ctr_Sugar.ctr_sugar) = []
        | from_sugar ({T, ctrs, selss, ...} : Ctr_Sugar.ctr_sugar) =
        let
          val ty_name_opt = Option.map canonical_name (type_name_of T)
          (* Old_Datatype uses an empty outer selector list; otherwise rows align with constructors. *)
          val entries =
            if null selss then map (fn ctr => (ctr, [])) ctrs
            else if length ctrs = length selss then ListPair.zip (ctrs, selss)
            else
              error ("urust_expr: inconsistent constructor/selector metadata for " ^
                quote (the_default id_name (type_name_of T)) ^ Position.here pos)
          val direct =
            map_filter (fn (ctr, sels) =>
              (case term_name_of ctr of
                 SOME ctor_name =>
                   if name_matches ctor_name id_name'
                   then
                     SOME (ctor_name, constructor_candidate ctor_name sels)
                   else NONE
               | NONE => NONE)) entries
          val fallback =
            (case (ty_name_opt, entries) of
               (SOME ty_name, [(ctr, sels)]) =>
                 if ty_name = id_name'
                 then
                   (case term_name_of ctr of
                      SOME ctor_name =>
                        [(ctor_name, constructor_candidate ctor_name sels)]
                    | NONE => [])
                 else []
             | _ => [])
        in direct @ fallback end

      fun record_candidate rec_name =
        let
          val resolved_name_opt =
            (type_name_of (Proof_Context.read_type_name {proper = true, strict = false} ctxt rec_name)
              handle ERROR _ => NONE)
          val (record_name, info_opt) =
            (case resolved_name_opt of
               SOME resolved_name => (resolved_name, Record.get_info thy resolved_name)
             | NONE => (rec_name, Record.get_info thy rec_name))
        in
          (case info_opt of
             NONE => NONE
           | SOME info =>
               SOME (record_name,
                 Record_Candidate
                   {record_name = record_name,
                    fields = map (fn (field, _) => Const (field, dummyT)) (#fields info)}))
        end

      fun same_candidate
          (Constructor_Candidate {ctor = ctor1, selectors = selectors1},
           Constructor_Candidate {ctor = ctor2, selectors = selectors2}) =
            ctor1 aconv ctor2 andalso eq_list (op aconv) (selectors1, selectors2)
        | same_candidate
          (Record_Candidate {record_name = name1, fields = fields1},
           Record_Candidate {record_name = name2, fields = fields2}) =
            name1 = name2 andalso eq_list (op aconv) (fields1, fields2)
        | same_candidate _ = false

      fun candidate_description (Constructor_Candidate {ctor, selectors}) =
            "constructor " ^ quote (the_default "<unnamed>" (term_name_of ctor)) ^
              " with selectors [" ^
              space_implode ", " (map (the_default "<unnamed>" o term_name_of) selectors) ^ "]"
        | candidate_description (Record_Candidate {record_name, fields}) =
            "record " ^ quote record_name ^ " with fields [" ^
              space_implode ", " (map (the_default "<unnamed>" o term_name_of) fields) ^ "]"

      fun candidate_key (Constructor_Candidate {ctor, ...}) =
            "C:" ^ the_default "<unnamed>" (term_name_of ctor)
        | candidate_key (Record_Candidate {record_name, ...}) = "R:" ^ record_name

      fun add_candidate (display_name, candidate) candidates =
        let val key = candidate_key candidate in
          (case Symtab.lookup candidates key of
             NONE => Symtab.update (key, (display_name, candidate)) candidates
           | SOME (_, existing) =>
               if same_candidate (existing, candidate) then candidates
               else
                 error ("urust_expr: inconsistent struct metadata for " ^ quote display_name ^
                   ": " ^ candidate_description existing ^ " versus " ^
                   candidate_description candidate ^ Position.here pos))
        end

      val record_candidates =
        map_filter record_candidate (distinct (op =) [id_name, id_name'])
      val candidates =
        fold add_candidate (maps from_sugar sugars @ record_candidates) Symtab.empty
        |> Symtab.dest
        |> map snd
    in
      (case candidates of
         [] =>
           error ("urust_expr: struct pattern " ^ quote id_name ^
             ": no matching constructor or single-constructor record/datatype found" ^
             Position.here pos)
       | [(_, candidate)] => candidate
       | _ =>
           error ("urust_expr: struct pattern " ^ quote id_name ^
             " is ambiguous; candidates: " ^
             space_implode ", " (map fst candidates) ^ Position.here pos))
    end

  fun split_slice_items items =
    let
      fun split prefix rest_pos suffix [] = (rev prefix, rest_pos, rev suffix)
        | split prefix NONE suffix (SI_Rest pos :: rest) =
            split prefix (SOME pos) suffix rest
        | split _ (SOME _) _ (SI_Rest pos :: _) =
            error ("urust_expr: slice pattern has multiple `..` rest entries" ^
                   Position.here pos)
        | split prefix rest_pos suffix (SI_Pat pat :: rest) =
            if is_some rest_pos
            then split prefix rest_pos (pat :: suffix) rest
            else split (pat :: prefix) rest_pos suffix rest
    in split [] NONE [] items end

  fun resolve_struct_pattern ctxt (head, head_pos, fields) =
    let
      val candidate = resolve_struct_constructor ctxt (head, head_pos)
      val (display_name, selectors) =
        (case candidate of
           Constructor_Candidate {ctor, selectors} =>
             (the_default head (Option.map canonical_name (term_name_of ctor)), selectors)
         | Record_Candidate {record_name, fields} =>
             (canonical_name record_name, fields))

      fun selector_entry selector =
        (case term_name_of selector of
           SOME name => (canonical_name name, selector)
         | NONE =>
             error ("urust_expr: unnamed selector in struct metadata for " ^
               quote display_name ^ Position.here head_pos))
      val selector_entries = map selector_entry selectors
      val selector_names = map fst selector_entries

      fun add_field (name, pos, pat) (entries, rest_pos) =
        let val field = canonical_name name in
          (case AList.lookup (op =) entries field of
             SOME _ =>
               error ("urust_expr: struct pattern for " ^ quote display_name ^
                 " has duplicate field " ^ quote field ^ Position.here pos)
           | NONE => ((field, (pos, pat)) :: entries, rest_pos))
        end
      fun collect (SF_Field (name, pos, pat)) state = add_field (name, pos, pat) state
        | collect (SF_Shorthand (name, pos)) state =
            add_field (name, pos, P_Ident (name, pos)) state
        | collect (SF_Rest pos) (entries, NONE) = (entries, SOME pos)
        | collect (SF_Rest pos) (_, SOME _) =
            error ("urust_expr: struct pattern has multiple `..` rest entries" ^
                   Position.here pos)

      val (entries_rev, rest_pos) = fold collect fields ([], NONE)
      val entries = rev entries_rev
      val unknown =
        get_first (fn (name, (pos, _)) =>
          if member (op =) selector_names name then NONE else SOME (name, pos)) entries
      val _ =
        (case unknown of
           NONE => ()
         | SOME (name, pos) =>
             error ("urust_expr: struct pattern for " ^ quote display_name ^
               " has unknown field " ^ quote name ^ Position.here pos))
      val missing =
        if is_some rest_pos then []
        else filter_out (AList.defined (op =) entries) selector_names
      val _ =
        if null missing then ()
        else error ("urust_expr: struct pattern for " ^ quote display_name ^
          " is missing field(s): " ^ space_implode ", " missing ^ Position.here head_pos)
      val ordered =
        map (fn (name, selector) =>
          (case AList.lookup (op =) entries name of
             SOME (pos, pat) => (selector, SOME pos, pat)
           | NONE => (selector, NONE, P_Wild Position.none)))
          selector_entries
    in
      (case candidate of
         Constructor_Candidate {ctor, ...} =>
           Resolved_Constructor_Struct (ctor, ordered)
       | Record_Candidate {record_name, ...} =>
           Resolved_Record_Struct (record_name, ordered))
    end

  fun unsupported_record_pattern record_name pos =
    error ("urust_expr: HOL record pattern " ^ quote (canonical_name record_name) ^
      " requires selector-based lowering" ^ Position.here pos)

  (* Core expression constructors *)
  (* `let x = e; k` -> bind e (\<lambda>x. k) (HOAS). Sequencing MUST be `sequence`, not `bind e (\<lambda>_. k)`:
     the latter is definitionally but NOT alpha-equal to the frontend, so `refl` conformance would fail. *)
  fun mk_bind e f     = mk_const \<^const_name>\<open>Core_Expression.bind\<close> [e, f]
  fun mk_sequence a b = mk_const \<^const_name>\<open>Core_Expression.sequence\<close> [a, b]
  fun mk_case_prod f  = mk_const \<^const_name>\<open>case_prod\<close> [f]
  fun mk_ref_new pos e =
    mk_const \<^const_name>\<open>funcall1\<close>
      [mk_const_at \<^const_name>\<open>store_reference_const\<close> pos [], e]
  fun mk_borrow mode pos e =
    mk_bindlift1
      (mk_const_at
        (case mode of
           BM_Imm => \<^const_name>\<open>ro_ref_from_ref\<close>
         | BM_Mut => \<^const_name>\<open>mut_ref_from_ref\<close>)
        pos [])
      e
  fun mk_deref pos e =
    mk_bind e
      (mk_const \<^const_name>\<open>deep_compose1\<close>
        [Const (\<^const_name>\<open>call\<close>, dummyT),
         mk_const_at \<^const_name>\<open>store_dereference_const\<close> pos []])
  fun mk_update pos place rhs =
    mk_const \<^const_name>\<open>bind2\<close>
      [mk_const \<^const_name>\<open>deep_compose2\<close>
        [Const (\<^const_name>\<open>call\<close>, dummyT),
         mk_const_at \<^const_name>\<open>store_update_const\<close> pos []],
       place, rhs]
  fun mk_assign_add pos place rhs =
    mk_const \<^const_name>\<open>funcall2\<close>
      [mk_const_at \<^const_name>\<open>assign_add_const\<close> pos [], place, rhs]

  fun mk_ident_expr ctxt env (name, pos) =
    (case Symtab.lookup env name of
       SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) pos; mk_literal free)
     | NONE => mk_literal (ident_term ctxt Micro_Rust_Names.NLiteral name pos))

  fun mk_field ctxt receiver name pos =
    let
      val field = ident_term ctxt Micro_Rust_Names.NField name pos
      val focus = mk_const \<^const_name>\<open>focus_lens_const\<close> [field]
    in mk_bindlift1 focus receiver end

  fun mk_tuple_lift terminal a b =
    let
      val x = Free ("x", dummyT)
      val y = Free ("y", dummyT)
      fun pair u v = mk_const \<^const_name>\<open>Product_Type.Pair\<close> [u, v]
      val result =
        if terminal
        then pair x (pair y (Const (\<^const_name>\<open>TNil\<close>, dummyT)))
        else pair x y
      val f = Term.lambda x (Term.lambda y result)
    in mk_const \<^const_name>\<open>bindlift2\<close> [f, a, b] end

  fun mk_tuple [a, b] = mk_tuple_lift true a b
    | mk_tuple (a :: rest) = mk_tuple_lift false a (mk_tuple rest)
    | mk_tuple _ = error "urust_expr: internal tuple with fewer than two elements"

  (* if c {t} else {e} -> two_armed_conditional. A one-armed `if` fills the else with `skip`: the frontend's
     `{..}` path emits two_armed_conditional c t skip, NOT one_armed_conditional, and `skip` is an (input)
     abbreviation for `literal ()` -- so we must emit `literal ()` here (D22). *)
  fun mk_two_armed c t e = mk_const \<^const_name>\<open>two_armed_conditional\<close> [c, t, e]

  (* Operators *)
  (* Operator -> HOL const, one row each (the frontend's shallow-embedding targets: `+` is the overloaded
     urust_add, other arithmetic/shift/bitwise are the Numeric_Types word combinators, comparisons and
     connectives the comp_*/urust_* ones). *)
  fun binop_const Add  = \<^const_name>\<open>urust_add\<close>
    | binop_const Sub  = \<^const_name>\<open>word_minus_no_wrap\<close>
    | binop_const Mul  = \<^const_name>\<open>word_mul_no_wrap\<close>
    | binop_const Div  = \<^const_name>\<open>word_udiv\<close>
    | binop_const Mod  = \<^const_name>\<open>word_umod\<close>
    | binop_const Shl  = \<^const_name>\<open>word_shift_left_shift64\<close>
    | binop_const Shr  = \<^const_name>\<open>word_shift_right_shift64\<close>
    | binop_const BAnd = \<^const_name>\<open>word_bitwise_and\<close>
    | binop_const BOr  = \<^const_name>\<open>word_bitwise_or\<close>
    | binop_const BXor = \<^const_name>\<open>word_bitwise_xor\<close>
    | binop_const Eq   = \<^const_name>\<open>urust_eq\<close>
    | binop_const Ne   = \<^const_name>\<open>urust_neq\<close>
    | binop_const Lt   = \<^const_name>\<open>comp_lt\<close>
    | binop_const Le   = \<^const_name>\<open>comp_le\<close>
    | binop_const Gt   = \<^const_name>\<open>comp_gt\<close>
    | binop_const Ge   = \<^const_name>\<open>comp_ge\<close>
    | binop_const And  = \<^const_name>\<open>urust_conj\<close>
    | binop_const Or   = \<^const_name>\<open>urust_disj\<close>
  fun unop_const Not = \<^const_name>\<open>negation_const\<close>
  fun binop_of_assign_binop AssignSub  = Sub
    | binop_of_assign_binop AssignMul  = Mul
    | binop_of_assign_binop AssignMod  = Mod
    | binop_of_assign_binop AssignBAnd = BAnd
    | binop_of_assign_binop AssignBOr  = BOr
    | binop_of_assign_binop AssignBXor = BXor
    | binop_of_assign_binop AssignShl  = Shl
    | binop_of_assign_binop AssignShr  = Shr
  fun mk_bin bop a b = mk_const (binop_const bop) [a, b]
  fun mk_un uop a    = mk_const (unop_const uop) [a]

  (* Patterns and match routing *)
  (* The IRREFUTABLE pattern seam (`let`/`const`, later closure and `fn` parameters): register the
     pattern's variable(s), return an abstraction builder for the binder's body + the extended env.
     Case normalization below is the refutable (match-arm) seam and the `MF_Switch` `key` function the
     first-order one; all three consume the SAME `ur_pat`, so a new pattern form is one constructor plus
     one clause per seam, with every binding SITE unchanged (D28). *)
  fun pat_pos (P_Wild pos) = pos
    | pat_pos (P_Ident (_, pos)) = pos
    | pat_pos (P_Lit (_, pos)) = pos
    | pat_pos (P_Value payload) = literal_pos payload
    | pat_pos (P_Constr (_, pos, _)) = pos
    | pat_pos (P_Tuple (_, pos)) = pos
    | pat_pos (P_Group pat) = pat_pos pat
    | pat_pos (P_Borrow (_, _, pos)) = pos
    | pat_pos (P_Alias (_, _, _, pos)) = pos
    | pat_pos (P_Range (_, _, _, pos)) = pos
    | pat_pos (P_Slice (_, pos)) = pos
    | pat_pos (P_Struct (_, pos, _)) = pos
    | pat_pos (P_Or (_, pos)) = pos

  fun strip_group_pat (P_Group pat) = strip_group_pat pat
    | strip_group_pat pat = pat

  fun strip_case_transparent_pat pat =
    (case strip_group_pat pat of
       P_Borrow (_, inner, _) => strip_case_transparent_pat inner
     | inner => inner)

  fun arm_pat (UR_Arm (pat, _, _)) = pat
  fun arm_guard (UR_Arm (_, guard, _)) = guard

  (* Bare `match` mirrors the frontend's syntactic head-based router. Any guard forces case lowering.
     Otherwise identifiers and `_` fit either lowering, so case wins; a disjunction is case-shaped even
     when its alternatives are numerals. *)
  fun classify_match arms pos =
    let
      fun case_compatible pat =
        (case strip_group_pat pat of P_Lit _ => false | _ => true)
      fun switch_compatible pat =
        (case strip_group_pat pat of
           P_Lit _ => true
         | P_Ident _ => true
         | P_Wild _ => true
         | _ => false)
      val pats = map arm_pat arms
    in
      if List.exists (is_some o arm_guard) arms then MF_Case
      else if List.all case_compatible pats then MF_Case
      else if List.all switch_compatible pats then MF_Switch
      else
        error ("urust_expr: mixed numeral and constructor patterns in bare `match`" ^
               Position.here pos)
    end

  fun bind_pat ctxt env pat =
    (case strip_group_pat pat of
       (* A bare id here is ALWAYS a variable binder, deliberately NOT run through resolve_ctor: the
          frontend's `let` binder is a plain identifier, so `let None = e; ..` binds a variable named
          `None`, and rejecting it as a nullary constructor would be a DIVERGENCE, not extra fidelity. *)
       P_Ident (x, def_pos) =>
         let val (free, env') = bind_var ctxt env (x, def_pos)
         in (fn body => Term.lambda free body, env') end
       (* `let _ = e; k` binds nothing: an anonymous lambda, NOT a variable literally named "_" (that
          leaked a `Free "_"` into the defined term). *)
     | P_Wild pos =>
         (report_wildcard ctxt pos;
          (fn body => anon_abs body, env))
     | P_Tuple (pats, _) =>
         let
           val (absfs, env') = fold_map (fn p => fn env' => bind_pat ctxt env' p) pats env
           fun tuple_abs [absf] body = mk_case_prod (absf (anon_abs body))
             | tuple_abs (absf :: rest) body = mk_case_prod (absf (tuple_abs rest body))
             | tuple_abs [] _ = error "urust_expr: internal empty tuple pattern"
         in (fn body => tuple_abs absfs body, env') end
     | _ =>
         error ("urust_expr: refutable pattern in an irrefutable (let/const) binder position" ^
                Position.here (pat_pos pat)))

  (* Match-switch lowering *)
  (* match_switch -> bind <<scrut>> (ncase_selector [(key, body), ..]): numeral key -> Some n, `_` -> None,
     each or-alternative its own pair with the same body. First-order -- no binders, no case skeleton (D26). *)
  fun mk_some v = mk_const \<^const_name>\<open>Option.Some\<close> [v]
  val mk_none   = Const (\<^const_name>\<open>Option.None\<close>, dummyT)
  fun mk_pair a b = mk_const \<^const_name>\<open>Product_Type.Pair\<close> [a, b]
  fun mk_cons h t = mk_const \<^const_name>\<open>List.Cons\<close> [h, t]
  val mk_nil      = Const (\<^const_name>\<open>List.Nil\<close>, dummyT)
  fun mk_ncase_selector lst = mk_const \<^const_name>\<open>ncase_selector\<close> [lst]

  (* Match-case lowering *)
  datatype basic_case_pat =
      BCP_Wild of Position.T option
    | BCP_Ident of string * Position.T
    | BCP_Generated of term
    | BCP_Constr of string * Position.T * basic_case_pat list
    | BCP_Resolved of term * basic_case_pat list
    | BCP_Tuple of basic_case_pat list

  datatype case_pat =
      CP_Wild of Position.T
    | CP_Ident of string * Position.T
    | CP_Lit of string * Position.T
    | CP_Value of term * Position.T
    | CP_Constr of string * Position.T * case_pat list
    | CP_Resolved of term * case_pat list
    | CP_Tuple of case_pat list
    | CP_Alias of string * Position.T * case_pat
    | CP_Range of range_kind * term * term * Position.T
    | CP_SliceSuffix of case_pat

  datatype case_pat_tree =
      CPT_Const of term
    | CPT_Slot of int
    | CPT_App of term * case_pat_tree list

  (* Ctr_Sugar case skeleton (match_case, D27): case_guard/case_cons/case_nil/case_elem/case_abs are
     uninterpreted HOL markers, and the Case_Translation term-check phase folds a well-formed tree into the
     datatype's concrete `case_<T>` DURING our single check_term. So we build exactly the frontend's
     skeleton and never construct case_option / case_result ourselves. *)
  fun mk_case_guard b s cs = mk_const \<^const_name>\<open>case_guard\<close> [b, s, cs]
  fun mk_case_cons h t     = mk_const \<^const_name>\<open>case_cons\<close> [h, t]
  val mk_case_nil          = Const (\<^const_name>\<open>case_nil\<close>, dummyT)
  fun mk_case_elem p b     = mk_const \<^const_name>\<open>case_elem\<close> [p, b]
  fun mk_case_abs f        = mk_const \<^const_name>\<open>case_abs\<close> [f]

  (* Abstract a mixed list of binder SLOTS over an inner term, leftmost binder OUTERMOST: `SOME free` is a
     NAMED source binder (abstracted by name, so its occurrences anywhere inside are captured -- HOAS),
     `NONE` an ANONYMOUS one, referenced only through the `Bound` index handed to `mk_inner`. `wrap` goes
     around each abstraction (Ctr_Sugar's `case_abs` here). For a SINGLE binder, abstract directly instead
     (`Term.lambda` / `anon_abs`); this exists for the several-binders case, where the indices interact.

     Mixing the two kinds is sound because the indices handed out are the FINAL ones (counting all `n`
     abstractions): `Term.abstract_over` (behind `Term.lambda`) tracks its own level as it descends and
     LEAVES existing `Bound`s untouched (Pure/term.ML:841-852), while each `Abs` binds the loose index 0 of
     its body. So a pre-placed index still denotes its slot after any number of outer abstractions.
     uRust-specific (the only caller is the recursive case-pattern compiler below), so it lives here
     rather than in the shared Parser_Utils layer. *)
  fun abs_slots wrap slots mk_inner =
    let
      val n = length slots
      val args = map_index (fn (_, SOME free) => free | (j, NONE) => Bound (n - 1 - j)) slots
    in
      fold_rev (fn slot => fn t =>
          wrap (case slot of SOME free => Term.lambda free t | NONE => anon_abs t))
        slots (mk_inner args)
    end

  (* Expand every disjunction before binding. Constructor arguments use a left-to-right Cartesian product,
     matching the frontend's source ordering. Each resulting arm is elaborated independently. *)
  fun expand_case_pat pat =
    let
      fun products [] = [[]]
        | products (xs :: xss) =
            let val tails = products xss
            in maps (fn x => map (fn ys => x :: ys) tails) xs end
      fun expand (P_Or (ps, _)) = maps expand ps
        | expand (P_Constr (name, pos, args)) =
            map (fn args' => P_Constr (name, pos, args'))
              (products (map expand args))
        | expand (P_Tuple (args, pos)) =
            map (fn args' => P_Tuple (args', pos))
              (products (map expand args))
        | expand (P_Group inner) =
            map P_Group (expand inner)
        | expand (P_Borrow (mode, inner, pos)) =
            map (fn inner' => P_Borrow (mode, inner', pos)) (expand inner)
        | expand (P_Alias (name, npos, inner, apos)) =
            map (fn inner' => P_Alias (name, npos, inner', apos)) (expand inner)
        | expand (P_Range (kind, lo, hi, pos)) =
            maps (fn lo' =>
              map (fn hi' => P_Range (kind, lo', hi', pos)) (expand hi)) (expand lo)
        | expand (P_Slice (items, pos)) =
            let
              fun item_alts (SI_Pat p) = map SI_Pat (expand p)
                | item_alts (SI_Rest p) = [SI_Rest p]
            in map (fn items' => P_Slice (items', pos))
                 (products (map item_alts items)) end
        | expand (P_Struct (name, npos, fields)) =
            let
              fun field_alts (SF_Field (field, fpos, p)) =
                    map (fn p' => SF_Field (field, fpos, p')) (expand p)
                | field_alts (SF_Shorthand field) = [SF_Shorthand field]
                | field_alts (SF_Rest p) = [SF_Rest p]
            in map (fn fields' => P_Struct (name, npos, fields'))
                 (products (map field_alts fields)) end
        | expand p = [p]
    in expand pat end

  (* Register every source binder once for an expanded alternative. Guard and body elaboration then reuse
     the same Free, preserving capture and source navigation, including inside antiquotations. *)
  fun bind_case_vars ctxt pat env =
    (case strip_case_transparent_pat pat of
       P_Wild _ => env
     | P_Lit _ => env
     | P_Value _ => env
     | P_Ident (name, pos) =>
         (case resolve_ctor ctxt name of
            SOME _ => env
          | NONE => #2 (bind_var ctxt env (name, pos)))
     | P_Constr (name, pos, args) =>
         (case resolve_ctor ctxt name of
            NONE => error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^
                           Position.here pos)
          | SOME _ => fold (bind_case_vars ctxt) args env)
     | P_Tuple (args, _) => fold (bind_case_vars ctxt) args env
     | P_Alias ("_", pos, _, _) =>
         error ("urust_expr: alias pattern binder cannot be `_`" ^ Position.here pos)
     | P_Alias (name, pos, inner, _) =>
         bind_case_vars ctxt inner (#2 (bind_var ctxt env (name, pos)))
     | P_Range _ => env
     | P_Slice (items, _) =>
         let
           val _ = split_slice_items items
           fun bind_item (SI_Pat p) env' = bind_case_vars ctxt p env'
             | bind_item (SI_Rest _) env' = env'
         in fold bind_item items env end
     | P_Struct (name, pos, fields) =>
         (case resolve_struct_pattern ctxt (name, pos, fields) of
            Resolved_Constructor_Struct (_, ordered) =>
              fold (fn (_, _, p) => bind_case_vars ctxt p) ordered env
          | Resolved_Record_Struct (record_name, _) =>
              unsupported_record_pattern record_name pos)
     | P_Or (_, pos) =>
         error ("urust_expr: internal unexpanded case or-pattern" ^ Position.here pos))

  (* Literal payloads are elaborated once after the arm's source binders have been registered. Nested
     guard/extraction matches then reuse the resulting term, preserving antiquotation capture and markup. *)
  fun pattern_value_expr ctxt env pat =
    (case strip_group_pat pat of
       P_Lit (lexeme, pos) =>
         let val (value, _) = parse_int_lit pos lexeme
         in mk_literal (HOLogic.mk_number dummyT value) end
     | P_Value payload => mk_literal (literal_value ctxt env payload)
     | P_Ident (name, pos) =>
         (case Symtab.lookup env name of
            SOME {free, def_pos, id} =>
              (report_ref ctxt id (name, def_pos) pos; mk_literal free)
          | NONE => mk_literal (ident_term ctxt Micro_Rust_Names.NLiteral name pos))
     | _ =>
         error ("urust_expr: invalid range-pattern endpoint" ^
                Position.here (pat_pos pat)))

  fun prepare_case_pattern ctxt env pat =
    (case strip_case_transparent_pat pat of
       P_Wild p => CP_Wild p
     | P_Ident id => CP_Ident id
     | P_Lit lit => CP_Lit lit
     | P_Value payload => CP_Value (literal_value ctxt env payload, literal_pos payload)
     | P_Constr (name, p, args) =>
         CP_Constr (name, p, map (prepare_case_pattern ctxt env) args)
     | P_Tuple (args, _) =>
         CP_Tuple (map (prepare_case_pattern ctxt env) args)
     | P_Alias (name, pos, inner, _) =>
         CP_Alias (name, pos, prepare_case_pattern ctxt env inner)
     | P_Range (_, P_Range _, _, pos) =>
         error ("urust_expr: range patterns are non-associative" ^ Position.here pos)
     | P_Range (kind, lo, hi, pos) =>
         CP_Range (kind, pattern_value_expr ctxt env lo, pattern_value_expr ctxt env hi, pos)
     | P_Slice (items, _) =>
         let
           val (prefix, rest_pos, suffix) = split_slice_items items
           fun cons_chain pats tail =
             fold_rev (fn p => fn rest =>
                 CP_Resolved (Const (\<^const_name>\<open>List.Cons\<close>, dummyT),
                   [prepare_case_pattern ctxt env p, rest])) pats tail
           val nil_pat = CP_Resolved (Const (\<^const_name>\<open>List.Nil\<close>, dummyT), [])
         in
           (case rest_pos of
              NONE => cons_chain prefix nil_pat
            | SOME _ =>
                if null suffix
                then cons_chain prefix (CP_Wild Position.none)
                else cons_chain prefix
                  (CP_SliceSuffix (cons_chain (rev suffix) nil_pat)))
         end
     | P_Struct (name, pos, fields) =>
         (case resolve_struct_pattern ctxt (name, pos, fields) of
            Resolved_Constructor_Struct (ctor, ordered) =>
              let
                val _ = report_ctor_markup ctxt pos ctor
                fun prepare_field (selector, field_pos, field_pat) =
                  (case field_pos of
                     SOME p => report_ctor_markup ctxt p selector
                   | NONE => ();
                   prepare_case_pattern ctxt env field_pat)
              in CP_Resolved (ctor, map prepare_field ordered) end
          | Resolved_Record_Struct (record_name, _) =>
              unsupported_record_pattern record_name pos)
     | P_Or (_, p) =>
         error ("urust_expr: internal unexpanded case or-pattern" ^ Position.here p))

  (* Preserve recursive constructors in the basic case tree. Case numerals are rejected at any depth,
     matching the frontend acceptance boundary; switch numerals continue to use `ncase_selector`. *)
  fun normalize_basic_case_pattern pat =
    (case pat of
       CP_Wild p => BCP_Wild (SOME p)
     | CP_Ident id => BCP_Ident id
     | CP_Lit (lexeme, p) =>
         error ("urust_expr: numeric pattern in match_case: " ^ lexeme ^ Position.here p)
     | CP_Value (_, p) =>
         error ("urust_expr: internal unnormalized value pattern" ^ Position.here p)
     | CP_Constr (name, p, args) =>
         BCP_Constr (name, p, map normalize_basic_case_pattern args)
     | CP_Resolved (ctor, args) =>
         BCP_Resolved (ctor, map normalize_basic_case_pattern args)
     | CP_Tuple args =>
         BCP_Tuple (map normalize_basic_case_pattern args)
     | CP_Alias (_, p, _) =>
         error ("urust_expr: internal unnormalized alias pattern" ^ Position.here p)
     | CP_Range (_, _, _, p) =>
         error ("urust_expr: internal unnormalized range pattern" ^ Position.here p)
     | CP_SliceSuffix _ =>
         error "urust_expr: internal unnormalized slice suffix pattern")

  fun instantiate_case_pat args tree =
    (case tree of
       CPT_Const t => t
     | CPT_Slot i => nth args i
     | CPT_App (c, ts) => Term.list_comb (c, map (instantiate_case_pat args) ts))

  (* Convert one normalized basic pattern into the Ctr_Sugar branch skeleton. Slots are collected in
     depth-first source order; named slots use their source Free and wildcards use final Bound indices. *)
  fun bind_basic_case_pat ctxt env pat =
    let
      fun add_slot slot (slots_rev, n) = (CPT_Slot n, (slot :: slots_rev, n + 1))
      fun walk (BCP_Wild pos_opt) state =
            (case pos_opt of SOME pos => report_wildcard ctxt pos | NONE => ();
             add_slot NONE state)
        | walk (BCP_Ident (name, pos)) state =
            (case resolve_ctor ctxt name of
               SOME c => (report_ctor_markup ctxt pos c; (CPT_Const c, state))
             | NONE =>
                 (case Symtab.lookup env name of
                    SOME {free, ...} => add_slot (SOME free) state
                  | NONE => error ("urust_expr: internal unregistered case binder " ^ quote name ^
                                    Position.here pos)))
        | walk (BCP_Generated free) state = add_slot (SOME free) state
        | walk (BCP_Constr (name, pos, args)) state =
            (case resolve_ctor ctxt name of
               NONE => error ("urust_expr: `" ^ name ^ "` is not a known constructor" ^
                              Position.here pos)
             | SOME c =>
                 let
                   val _ = report_ctor_markup ctxt pos c
                   val (trees, state') = fold_map walk args state
                 in (CPT_App (c, trees), state') end)
        | walk (BCP_Resolved (ctor, args)) state =
            let
              val (trees, state') = fold_map walk args state
            in (CPT_App (ctor, trees), state') end
        | walk (BCP_Tuple args) state =
            let
              fun tuple_tree [] state' =
                    (CPT_Const (Const (\<^const_name>\<open>TNil\<close>, dummyT)), state')
                | tuple_tree (arg :: rest) state' =
                    let
                      val (arg_tree, state'') = walk arg state'
                      val (rest_tree, state''') = tuple_tree rest state''
                    in
                      (CPT_App (Const (\<^const_name>\<open>Product_Type.Pair\<close>, dummyT),
                                [arg_tree, rest_tree]),
                       state''')
                    end
            in tuple_tree args state end
      val (tree, (slots_rev, _)) = walk pat ([], 0)
    in
      fn body =>
        abs_slots mk_case_abs (rev slots_rev)
          (fn args => mk_case_elem (instantiate_case_pat args tree) body)
    end

  fun case_requires_nested pat =
    (case pat of
       CP_Value _ => true
     | CP_Alias _ => true
     | CP_Range _ => true
     | CP_SliceSuffix _ => true
     | CP_Constr (_, _, args) => List.exists case_requires_nested args
     | CP_Resolved (_, args) => List.exists case_requires_nested args
     | CP_Tuple args => List.exists case_requires_nested args
     | _ => false)

  fun extend_case_guard generated NONE = SOME generated
    | extend_case_guard generated (SOME source) = SOME (mk_bin And source generated)

  fun mk_rev_expr expr =
    mk_bindlift1 (Const (\<^const_name>\<open>List.rev\<close>, dummyT)) expr

  fun alias_wrapper env expr name pos rhs =
    (case Symtab.lookup env name of
       SOME {free, ...} => mk_bind expr (Term.lambda free rhs)
     | NONE =>
         error ("urust_expr: internal unregistered alias binder " ^ quote name ^
                Position.here pos))

  (* Compile normalized branches either as one Ctr_Sugar case tree (the fast unguarded path) or as ordered
     cases whose guarded bodies fall through to the remaining tree. Extended value patterns recursively
     invoke this compiler for the frontend's nested guard/extraction wrappers. *)
  fun compile_case ctxt scrut arms =
    let
      val value = Free ("_urust_case_value_" ^ string_of_int (serial ()), dummyT)
      val normalized = map (normalize_case_arm ctxt value) arms
      fun case_term branches =
        mk_case_guard \<^term>\<open>True\<close> value
          (fold_rev mk_case_cons branches mk_case_nil)
      fun generated_wild rhs = bind_basic_case_pat ctxt Symtab.empty (BCP_Wild NONE) rhs
      val undefined = Const (\<^const_name>\<open>undefined\<close>, dummyT)
      fun process [] = error "urust_expr: internal empty case branch list"
        | process [(wild, absf, NONE, rhs)] =
            if wild then rhs else case_term [absf rhs]
        | process [(wild, absf, SOME guard, rhs)] =
            let val guarded = mk_two_armed guard rhs undefined
            in
              if wild then guarded
              else case_term [absf guarded, generated_wild undefined]
            end
        | process ((wild, absf, guard, rhs) :: rest) =
            let
              val rest_case = process rest
              val rhs' =
                (case guard of
                   SOME g => mk_two_armed g rhs rest_case
                 | NONE => rhs)
            in
              if wild then rhs'
              else case_term [absf rhs', generated_wild rest_case]
            end
      val selector =
        if List.exists (fn (_, _, guard, _) => is_some guard) normalized
        then process normalized
        else case_term (map (fn (_, absf, _, rhs) => absf rhs) normalized)
    in mk_bind scrut (Term.lambda value selector) end

  and normalize_case_arm ctxt value (pat, env, source_guard, rhs) =
    let
      val (basic_pat, generated_guards, wrappers) =
        normalize_extended_pattern ctxt env (mk_literal value) pat
      val absf = bind_basic_case_pat ctxt env basic_pat
      val guard = fold extend_case_guard generated_guards source_guard
      val rhs' = fold_rev (fn wrap => fn body => wrap body) wrappers rhs
      val wild = (case basic_pat of BCP_Wild _ => true | _ => false)
    in (wild, absf, guard, rhs') end

  and normalize_extended_pattern ctxt env expr pat =
    (case pat of
       CP_Alias (name, pos, inner) =>
         let
           val (basic, guards, wrappers) =
             normalize_extended_pattern ctxt env expr inner
           fun wrap rhs = alias_wrapper env expr name pos rhs
         in (basic, guards, wrappers @ [wrap]) end
     | CP_Value (literal, _) =>
         (BCP_Wild NONE, [mk_bin Eq expr (mk_literal literal)], [])
     | CP_Range (kind, lo, hi, _) =>
         let
           val upper =
             mk_bin (case kind of RK_Exclusive => Lt | RK_Inclusive => Le) expr hi
         in (BCP_Wild NONE, [mk_bin And (mk_bin Ge expr lo) upper], []) end
     | CP_SliceSuffix suffix_rev =>
         let
           val reversed = mk_rev_expr expr
           val guard = mk_nested_match_guard ctxt env reversed suffix_rev
           fun wrap rhs = mk_nested_match_extract ctxt env reversed suffix_rev rhs
         in (BCP_Wild NONE, [guard], [wrap]) end
     | _ => normalize_pattern_for_nested ctxt env pat)

  and normalize_pattern_for_nested ctxt env pat =
    (case pat of
       CP_Constr (name, pos, args) =>
         let
           val (args', guards, wrappers) = normalize_args_for_nested ctxt env args
         in (BCP_Constr (name, pos, args'), guards, wrappers) end
     | CP_Resolved (ctor, args) =>
         let
           val (args', guards, wrappers) = normalize_args_for_nested ctxt env args
         in (BCP_Resolved (ctor, args'), guards, wrappers) end
     | CP_Tuple args =>
         let
           val (args', guards, wrappers) = normalize_args_for_nested ctxt env args
         in (BCP_Tuple args', guards, wrappers) end
     | _ => (normalize_basic_case_pattern pat, [], []))

  and normalize_args_for_nested _ _ [] = ([], [], [])
    | normalize_args_for_nested ctxt env (arg :: rest) =
        let
          val (arg', guards0, wrappers0) = normalize_arg_for_nested ctxt env arg
          val (rest', guards1, wrappers1) = normalize_args_for_nested ctxt env rest
        in (arg' :: rest', guards0 @ guards1, wrappers0 @ wrappers1) end

  and normalize_arg_for_nested ctxt env pat =
    if case_requires_nested pat then
      let
        val tmp = Free ("_urust_pat_" ^ string_of_int (serial ()), dummyT)
        val tmp_expr = mk_literal tmp
        val (matched_expr, matched_pat) =
          (case pat of
             CP_SliceSuffix suffix_rev => (mk_rev_expr tmp_expr, suffix_rev)
           | _ => (tmp_expr, pat))
        val guard = mk_nested_match_guard ctxt env matched_expr matched_pat
        fun wrapper rhs = mk_nested_match_extract ctxt env matched_expr matched_pat rhs
      in (BCP_Generated tmp, [guard], [wrapper]) end
    else normalize_pattern_for_nested ctxt env pat

  and mk_nested_match_guard ctxt env expr pat =
    compile_case ctxt expr
      [(pat, env, NONE, mk_literal \<^term>\<open>True\<close>),
       (CP_Wild Position.none, env, NONE, mk_literal \<^term>\<open>False\<close>)]

  and mk_nested_match_extract ctxt env expr pat rhs =
    compile_case ctxt expr
      [(pat, env, NONE, rhs),
       (CP_Wild Position.none, env, NONE,
        Const (\<^const_name>\<open>undefined\<close>, dummyT))]

  (* Recursive AST elaboration *)
  (* env : source name -> var_info for the enclosing binders (lexical scope). A bound use resolves to its
     binder's Free + nav markup and is NOT sent through dispatch -- lexical scoping wins, matching the
     frontend's witness precedence. Capture is by construction: the enclosing Term.lambda abstracts the
     `Free name` returned here, including one parsed inside a nested antiquotation. *)
  fun mk ctxt env e =
    (case e of
       UE_Num (lexeme, pos) =>
         let val (v, _) = parse_int_lit pos lexeme
         in mk_literal (HOLogic.mk_number dummyT v) end
     | UE_NumSfx (lexeme, pos) =>
         (case parse_int_lit pos lexeme of
            (v, SOME T) => mk_literal (HOLogic.mk_number T v)
          | (_, NONE) => error ("urust_expr: internal missing integer suffix" ^ Position.here pos))
     | UE_Unit _           => mk_literal HOLogic.unit
     | UE_Tuple (args, _)   => mk_tuple (map (mk ctxt env) args)
     | UE_Ident id          => mk_ident_expr ctxt env id
     | UE_Literal payload  => literal_expr ctxt env payload
     | UE_ExprAntiq src    => parse_antiq ctxt env src
     | UE_Seq (e1, e2)     => mk_sequence (mk ctxt env e1) (mk ctxt env e2)
     | UE_Bin (bop, a, b, _) => mk_bin bop (mk ctxt env a) (mk ctxt env b)
     | UE_Un (uop, a, _)     => mk_un uop (mk ctxt env a)
     | UE_Borrow (mode, a, pos) => mk_borrow mode pos (mk ctxt env a)
     | UE_Deref (a, pos)      => mk_deref pos (mk ctxt env a)
     | UE_Group (e1, _)    => mk ctxt env e1
     | UE_Block (e1, _)    => mk ctxt env e1          (* erase: alpha-equal to the frontend `{ e } = e` *)
     | UE_If (c, t, eopt, _) =>
         mk_two_armed (mk ctxt env c) (mk ctxt env t)
           (case eopt of SOME e => mk ctxt env e | NONE => mk_literal HOLogic.unit)
     | UE_Let bnd          => elab_let ctxt env bnd
     | UE_LetMut bnd       => elab_let_mut ctxt env bnd
     | UE_Const bnd        => elab_let ctxt env bnd   (* same desugaring as let today (SE:433-434) *)
     | UE_Call (name, npos, args, cpos) =>
         (* The callee resolves in NFunction context and is NOT wrapped in `literal` (a bound callee -> its
            env Free). Args are ordinary value expressions, so nested calls fall out of the recursion. *)
         let
           val func =
             (case Symtab.lookup env name of
                SOME {free, def_pos, id} => (report_ref ctxt id (name, def_pos) npos; free)
              | NONE => ident_term ctxt Micro_Rust_Names.NFunction name npos)
         in mk_const (funcall_const cpos (length args)) (func :: map (mk ctxt env) args) end
     | UE_Field (receiver, name, pos) =>
         mk_field ctxt (mk ctxt env receiver) name pos
     | UE_Propagate (expr, pos) =>
         mk_const_at \<^const_name>\<open>propagate_const\<close> pos [mk ctxt env expr]
     | UE_Assign (aop, place, rhs, pos) =>
         let
           val place' = mk_place ctxt env place
           val rhs' = mk ctxt env rhs
         in
           (case aop of
              Assign => mk_update pos place' rhs'
            | AssignAdd => mk_assign_add pos place' rhs'
            | AssignBin bop =>
                mk_update pos place'
                  (mk_bin (binop_of_assign_binop bop) (mk_deref pos place') rhs'))
         end
     | UE_Match args => elab_match ctxt env args)

  and mk_place ctxt env place =
    (case place of
       UP_Ident id => mk_ident_expr ctxt env id
     | UP_Deref (expr, _) => mk ctxt env expr
     | UP_Field (base, name, pos) =>
         mk_field ctxt (mk_place ctxt env base) name pos
     | UP_Antiq src => parse_antiq ctxt env src)

  (* `let`/`const` <pat> = rhs; body -> bind rhs (<pat-abstraction> body); shared by both nodes. *)
  and elab_let ctxt env (pat, rhs, body) =
    let
      val rhs'         = mk ctxt env rhs        (* rhs is in the OUTER scope (pat not yet visible) *)
      val (absf, env') = bind_pat ctxt env pat  (* register pattern vars; get body abstraction *)
      val body'        = mk ctxt env' body      (* innermost binding wins -> shadowing-correct *)
    in mk_bind rhs' (absf body') end

  (* Scalar mutable bindings allocate one store reference. The frontend drops `mut` from a top-level
     tuple destructure, so that case deliberately reuses immutable-let lowering. No mutability metadata
     is needed in the lexical environment: every later use denotes the allocated reference value. *)
  and elab_let_mut ctxt env (pat, rhs, body, mut_pos) =
    let
      fun allocate () =
        let
          val rhs' = mk_ref_new mut_pos (mk ctxt env rhs)
          val (absf, env') = bind_pat ctxt env pat
        in mk_bind rhs' (absf (mk ctxt env' body)) end
    in
      (case pat of
         P_Ident _ => allocate ()
       | P_Wild _ => allocate ()
       | P_Tuple _ => elab_let ctxt env (pat, rhs, body)
       | _ =>
           error ("urust_expr: invalid mutable binding pattern" ^
             " (expected identifier, `_`, or top-level tuple destructuring)" ^
             Position.here (pat_pos pat)))
    end

  (* ONE match entry point. Switch lowering remains first-order and unchanged; case lowering expands each
     disjunctive alternative into an independent arm before entering the staged compiler below. *)
  and elab_match ctxt env (flavour, scrut, arms, pos) =
    let
      val selected = (case flavour of MF_Auto => classify_match arms pos | explicit => explicit)
      fun guarded_pos [] = NONE
        | guarded_pos (UR_Arm (_, SOME (_, gpos), _) :: _) = SOME gpos
        | guarded_pos (_ :: rest) = guarded_pos rest
      val _ =
        (case (selected, guarded_pos arms) of
           (MF_Switch, SOME gpos) =>
             error ("urust_expr: guards are not supported in explicit `match_switch`" ^
                    Position.here gpos)
         | _ => ())
      val scrut' = mk ctxt env scrut
    in
      (case selected of
         MF_Switch =>
           let
             fun key pat =
               (case strip_group_pat pat of
                  P_Lit (lexeme, p) =>
                   let val (n, _) = parse_int_lit p lexeme
                   in mk_some (HOLogic.mk_number dummyT n) end
                | P_Wild p => (report_wildcard ctxt p; mk_none)
                | P_Ident (name, p) =>
                   error ("urust_expr: unsupported match_switch key " ^ quote name ^
                          " (numeral or `_` only; const-id / path keys not yet supported)" ^
                          Position.here p)
                | unsupported =>
                   error ("urust_expr: unsupported match_switch pattern" ^
                          " (numeral, `_`, or an or-list of those; binding patterns need" ^
                          " `match_case`)" ^ Position.here (pat_pos unsupported)))
             fun switch_alts (P_Or (ps, _)) = maps switch_alts ps
               | switch_alts (P_Group p) = switch_alts p
               | switch_alts p = [p]
             fun arm_pairs (UR_Arm (pat, NONE, body)) =
                   let val body' = mk ctxt env body
                   in map (fn p => mk_pair (key p) body') (switch_alts pat)
                   end
               | arm_pairs (UR_Arm (_, SOME (_, gpos), _)) =
                   error ("urust_expr: guards are not supported in explicit `match_switch`" ^
                          Position.here gpos)
             val pairs = maps arm_pairs arms
           in mk_bind scrut' (mk_ncase_selector (fold_rev mk_cons pairs mk_nil)) end
       | MF_Case =>
           let
             fun expand_arm (UR_Arm (pat, guard, body)) =
               map (fn pat' =>
                 let
                   val env' = bind_case_vars ctxt pat' env
                   val pat'' = prepare_case_pattern ctxt env' pat'
                   val guard' = Option.map (fn (g, _) => mk ctxt env' g) guard
                   val body' = mk ctxt env' body
                 in (pat'', env', guard', body') end)
                 (expand_case_pat pat)
           in compile_case ctxt scrut' (maps expand_arm arms) end
       | MF_Auto => error "urust_expr: internal unresolved auto match flavour")
    end

  (* Public entry point *)
  fun mk_closed ctxt = mk ctxt Symtab.empty
end
\<close>

end
