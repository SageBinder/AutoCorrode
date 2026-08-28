theory Micro_Rust_Resolution
  imports
    Micro_Rust_Elab_Terms
    Parser_Utils
begin

section\<open> Names, binders, and metadata \<close>

ML\<open>
signature URUST_RESOLUTION =
sig
  type environment

  val empty_environment: environment
  val bind_local:
    Proof.context -> environment -> string * Position.T -> term * environment
  val use_local:
    Proof.context -> environment -> string * Position.T -> term option
  val lookup_local: environment -> string -> term option
  val parse_antiquotation: Proof.context -> environment -> Input.source -> term
  val anonymous_abstraction: term -> term

  val report_wildcard: Proof.context -> Position.T -> unit
  val literal_position: URust_AST.literal_payload -> Position.T
  val literal_value:
    Proof.context -> environment -> URust_AST.literal_payload -> term
  val literal_expression:
    Proof.context -> environment -> URust_AST.literal_payload -> term
  val literal_identifier:
    Proof.context -> environment -> string * Position.T -> term
  val function_identifier:
    Proof.context -> environment -> string * Position.T -> term
  val field_expression:
    Proof.context -> term -> string -> Position.T -> term

  val resolve_constructor: Proof.context -> string -> term option
  val report_constructor: Proof.context -> Position.T -> term -> unit

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        term * (term * Position.T option * URust_AST.ur_pat) list
    | Resolved_Record_Struct of
        string * (term * Position.T option * URust_AST.ur_pat) list

  val resolve_struct_pattern:
    Proof.context ->
      string * Position.T * URust_AST.struct_field list ->
      resolved_struct_pattern
  val unsupported_record_pattern: string -> Position.T -> 'a
end
\<close>

text\<open>
Resolution owns every effectful name operation: binder IDs and navigation, local shadowing,
antiquotation capture, notation dispatch, constructor reports, and struct metadata. Its environment is
abstract so downstream modules cannot depend on the underlying binder record.
\<close>

ML\<open>
structure URust_Resolution : URUST_RESOLUTION =
struct
  open URust_AST
  structure T = URust_Elab_Terms

  type environment = Parser_Utils.var_info Symtab.table

  val variable_entity_kind = "urust_var"
  val report_reference = Parser_Utils.report_ref variable_entity_kind
  val bind_variable = Parser_Utils.bind_var variable_entity_kind
  val parse_bound_antiquotation = Parser_Utils.parse_antiq variable_entity_kind

  val empty_environment = Symtab.empty
  val anonymous_abstraction = Parser_Utils.anon_abs

  fun bind_local ctxt environment binding =
    bind_variable ctxt environment binding

  fun use_local ctxt environment (name, pos) =
    (case Symtab.lookup environment name of
       SOME {free, def_pos, id} =>
         (report_reference ctxt id (name, def_pos) pos; SOME free)
     | NONE => NONE)

  fun lookup_local environment name =
    Option.map #free (Symtab.lookup environment name)

  fun parse_antiquotation ctxt environment source =
    parse_bound_antiquotation ctxt environment source

  (* Syntax.parse_term wraps resolved constants in an internal type constraint. This helper is used only
     for markup; the returned identifier term retains the wrapper for the final check_term. *)
  fun identifier_leaf term =
    (case Term_Position.strip_positions term of
       Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ inner =>
         identifier_leaf inner
     | inner => inner)

  (* Registered notation witnesses must remain bare Frees until the enclosing Term.lambda can capture
     them. This is the witness-precedence rule that lets a lexical binder shadow a notation. *)
  fun resolve_identifier ctxt kind name pos =
    (case Micro_Rust_Names.lookups ctxt kind name of
       [] =>
         let val term = Syntax.parse_term ctxt name in
           (case identifier_leaf term of
              Const (constant_name, _) =>
                Context_Position.report ctxt pos
                  (Name_Space.markup
                    (Consts.space_of (Proof_Context.consts_of ctxt)) constant_name)
            | Free (free_name, _) =>
                (case Proof_Context.lookup_free ctxt free_name of
                   SOME fixed =>
                     List.app (Context_Position.report ctxt pos)
                       (Syntax_Phases.markup_free ctxt fixed)
                 | NONE => Context_Position.report ctxt pos Markup.free)
            | _ => Context_Position.report ctxt pos Markup.free);
           term
         end
     | _ => Micro_Rust_Dispatch.mk_marker kind name pos (Free (name, dummyT)))

  fun literal_identifier ctxt environment (identifier as (name, pos)) =
    (case use_local ctxt environment identifier of
       SOME local_term => T.literal local_term
     | NONE =>
         T.literal (resolve_identifier ctxt Micro_Rust_Names.NLiteral name pos))

  fun function_identifier ctxt environment (identifier as (name, pos)) =
    (case use_local ctxt environment identifier of
       SOME local_term => local_term
     | NONE => resolve_identifier ctxt Micro_Rust_Names.NFunction name pos)

  fun field_expression ctxt receiver name pos =
    T.focus_field
      (resolve_identifier ctxt Micro_Rust_Names.NField name pos)
      receiver

  fun resolve_constructor ctxt name =
    let val theory = Proof_Context.theory_of ctxt in
      (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
         SOME (Const (full_name, _)) =>
           if Code.is_constr theory full_name
           then SOME (Const (full_name, dummyT))
           else NONE
       | _ => NONE)
    end

  fun report_constructor ctxt pos (Const (name, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) name)
    | report_constructor _ _ _ = ()

  fun report_wildcard ctxt pos =
    Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

  fun literal_position (LP_Bool (_, pos)) = pos
    | literal_position (LP_String (_, pos)) = pos
    | literal_position (LP_ValAntiq source) = Input.pos_of source

  fun literal_value ctxt environment payload =
    (case payload of
       LP_Bool (value, _) => if value then T.true_value else T.false_value
     | LP_String (raw, pos) => T.string_value raw pos
     | LP_ValAntiq source => parse_antiquotation ctxt environment source)

  fun literal_expression _ _ (LP_Bool (value, _)) =
        T.boolean_expression value
    | literal_expression ctxt environment payload =
        T.literal (literal_value ctxt environment payload)

  fun canonical_name name = Long_Name.base_name name
  fun name_matches left right =
    left = right orelse canonical_name left = canonical_name right

  fun term_name_of (Const (name, _)) = SOME name
    | term_name_of (Free (name, _)) = SOME name
    | term_name_of _ = NONE

  fun type_name_of (Type (name, _)) = SOME name
    | type_name_of _ = NONE

  datatype struct_candidate =
      Constructor_Candidate of {ctor: term, selectors: term list}
    | Record_Candidate of {record_name: string, fields: term list}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        term * (term * Position.T option * ur_pat) list
    | Resolved_Record_Struct of
        string * (term * Position.T option * ur_pat) list

  (* Struct heads accept either a constructor name or the type name of a single-constructor datatype.
     Records come only from Record.get_info; Ctr_Sugar's record entry belongs to a different lowering
     domain and must not compete with constructor candidates. *)
  fun resolve_struct_constructor ctxt (identifier_name, pos) =
    let
      val base_identifier = canonical_name identifier_name
      val theory = Proof_Context.theory_of ctxt
      val sugars = Ctr_Sugar.ctr_sugars_of ctxt

      fun named_constant role term =
        (case term_name_of term of
           SOME name => Const (name, dummyT)
         | NONE =>
             error ("urust_expr: unnamed " ^ role ^ " in constructor metadata" ^
               Position.here pos))

      fun constructor_candidate constructor_name selectors =
        Constructor_Candidate
          {ctor = Const (constructor_name, dummyT),
           selectors = map (named_constant "selector") selectors}

      fun from_sugar ({kind = Ctr_Sugar.Record, ...} : Ctr_Sugar.ctr_sugar) = []
        | from_sugar ({T, ctrs, selss, ...} : Ctr_Sugar.ctr_sugar) =
        let
          val type_name = Option.map canonical_name (type_name_of T)
          (* Old_Datatype uses an empty outer selector list; otherwise rows align with constructors. *)
          val entries =
            if null selss then map (fn constructor => (constructor, [])) ctrs
            else if length ctrs = length selss then ListPair.zip (ctrs, selss)
            else
              error ("urust_expr: inconsistent constructor/selector metadata for " ^
                quote (the_default identifier_name (type_name_of T)) ^ Position.here pos)
          val direct =
            map_filter (fn (constructor, selectors) =>
              (case term_name_of constructor of
                 SOME constructor_name =>
                   if name_matches constructor_name base_identifier
                   then
                     SOME
                       (constructor_name,
                        constructor_candidate constructor_name selectors)
                   else NONE
               | NONE => NONE)) entries
          val fallback =
            (case (type_name, entries) of
               (SOME candidate_type, [(constructor, selectors)]) =>
                 if candidate_type = base_identifier
                 then
                   (case term_name_of constructor of
                      SOME constructor_name =>
                        [(constructor_name,
                          constructor_candidate constructor_name selectors)]
                    | NONE => [])
                 else []
             | _ => [])
        in direct @ fallback end

      fun record_candidate record_name =
        let
          val resolved_name =
            (type_name_of
               (Proof_Context.read_type_name
                 {proper = true, strict = false} ctxt record_name)
              handle ERROR _ => NONE)
          val (canonical_record_name, info) =
            (case resolved_name of
               SOME name => (name, Record.get_info theory name)
             | NONE => (record_name, Record.get_info theory record_name))
        in
          (case info of
             NONE => NONE
           | SOME record_info =>
               SOME
                 (canonical_record_name,
                  Record_Candidate
                    {record_name = canonical_record_name,
                     fields =
                       map (fn (field, _) => Const (field, dummyT))
                         (#fields record_info)}))
        end

      fun same_candidate
          (Constructor_Candidate {ctor = left_ctor, selectors = left_selectors},
           Constructor_Candidate {ctor = right_ctor, selectors = right_selectors}) =
            left_ctor aconv right_ctor andalso
              eq_list (op aconv) (left_selectors, right_selectors)
        | same_candidate
          (Record_Candidate {record_name = left_name, fields = left_fields},
           Record_Candidate {record_name = right_name, fields = right_fields}) =
            left_name = right_name andalso
              eq_list (op aconv) (left_fields, right_fields)
        | same_candidate _ = false

      fun candidate_description (Constructor_Candidate {ctor, selectors}) =
            "constructor " ^ quote (the_default "<unnamed>" (term_name_of ctor)) ^
              " with selectors [" ^
              space_implode ", "
                (map (the_default "<unnamed>" o term_name_of) selectors) ^ "]"
        | candidate_description (Record_Candidate {record_name, fields}) =
            "record " ^ quote record_name ^ " with fields [" ^
              space_implode ", "
                (map (the_default "<unnamed>" o term_name_of) fields) ^ "]"

      fun candidate_key (Constructor_Candidate {ctor, ...}) =
            "C:" ^ the_default "<unnamed>" (term_name_of ctor)
        | candidate_key (Record_Candidate {record_name, ...}) =
            "R:" ^ record_name

      fun add_candidate (display_name, candidate) candidates =
        let val key = candidate_key candidate in
          (case Symtab.lookup candidates key of
             NONE => Symtab.update (key, (display_name, candidate)) candidates
           | SOME (_, existing) =>
               if same_candidate (existing, candidate) then candidates
               else
                 error ("urust_expr: inconsistent struct metadata for " ^
                   quote display_name ^ ": " ^ candidate_description existing ^
                   " versus " ^ candidate_description candidate ^ Position.here pos))
        end

      val record_candidates =
        map_filter record_candidate
          (distinct (op =) [identifier_name, base_identifier])
      val candidates =
        fold add_candidate (maps from_sugar sugars @ record_candidates) Symtab.empty
        |> Symtab.dest
        |> map snd
    in
      (case candidates of
         [] =>
           error ("urust_expr: struct pattern " ^ quote identifier_name ^
             ": no matching constructor or single-constructor record/datatype found" ^
             Position.here pos)
       | [(_, candidate)] => candidate
       | _ =>
           error ("urust_expr: struct pattern " ^ quote identifier_name ^
             " is ambiguous; candidates: " ^
             space_implode ", " (map fst candidates) ^ Position.here pos))
    end

  fun resolve_struct_pattern ctxt (head, head_pos, fields) =
    let
      val candidate = resolve_struct_constructor ctxt (head, head_pos)
      val (display_name, selectors) =
        (case candidate of
           Constructor_Candidate {ctor, selectors} =>
             (the_default head (Option.map canonical_name (term_name_of ctor)),
              selectors)
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

      fun add_field (name, pos, pattern) (entries, rest_pos) =
        let val field = canonical_name name in
          (case AList.lookup (op =) entries field of
             SOME _ =>
               error ("urust_expr: struct pattern for " ^ quote display_name ^
                 " has duplicate field " ^ quote field ^ Position.here pos)
           | NONE => ((field, (pos, pattern)) :: entries, rest_pos))
        end

      fun collect (SF_Field (name, pos, pattern)) state =
            add_field (name, pos, pattern) state
        | collect (SF_Shorthand (name, pos)) state =
            add_field (name, pos, P_Ident (name, pos)) state
        | collect (SF_Rest pos) (entries, NONE) =
            (entries, SOME pos)
        | collect (SF_Rest pos) (_, SOME _) =
            error ("urust_expr: struct pattern has multiple `..` rest entries" ^
              Position.here pos)

      val (entries_rev, rest_pos) = fold collect fields ([], NONE)
      val entries = rev entries_rev
      val unknown =
        get_first (fn (name, (pos, _)) =>
          if member (op =) selector_names name
          then NONE
          else SOME (name, pos)) entries
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
        else
          error ("urust_expr: struct pattern for " ^ quote display_name ^
            " is missing field(s): " ^ space_implode ", " missing ^
            Position.here head_pos)
      val ordered =
        map (fn (name, selector) =>
          (case AList.lookup (op =) entries name of
             SOME (pos, pattern) => (selector, SOME pos, pattern)
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
end
\<close>

end
