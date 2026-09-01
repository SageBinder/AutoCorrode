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
  datatype binding_mode = Binding_By_Value
  type binding_signature = string * Position.T * binding_mode

  val empty_environment: environment
  val bind_local:
    Proof.context -> environment -> string * Position.T -> term * environment
  val allocate_locals:
    Proof.context -> environment -> binding_signature list -> environment
  val use_local:
    Proof.context -> environment -> string * Position.T -> term option
  val lookup_local: environment -> string -> term option
  val parse_antiquotation: Proof.context -> environment -> Input.source -> term
  val anonymous_abstraction: term -> term

  val report_wildcard: Proof.context -> Position.T -> unit
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

  type constructor_info
  val resolve_constructor: Proof.context -> string -> constructor_info option
  val constructor_term: constructor_info -> term
  val constructor_arity: constructor_info -> int
  val constructor_family: constructor_info -> (string * term list) option
  val report_constructor: Proof.context -> Position.T -> constructor_info -> unit
  val report_selector: Proof.context -> Position.T -> term -> unit

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info * (term * Position.T option * URust_AST.ur_pat) list
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
  datatype binding_mode = Binding_By_Value
  type binding_signature = string * Position.T * binding_mode

  val variable_entity_kind = "urust_var"
  val report_reference = Parser_Utils.report_ref variable_entity_kind
  val bind_local = Parser_Utils.bind_var variable_entity_kind
  val parse_antiquotation = Parser_Utils.parse_antiq variable_entity_kind

  val empty_environment = Symtab.empty
  val anonymous_abstraction = Parser_Utils.anon_abs

  fun allocate_locals ctxt environment signatures =
    let
      fun validate (name, pos, _) seen =
        (case Symtab.lookup seen name of
           NONE => Symtab.update (name, pos) seen
         | SOME original_pos =>
             error ("urust_expr: duplicate pattern binder " ^ quote name ^
               Position.here pos ^ "\nThe original binder is here" ^
               Position.here original_pos))
      val _ = fold validate signatures Symtab.empty
      fun allocate (name, pos, _) env = #2 (bind_local ctxt env (name, pos))
    in fold allocate signatures environment end

  fun use_local ctxt environment (name, pos) =
    (case Symtab.lookup environment name of
       SOME {free, def_pos, id} =>
         (report_reference ctxt id (name, def_pos) pos; SOME free)
     | NONE => NONE)

  fun lookup_local environment name =
    Option.map #free (Symtab.lookup environment name)

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

  type constructor_info =
    {constructor: term, arity: int, family: (string * term list) option}

  fun constructor_term ({constructor, ...} : constructor_info) = constructor
  fun constructor_arity ({arity, ...} : constructor_info) = arity
  fun constructor_family ({family, ...} : constructor_info) = family

  fun term_name_of (Const (name, _)) = SOME name
    | term_name_of (Free (name, _)) = SOME name
    | term_name_of _ = NONE

  fun type_name_of (Type (name, _)) = SOME name
    | type_name_of _ = NONE

  fun normalize_constructor (Const (name, _)) = Const (name, dummyT)
    | normalize_constructor term = term

  fun family_of_constructor ctxt constructor_name =
    let
      fun family
          ({kind = Ctr_Sugar.Record, ...} : Ctr_Sugar.ctr_sugar) = NONE
        | family ({T, ctrs, ...} : Ctr_Sugar.ctr_sugar) =
            if List.exists
                (fn constructor =>
                  term_name_of constructor = SOME constructor_name) ctrs
            then
              Option.map
                (fn type_name =>
                  (type_name, map normalize_constructor ctrs))
                (type_name_of T)
            else NONE
    in get_first family (Ctr_Sugar.ctr_sugars_of ctxt) end

  fun make_constructor_info ctxt constructor =
    (case constructor of
       Const (name, typ) =>
         {constructor = Const (name, dummyT),
          arity = length (binder_types typ),
          family = family_of_constructor ctxt name}
     | _ => error "urust_expr: internal unnamed constructor")

  fun resolve_constructor ctxt name =
    let val theory = Proof_Context.theory_of ctxt in
      (case try (Proof_Context.read_const {proper = true, strict = false} ctxt) name of
         SOME (constructor as Const (full_name, _)) =>
           if Code.is_constr theory full_name
           then SOME (make_constructor_info ctxt constructor)
           else NONE
       | _ => NONE)
    end

  fun report_named_term ctxt pos (Const (name, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) name)
    | report_named_term _ _ _ = ()

  fun report_constructor ctxt pos info =
    report_named_term ctxt pos (constructor_term info)

  val report_selector = report_named_term

  fun report_wildcard ctxt pos =
    Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

  fun literal_value ctxt environment payload =
    (case payload of
       LP_Integer (lexeme, pos) => T.integer_value pos lexeme
     | LP_Bool (value, _) => if value then T.true_value else T.false_value
     | LP_String (raw, pos) => T.string_value raw pos
     | LP_ValAntiq source => parse_antiquotation ctxt environment source)

  fun literal_expression _ _ (LP_Bool (value, _)) =
        T.boolean_expression value
    | literal_expression ctxt environment payload =
        T.literal (literal_value ctxt environment payload)

  val canonical_name = Long_Name.base_name
  fun name_matches left right =
    left = right orelse canonical_name left = canonical_name right

  datatype struct_candidate =
      Constructor_Candidate of {info: constructor_info, selectors: term list}
    | Record_Candidate of {record_name: string, fields: term list}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info * (term * Position.T option * ur_pat) list
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

      fun constructor_candidate constructor selectors =
        Constructor_Candidate
          {info = make_constructor_info ctxt constructor,
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
                        constructor_candidate constructor selectors)
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
                          constructor_candidate constructor selectors)]
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
          (Constructor_Candidate {info = left_info, selectors = left_selectors},
           Constructor_Candidate {info = right_info, selectors = right_selectors}) =
            constructor_term left_info aconv constructor_term right_info andalso
              eq_list (op aconv) (left_selectors, right_selectors)
        | same_candidate
          (Record_Candidate {record_name = left_name, fields = left_fields},
           Record_Candidate {record_name = right_name, fields = right_fields}) =
            left_name = right_name andalso
              eq_list (op aconv) (left_fields, right_fields)
        | same_candidate _ = false

      fun candidate_description (Constructor_Candidate {info, selectors}) =
            "constructor " ^
              quote (the_default "<unnamed>"
                (term_name_of (constructor_term info))) ^
              " with selectors [" ^
              space_implode ", "
                (map (the_default "<unnamed>" o term_name_of) selectors) ^ "]"
        | candidate_description (Record_Candidate {record_name, fields}) =
            "record " ^ quote record_name ^ " with fields [" ^
              space_implode ", "
                (map (the_default "<unnamed>" o term_name_of) fields) ^ "]"

      fun candidate_key (Constructor_Candidate {info, ...}) =
            "C:" ^ the_default "<unnamed>"
              (term_name_of (constructor_term info))
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
           Constructor_Candidate {info, selectors} =>
             (the_default head
                (Option.map canonical_name
                  (term_name_of (constructor_term info))),
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
         Constructor_Candidate {info, ...} =>
           Resolved_Constructor_Struct (info, ordered)
       | Record_Candidate {record_name, ...} =>
           Resolved_Record_Struct (record_name, ordered))
    end

  fun unsupported_record_pattern record_name pos =
    error ("urust_expr: HOL record pattern " ^ quote (canonical_name record_name) ^
      " requires selector-based lowering" ^ Position.here pos)
end
\<close>

end
