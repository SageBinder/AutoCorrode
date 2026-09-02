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
  type constructor_resolver
  val make_constructor_resolver:
    Proof.context -> Position.T -> constructor_resolver
  val resolve_constructor:
    constructor_resolver ->
      string * Position.T -> constructor_info option
  val constructor_identity: constructor_info -> string
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
    Proof.context -> constructor_resolver ->
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

  fun term_name_of (Const (name, _)) = SOME name
    | term_name_of (Free (name, _)) = SOME name
    | term_name_of _ = NONE

  fun type_name_of (Type (name, _)) = SOME name
    | type_name_of _ = NONE

  fun normalize_constructor (Const (name, _)) = Const (name, dummyT)
    | normalize_constructor term = term

  type constructor_info =
    {identity: string,
     constructor: term,
     arity: int,
     family: (string * term list) option,
     selectors: term list}

  datatype constructor_resolver =
    Constructor_Resolver of
      {by_identity: constructor_info Symtab.table,
       by_basename: constructor_info list Symtab.table,
       type_fallbacks: (string * constructor_info) list,
       record_types: string list}

  fun constructor_identity
      ({identity, ...} : constructor_info) = identity
  fun constructor_term
      ({constructor, ...} : constructor_info) = constructor
  fun constructor_arity
      ({arity, ...} : constructor_info) = arity
  fun constructor_family
      ({family, ...} : constructor_info) = family
  fun constructor_selectors
      ({selectors, ...} : constructor_info) = selectors

  val canonical_name = Long_Name.base_name

  fun qualified_name name =
    String.isSubstring Long_Name.separator name

  fun named_constant role pos term =
    (case term_name_of term of
       SOME name => Const (name, dummyT)
     | NONE =>
         error ("urust_expr: unnamed " ^ role ^
           " in constructor metadata" ^ Position.here pos))

  fun same_family (NONE, NONE) = true
    | same_family
        (SOME (left_name, left_members),
         SOME (right_name, right_members)) =
        left_name = right_name andalso
          eq_list (op aconv) (left_members, right_members)
    | same_family _ = false

  fun same_constructor_info
      (left : constructor_info, right : constructor_info) =
    #identity left = #identity right andalso
      #constructor left aconv #constructor right andalso
      #arity left = #arity right andalso
      same_family (#family left, #family right) andalso
      eq_list (op aconv) (#selectors left, #selectors right)

  fun merge_optional_family identity (NONE, family) = family
    | merge_optional_family _ (family, NONE) = family
    | merge_optional_family identity
        (left as SOME _, right as SOME _) =
        if same_family (left, right)
        then left
        else
          error
            ("urust_expr: inconsistent constructor family metadata for " ^
              quote identity)

  fun merge_selectors identity arity left right =
    if eq_list (op aconv) (left, right)
    then left
    else if null left andalso arity > 0
    then right
    else if null right andalso arity > 0
    then left
    else
      error
        ("urust_expr: inconsistent constructor selector metadata for " ^
          quote identity)

  fun merge_constructor_info pos
      (left : constructor_info, right : constructor_info) =
    let
      val identity = #identity left
      val _ =
        if identity = #identity right andalso
            #constructor left aconv #constructor right andalso
            #arity left = #arity right
        then ()
        else
          error
            ("urust_expr: inconsistent constructor core metadata for " ^
              quote identity ^ Position.here pos)
    in
      {identity = identity,
       constructor = #constructor left,
       arity = #arity left,
       family =
         merge_optional_family identity
           (#family left, #family right),
       selectors =
         merge_selectors identity (#arity left)
           (#selectors left) (#selectors right)}
    end

  fun describe_constructor_info (info : constructor_info) =
    "constructor " ^ quote (#identity info) ^
      " (arity " ^ string_of_int (#arity info) ^
      ", selectors [" ^
      space_implode ", "
        (map (the_default "<unnamed>" o term_name_of)
          (#selectors info)) ^ "])"

  fun make_constructor_resolver ctxt pos =
    let
      val theory = Proof_Context.theory_of ctxt
      val sugars = Ctr_Sugar.ctr_sugars_of ctxt

      fun selector_rows type_name ctrs selss =
        if null selss
        then map (fn constructor => (constructor, [])) ctrs
        else if length ctrs = length selss
        then ListPair.zip (ctrs, selss)
        else
          error
            ("urust_expr: inconsistent constructor/selector metadata for " ^
              quote type_name ^ Position.here pos)

      fun catalog_entries
          ({kind = Ctr_Sugar.Record, ...} :
            Ctr_Sugar.ctr_sugar) = []
        | catalog_entries
            ({T, ctrs, selss, ...} :
              Ctr_Sugar.ctr_sugar) =
            let
              val type_name = type_name_of T
              val display_name =
                the_default
                  (case map_filter term_name_of ctrs of
                     first :: _ => first
                   | [] => "<unnamed>")
                  type_name
              val family_members =
                map (named_constant "constructor" pos) ctrs
              val family =
                Option.map
                  (fn name => (name, family_members))
                  type_name

              fun entry (constructor, selectors) =
                (case constructor of
                   Const (identity, typ) =>
                     if Code.is_constr theory identity
                     then
                       let
                         val normalized_selectors =
                           map (named_constant "selector" pos)
                             selectors
                         val arity = length (binder_types typ)
                         val _ =
                           if null normalized_selectors orelse
                               length normalized_selectors = arity
                           then ()
                           else
                             error
                               ("urust_expr: inconsistent selector arity for " ^
                                 quote identity ^ Position.here pos)
                       in
                         SOME
                           {identity = identity,
                            constructor = Const (identity, dummyT),
                            arity = arity,
                            family = family,
                            selectors = normalized_selectors}
                       end
                     else NONE
                 | _ =>
                     error
                       ("urust_expr: unnamed constructor in family " ^
                         quote display_name ^ Position.here pos))
            in
              map_filter entry
                (selector_rows display_name ctrs selss)
            end

      fun add_entry info table =
        let val identity = constructor_identity info in
          (case Symtab.lookup table identity of
             NONE => Symtab.update (identity, info) table
           | SOME existing =>
               Symtab.update
                 (identity,
                  merge_constructor_info pos
                    (existing, info))
                 table)
        end

      val by_identity =
        fold add_entry (maps catalog_entries sugars) Symtab.empty

      fun add_basename info =
        Symtab.map_default
          (canonical_name (constructor_identity info), [])
          (insert (fn (left, right) =>
            constructor_identity left =
              constructor_identity right) info)

      val by_basename =
        fold add_basename (map #2 (Symtab.dest by_identity))
          Symtab.empty

      val type_fallbacks =
        map_filter
          (fn info =>
            (case constructor_family info of
               SOME (type_name, [_]) =>
                 SOME (type_name, info)
             | _ => NONE))
          (map #2 (Symtab.dest by_identity))

      val record_types =
        Name_Space.get_names (Sign.type_space theory)
        |> filter (is_some o Record.get_info theory)
        |> sort_strings
    in
      Constructor_Resolver
        {by_identity = by_identity,
         by_basename = by_basename,
         type_fallbacks = type_fallbacks,
         record_types = record_types}
    end

  fun constructor_candidates
      (Constructor_Resolver
        {by_identity, by_basename, ...}) name =
    if qualified_name name
    then
      (case Symtab.lookup by_identity name of
         SOME info => [info]
       | NONE => [])
    else
      the_default [] (Symtab.lookup by_basename name)

  fun ambiguity_error role name pos candidates =
    error
      ("urust_expr: " ^ role ^ " " ^ quote name ^
        " is ambiguous; candidates: " ^
        space_implode ", "
          (sort_strings
            (map constructor_identity candidates)) ^
        Position.here pos)

  fun resolve_constructor resolver (name, pos) =
    (case constructor_candidates resolver name of
       [] => NONE
     | [info] => SOME info
     | candidates =>
         ambiguity_error "constructor pattern" name pos
           candidates)

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
  fun resolve_struct_constructor ctxt
      (resolver as
        Constructor_Resolver
          {type_fallbacks, record_types, ...})
      (identifier_name, pos) =
    let
      val theory = Proof_Context.theory_of ctxt

      fun name_matches identity =
        if qualified_name identifier_name
        then identity = identifier_name
        else canonical_name identity = identifier_name

      val direct_candidates =
        map
          (fn info =>
            (constructor_identity info,
             Constructor_Candidate
               {info = info,
                selectors = constructor_selectors info}))
          (constructor_candidates resolver identifier_name)

      val fallback_candidates =
        type_fallbacks
        |> map_filter
          (fn (type_name, info) =>
            if name_matches type_name
            then
              SOME
                (constructor_identity info,
                 Constructor_Candidate
                   {info = info,
                    selectors = constructor_selectors info})
            else NONE)

      fun record_candidate record_name =
        (case Record.get_info theory record_name of
           NONE =>
             error
               ("urust_expr: missing record metadata for " ^
                 quote record_name ^ Position.here pos)
         | SOME record_info =>
             (record_name,
              Record_Candidate
                {record_name = record_name,
                 fields =
                   map (fn (field, _) =>
                     Const (field, dummyT))
                     (#fields record_info)}))

      val record_candidates =
        record_types
        |> filter name_matches
        |> map record_candidate

      fun same_candidate
          (Constructor_Candidate
             {info = left_info, selectors = left_selectors},
           Constructor_Candidate
             {info = right_info, selectors = right_selectors}) =
            same_constructor_info (left_info, right_info) andalso
              eq_list (op aconv)
                (left_selectors, right_selectors)
        | same_candidate
            (Record_Candidate
               {record_name = left_name, fields = left_fields},
             Record_Candidate
               {record_name = right_name, fields = right_fields}) =
            left_name = right_name andalso
              eq_list (op aconv) (left_fields, right_fields)
        | same_candidate _ = false

      fun candidate_description
          (Constructor_Candidate {info, ...}) =
            describe_constructor_info info
        | candidate_description
            (Record_Candidate {record_name, fields}) =
            "record " ^ quote record_name ^ " with fields [" ^
              space_implode ", "
                (map
                  (the_default "<unnamed>" o term_name_of)
                  fields) ^ "]"

      fun candidate_key
          (Constructor_Candidate {info, ...}) =
            "C:" ^ constructor_identity info
        | candidate_key
            (Record_Candidate {record_name, ...}) =
            "R:" ^ record_name

      fun add_candidate (display_name, candidate) candidates =
        let val key = candidate_key candidate in
          (case Symtab.lookup candidates key of
             NONE =>
               Symtab.update
                 (key, (display_name, candidate)) candidates
           | SOME (_, existing) =>
               if same_candidate (existing, candidate)
               then candidates
               else
                 error
                   ("urust_expr: inconsistent struct metadata for " ^
                     quote display_name ^ ": " ^
                     candidate_description existing ^ " versus " ^
                     candidate_description candidate ^
                     Position.here pos))
        end

      val candidates =
        fold add_candidate
          (direct_candidates @ fallback_candidates @
            record_candidates)
          Symtab.empty
        |> Symtab.dest
        |> map snd
        |> sort_by fst
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
             space_implode ", " (map fst candidates) ^
             Position.here pos))
    end

  fun resolve_struct_pattern ctxt resolver
      (head, head_pos, fields) =
    let
      val candidate =
        resolve_struct_constructor ctxt resolver
          (head, head_pos)
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
