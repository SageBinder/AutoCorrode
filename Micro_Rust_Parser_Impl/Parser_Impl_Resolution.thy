theory Parser_Impl_Resolution
  imports
    Parser_Impl_Shallow_Terms
    Parser_Impl_Item_Scope
    Parser_Utils
begin

section\<open> Names, binders, and metadata \<close>

ML\<open>
signature URUST_RESOLUTION =
sig
  type environment

  datatype value_category =
      Ordinary_Value
    | Reference_Value
    | Auto_Deref_Eligible

  val empty_environment: environment
  val allocate_locals:
    value_category ->
    Proof.context ->
      environment ->
      (string * Position.T) list ->
      environment
  val allocate_closure_formals:
    Proof.context ->
      environment ->
      (string * Position.T) list ->
      term list * environment
  val allocate_expression_arguments:
    Proof.context ->
      environment ->
      ((string * Position.T) * typ) list ->
      (term -> term) list * environment
  val allocate_function_parameters:
    Proof.context ->
      environment ->
      ((string * Position.T) * typ) list ->
      (term -> term) list * environment
  val use_local:
    Proof.context -> environment -> string * Position.T -> term option
  val use_local_with_category:
    Proof.context -> environment -> string * Position.T ->
      (term * value_category) option
  val lookup_local: environment -> string -> term option
  val parse_antiquotation: Proof.context -> environment -> Input.source -> term
  val anonymous_abstraction: term -> term

  val report_wildcard: Proof.context -> Position.T -> unit
  val report_struct_label:
    Proof.context -> string * Position.T -> unit
  val report_struct_labels:
    Proof.context -> URust_AST.ur_path ->
      URust_AST.struct_expr_field list -> unit
  val literal_value:
    Proof.context -> environment -> URust_AST.literal_payload -> term
  val literal_expression:
    Proof.context -> environment -> URust_AST.literal_payload -> term
  val literal_identifier_value:
    Proof.context -> environment -> string * Position.T -> term
  val literal_identifier:
    Proof.context -> environment -> string * Position.T -> term
  val ordinary_identifier_value:
    Proof.context -> environment -> string * Position.T -> term
  val literal_path_value:
    Proof.context -> environment -> URust_AST.ur_path -> term
  val literal_path:
    Proof.context -> environment -> URust_AST.ur_path -> term
  val literal_path_with_category:
    Proof.context -> environment -> URust_AST.ur_path ->
      term * value_category
  val global_constant_path_value:
    Proof.context -> environment -> URust_AST.ur_path -> term
  val function_identifier:
    Proof.context -> environment -> string * Position.T -> term
  val function_path:
    Proof.context -> environment -> URust_AST.ur_path -> int -> term
  val struct_function_path:
    Proof.context -> environment -> URust_AST.ur_path -> int -> term
  val method_path:
    Proof.context -> environment -> URust_AST.ur_path -> term
  val apply_generic_arguments:
    Proof.context -> environment -> term ->
      URust_AST.generic_args option -> term
  val registered_function:
    Proof.context -> string * Position.T -> term option
  val registered_macro_path:
    Proof.context -> URust_AST.ur_path ->
      {complete_name: string,
       complete_pos: Position.T,
       bang_pos: Position.T} ->
      term option
  val registered_function_path:
    Proof.context -> URust_AST.ur_path -> term option
  val is_nullary_function_path:
    Proof.context -> environment -> URust_AST.ur_path -> bool
  val field_expression:
    Proof.context -> environment -> term -> string -> Position.T -> term

  type constructor_info
  type constructor_resolver
  datatype registered_literal_class =
      Unregistered_Literal
    | Registered_Value_Literal
    | Registered_Constructor_Literal
  val make_constructor_resolver:
    Proof.context -> Position.T -> constructor_resolver
  val classify_registered_literal:
    Proof.context -> constructor_resolver ->
      URust_AST.ur_path -> registered_literal_class
  val resolve_constructor:
    Proof.context -> constructor_resolver ->
      URust_AST.ur_path -> constructor_info option
  val constructor_term: constructor_info -> term
  val constructor_arity: constructor_info -> int
  val constructor_family: constructor_info -> (string * term list) option
  val report_constructor:
    Proof.context -> URust_AST.ur_path -> constructor_info -> unit
  type field_reference
  val report_field:
    Proof.context -> Position.T -> term -> field_reference option -> unit

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info *
          (term * field_reference option *
            Position.T option * URust_AST.ur_pat) list
    | Resolved_Record_Struct of
        string *
          (term * field_reference option *
            Position.T option * URust_AST.ur_pat) list

  val resolve_struct_pattern:
    Proof.context -> constructor_resolver ->
      URust_AST.ur_path * URust_AST.struct_field list ->
      resolved_struct_pattern
end
\<close>

text\<open>
Resolution owns every effectful name operation: binder IDs and navigation, local shadowing,
antiquotation capture, notation dispatch, constructor reports, and struct metadata. Its environment is
abstract so downstream modules cannot depend on the underlying binder record.
\<close>

ML\<open>
(*
  URust_Resolution owns the effectful boundary between source names and shallow HOL terms. It is the
  only parser module that allocates lexical locals, resolves identifier roles and datatype metadata,
  parses binder-aware antiquotations, and emits name/binder PIDE reports. Pattern policy and
  compilation belong to URust_Patterns, case orchestration belongs to URust_Matching, macro policy
  belongs to URust_Macros, recursive expression lowering belongs to URust_Translate, and final type
  checking remains outside this structure.

  The public interface is:

  - environment is an abstract, immutable lexical scope. empty_environment has no locals.
    allocate_locals accepts source-name/definition-position pairs, rejects duplicate names within its
    input before allocating any of them, then extends the supplied scope with fresh dummy-typed locals
    while reporting their definitions. allocate_closure_formals instead permits repeated names,
    allocates one distinct Free per source formal in source order, and returns those Frees together
    with the final environment in which each later repeated name shadows its predecessors.
    allocate_expression_arguments and allocate_function_parameters reject duplicate named
    parameters through the same validation path. Named slots allocate the supplied type, enter the
    lexical environment with direct-call precedence, and return a source-ordered Term.lambda
    operation. A `_` slot enters no environment and returns a typed anonymous Abs operation instead;
    repeated and mixed wildcards therefore retain their type slots and abstraction order without
    becoming resolvable names. Untyped expression clients supply dummy types for inference; typed
    clients supply argument or parameter types from the complete declaration type. A nested ordinary
    binder with the same name removes the declaration-argument precedence marker while shadowing the
    outer argument. use_local performs a positioned lookup, reports a bound reference on success, and
    returns NONE without fallback resolution; lookup_local performs the same lexical lookup without
    reporting. Single-local allocation and the generic binder records are private implementation
    details.

  - parse_antiquotation parses an Input.source as a HOL term with every environment entry in lexical
    scope. Lexical names shadow context fixes and constants, and occurrences are restored to the exact
    local terms held by the environment while retaining ordinary HOL parsing and markup.
    anonymous_abstraction introduces one anonymous dummy-typed Abs without manufacturing a Free.
    report_wildcard emits the parser's wildcard typing report. report_struct_label marks one
    metadata-free struct-expression label with a syntax tooltip but deliberately does not report a
    HOL Free: labels are erased by source-order lowering and do not denote terms.
    report_struct_labels resolves field aliases for generated datatype constructors and reports
    their selector constants, falling back to report_struct_label when no alias is available.

  - literal_value lowers a literal payload to its unlifted HOL value, including binder-aware value
    antiquotations. literal_expression preserves the frontend's special boolean-expression shape and
    otherwise lifts literal_value. literal_identifier_value resolves locals before NLiteral
    notation/HOL fallback without lifting, and literal_identifier lifts that result. A single-segment
    direct NFunction call head resolves a declaration argument before an exact registration or HOL
    fallback; qualified call paths and method names retain registration-first resolution. In the
    NField role an exact registered notation wins, otherwise a lexical local wins before HOL fallback.
    ordinary_identifier_value resolves a lexical local before ordinary HOL parsing and deliberately
    performs no micro_rust_notation lookup; log-data identifiers use this path. function_identifier
    returns the selected unlifted direct callee. apply_generic_arguments parses the retained
    restricted generic argument sources in the current lexical environment and applies them to an
    already-resolved term from left to right.
    global_constant_path_value is the stricter array-repeat-length route: it rejects lexical locals,
    accepts exact literal registrations whose selected backend may depend on the proof context,
    direct fixed parameters, or genuine unqualified HOL constants. Qualified paths require exact
    literal registration, and the route never creates an unresolved Free.
    registered_function performs an exact registered NFunction lookup without imposing a caller
    naming policy. registered_macro_path performs the same lookup for the complete spelling including
    `!`, but rejects an unregistered qualified source path through the common call-role diagnostic.
    is_nullary_function_path is a report-free ambiguity query used by control-head
    validation: declaration arguments retain direct-call precedence, ordinary lexical values and
    fixed variables remain value paths, and otherwise an exact registered backend or proper HOL
    constant counts only when its declared type takes zero arguments before function_body.
    field_expression applies the same role policy and focuses the supplied receiver.
    Registered notation is represented by the existing dispatch marker; unregistered names retain
    Syntax.parse_term behavior. Every module-like qualifier of an exact registered path receives one
    role tooltip without pretending to be a HOL Free or backend constant, while its notation
    references are deferred until typed dispatch selects a registration. For an exact registered
    literal path whose complete backend matches genuine Ctr_Sugar constructor metadata, the nearest
    qualifier instead reports every distinct datatype family with the constructor's keyword styling;
    typed dispatch subsequently gives every segment the selected declaration target. Every
    multi-segment source path requires an exact role-appropriate notation registration; unqualified
    lexical, fixed, HOL, and constructor fallback remains unchanged.

  - constructor_info and constructor_resolver are abstract. make_constructor_resolver snapshots the
    context's non-record Ctr_Sugar constructors, constructor families/selectors, and HOL record names
    for a resolution site. classify_registered_literal is a report-free exact-registration query:
    it distinguishes absence, a nonconstructor value backend, and an authentic constructor backend
    by consulting Ctr_Sugar first and then native Case_Translation metadata for an exact registered
    backend absent there. It does not select a constructor, diagnose ambiguity, or emit semantic
    markup. resolve_constructor performs those later operations; unregistered lookup remains limited
    to constructors authenticated by Code.is_constr or Case_Translation metadata, using exact
    identity for qualified names and basename lookup for unqualified names. Qualified source
    constructor paths resolve only through their exact literal registration; no parsed Rust path is
    translated into an Isabelle long name. Resolution returns NONE when an unqualified name is absent
    and raises a positioned, deterministic ambiguity error for multiple matches.
    constructor_term returns the dummy-typed constructor term, constructor_arity its argument count,
    and constructor_family optionally the datatype identity with all family constructor terms.
    Constructor metadata deliberately carries no registration provenance: once native Isabelle
    metadata authenticates a backend as a constructor, every downstream pattern use is structural.
    report_constructor emits source-path markup only after a caller has validated the resolved
    constructor. Exact registered literals report backend/datatype information first, retain every
    registration reference, and make the lowest-serial declaration authenticating the selected
    constructor the final target on every source segment. Unregistered HOL constructors retain free
    qualifiers and constant terminal markup. Generated item references likewise retain HOL type and
    constructor navigation before making the source datatype declaration the final target.
    report_field emits selector-constant markup immediately and queues an authenticated generated
    source-field reference for replay after complete command checking; native fields have no source
    reference.

  - resolve_struct_pattern resolves a struct head as a constructor, a single-constructor datatype
    type name, or a HOL record type. It validates duplicate, unknown, missing, and repeated-rest
    fields, expands shorthand fields, and returns fields in metadata declaration order. Each ordered
    field carries its selector, an optional authenticated generated source-field identity, and
    (SOME source_position, pattern) when written or
    (NONE, P_Wild Position.none) when supplied by `..`.
    Resolved_Constructor_Struct carries constructor_info plus those fields;
    Resolved_Record_Struct carries the qualified record type name plus those fields. Policy for
    rejecting the currently unsupported HOL-record lowering belongs to URust_Patterns.

  Callers may rely on those results and diagnostics, but not on the environment table or binder
  record, generated local names/entity IDs, identifier-leaf inspection, catalog and metadata merge
  strategy, candidate ordering, private selector storage, or the internal Constructor_Candidate /
  Record_Candidate distinction. Those are implementation details hidden by URUST_RESOLUTION.
*)
structure URust_Resolution :> URUST_RESOLUTION =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure I = URust_Item_Scope

  datatype value_category =
      Ordinary_Value
    | Reference_Value
    | Auto_Deref_Eligible

  type field_reference = I.field_entry
  type local_table = Parser_Utils.var_info Symtab.table
  type environment =
    {locals: local_table,
     local_categories: value_category Symtab.table,
     declaration_arguments: unit Symtab.table}

  val variable_entity_kind = "urust_var"
  val report_reference = Parser_Utils.report_ref variable_entity_kind
  val bind_local = Parser_Utils.bind_var variable_entity_kind
  val bind_typed_local = Parser_Utils.bind_typed_var variable_entity_kind
  val reference_type_name =
    (case \<^typ>\<open>('a, 'b, 'v) Global_Store.ref\<close> of
       Type (type_name, _) => type_name
     | _ =>
         error
           "urust_expr: internal reference type is not a constructor")

  val empty_environment =
    {locals = Symtab.empty,
     local_categories = Symtab.empty,
     declaration_arguments = Symtab.empty}
  val anonymous_abstraction = Parser_Utils.anon_abs

  fun parse_antiquotation ctxt
      ({locals, ...} : environment) source =
    Parser_Utils.parse_antiq variable_entity_kind ctxt locals source

  fun bind_ordinary_local category ctxt
      ({locals, local_categories, declaration_arguments} : environment)
      (binding as (name, _)) =
    let
      val (free, locals') = bind_local ctxt locals binding
    in
      (free,
       {locals = locals',
        local_categories =
          Symtab.update (name, category) local_categories,
        declaration_arguments =
          Symtab.delete_safe name declaration_arguments})
    end

  fun bind_declaration_argument ctxt
      ({locals, local_categories, declaration_arguments} : environment)
      (parameter as ((name, _), _)) =
    let
      val (free, locals') = bind_typed_local ctxt locals parameter
      val category =
        (case #2 parameter of
           Type (type_name, _) =>
             if type_name = reference_type_name
             then Reference_Value
             else Ordinary_Value
         | _ => Reference_Value)
    in
      (free,
       {locals = locals',
        local_categories =
          Symtab.update (name, category) local_categories,
        declaration_arguments =
          Symtab.update (name, ()) declaration_arguments})
    end

  fun allocate_locals category ctxt environment signatures =
    let
      fun validate (name, pos) seen =
        (case Symtab.lookup seen name of
           NONE => Symtab.update (name, pos) seen
         | SOME original_pos =>
             error ("urust_expr: duplicate pattern binder " ^ quote name ^
               Position.here pos ^ "\nThe original binder is here" ^
               Position.here original_pos))
      val _ = fold validate signatures Symtab.empty
      fun allocate binding env =
        #2 (bind_ordinary_local category ctxt env binding)
    in fold allocate signatures environment end

  fun allocate_closure_formals ctxt environment signatures =
    let
      fun allocate [] env frees = (rev frees, env)
        | allocate (formal :: rest) env frees =
            let
              val (free, env') =
                bind_ordinary_local Reference_Value ctxt env formal
            in allocate rest env' (free :: frees) end
    in allocate signatures environment [] end

  fun allocate_parameters command role ctxt environment parameters =
    let
      fun validate ((name, pos), _) seen =
        if name = "_" then seen
        else
          (case Symtab.lookup seen name of
             NONE => Symtab.update (name, pos) seen
           | SOME original_pos =>
               error
                 (command ^ ": duplicate " ^ role ^ " " ^ quote name ^
                   Position.here pos ^ "\nThe original " ^ role ^ " is here" ^
                   Position.here original_pos))
      val _ = fold validate parameters Symtab.empty
      fun allocate [] env abstractions = (rev abstractions, env)
        | allocate ((parameter as ((name, pos), T)) :: rest) env abstractions =
            let
              val _ =
                Context_Position.report_text ctxt pos Markup.typing
                  ("uRust " ^ role ^ " :: " ^ Syntax.string_of_typ ctxt T)
              val (abstraction, env') =
                if name = "_" then
                  ((fn body => Abs (Name.uu, T, body)), env)
                else
                  let
                    val (free, env') =
                      bind_declaration_argument ctxt env parameter
                  in ((fn body => Term.lambda free body), env') end
            in allocate rest env' (abstraction :: abstractions) end
    in allocate parameters environment [] end

  fun allocate_expression_arguments ctxt environment arguments =
    allocate_parameters "urust_expr" "argument" ctxt environment arguments

  fun allocate_function_parameters ctxt environment parameters =
    allocate_parameters "urust_fn" "parameter" ctxt environment parameters

  fun use_local ctxt environment (name, pos) =
    (case Symtab.lookup (#locals environment) name of
       SOME {free, def_pos, id} =>
         (report_reference ctxt id (name, def_pos) pos; SOME free)
     | NONE => NONE)

  fun use_local_with_category ctxt
      (environment as {local_categories, ...} : environment)
      (identifier as (name, _)) =
    (case use_local ctxt environment identifier of
       SOME local_term =>
         SOME
           (local_term,
            the_default Reference_Value
              (Symtab.lookup local_categories name))
     | NONE => NONE)

  fun lookup_local environment name =
    Option.map #free (Symtab.lookup (#locals environment) name)

  fun use_declaration_argument ctxt
      (environment as {declaration_arguments, ...} : environment)
      (identifier as (name, _)) =
    if Symtab.defined declaration_arguments name
    then use_local ctxt environment identifier
    else NONE

  (* Syntax.parse_term wraps resolved constants in an internal type constraint. Resolution and
     call-role validation inspect through that wrapper while retaining it for the final check_term. *)
  fun identifier_leaf term =
    (case Term_Position.strip_positions term of
       Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ inner =>
         identifier_leaf inner
     | inner => inner)

  fun resolve_hol_identifier ctxt name pos =
    if Variable.is_fixed ctxt name then
      let
        val fixed = the (Proof_Context.lookup_free ctxt name)
        val _ =
          List.app (Context_Position.report ctxt pos)
            (Syntax_Phases.markup_free ctxt fixed)
      in T.source_position pos (Free (fixed, dummyT)) end
    else
      let
        val source =
          Parser_Lex_Util.positioned_content_source name
            (Position.no_range_position pos)
        val term = Syntax.parse_term ctxt (Syntax.implode_input source)
      in
        (case identifier_leaf term of
           Const (constant_name, _) =>
             let
               val consts = Proof_Context.consts_of ctxt
               val constant_type = Consts.the_constraint consts constant_name
               val _ =
                 List.app (Context_Position.report ctxt pos)
                   [Name_Space.markup (Consts.space_of consts) constant_name,
                    Markup.const]
             in
               Context_Position.report_text ctxt pos Markup.typing
                 (Syntax.string_of_typ ctxt constant_type)
             end
         | _ => ());
        term
      end

  fun call_result_may_be_function_body
      (Type (\<^type_name>\<open>fun\<close>, [_, result])) =
        call_result_may_be_function_body result
    | call_result_may_be_function_body
        (Type (\<^type_name>\<open>function_body\<close>, _)) = true
    | call_result_may_be_function_body (TFree _) = true
    | call_result_may_be_function_body (TVar _) = true
    | call_result_may_be_function_body _ = false

  fun constrain_call_head ctxt name pos term =
    (case identifier_leaf term of
       Const (constant_name, _) =>
         let
           val constant_type =
             Consts.the_constraint
               (Proof_Context.consts_of ctxt) constant_name
         in
           if call_result_may_be_function_body constant_type then term
           else
             error
               ("Type unification failed: call head " ^ quote name ^
                 " has pure HOL type " ^
                 quote (Syntax.string_of_typ ctxt constant_type) ^
                 ", whose result is not a shallow function_body" ^
                 Position.here pos)
         end
     | _ => term)

  (* Registered notation witnesses must remain bare Frees until the enclosing Term.lambda can capture
     them. This is the witness-precedence rule that lets a lexical binder shadow a notation. *)
  fun resolve_identifier_at_positions ctxt kind name pos qualifier_positions =
    (case Micro_Rust_Names.lookups ctxt kind name of
       [] => resolve_hol_identifier ctxt name pos
         |> (case kind of
               Micro_Rust_Names.NFunction =>
                 constrain_call_head ctxt name pos
             | _ => I)
     | _ =>
         Micro_Rust_Dispatch.mk_marker_positions
           kind name pos qualifier_positions (Free (name, dummyT)))

  fun resolve_identifier ctxt kind name pos =
    resolve_identifier_at_positions ctxt kind name pos []

  fun literal_identifier_value ctxt environment (identifier as (name, pos)) =
    (case use_local ctxt environment identifier of
       SOME local_term => local_term
     | NONE =>
         resolve_identifier ctxt Micro_Rust_Names.NLiteral name pos)

  fun literal_identifier ctxt environment identifier =
    T.literal (literal_identifier_value ctxt environment identifier)

  fun ordinary_identifier_value ctxt environment
      (identifier as (name, pos)) =
    let
      val _ =
        Context_Position.report_text ctxt pos Markup.typing
          "log data identifier"
    in
      (case use_local ctxt environment identifier of
         SOME local_term => local_term
       | NONE => resolve_hol_identifier ctxt name pos)
    end

  fun registered_identifier ctxt kind (name, pos) =
    if null (Micro_Rust_Names.lookups ctxt kind name)
    then NONE
    else SOME (resolve_identifier ctxt kind name pos)

  fun registered_identifier_at_positions ctxt kind
      (name, pos) qualifier_positions =
    if null (Micro_Rust_Names.lookups ctxt kind name)
    then NONE
    else
      SOME
        (resolve_identifier_at_positions
          ctxt kind name pos qualifier_positions)

  type native_case_metadata =
    {identity: string,
     constructor: term,
     arity: int,
     family_name: string,
     family_members: term list}

  fun native_case_metadata ctxt backend =
    (case identifier_leaf backend of
       Const (identity, typ) =>
         (case Case_Translation.lookup_by_constr_permissive ctxt
             (identity, typ) of
            NONE => NONE
          | SOME (_, members) =>
              let
                val normalized_backend = Const (identity, dummyT)
                fun normalize_member member =
                  (case identifier_leaf member of
                     Const (name, member_typ) =>
                       SOME
                         (Const (name, dummyT),
                          try dest_Type_name (body_type member_typ))
                   | _ => NONE)
                val normalized = map_filter normalize_member members
                val family_name = try dest_Type_name (body_type typ)
                val exact_member =
                  exists
                    (fn (member, _) =>
                      Term.aconv_untyped
                        (normalized_backend, member))
                    normalized
                val one_family =
                  (case family_name of
                     NONE => false
                   | SOME name =>
                       length normalized = length members andalso
                         List.all
                           (fn (_, SOME member_name) =>
                                 member_name = name
                             | _ => false)
                           normalized)
              in
                if exact_member andalso one_family then
                  SOME
                    {identity = identity,
                     constructor = normalized_backend,
                     arity = length (binder_types typ),
                     family_name = the family_name,
                     family_members = map fst normalized}
                else NONE
              end)
     | _ => NONE)

  fun registered_constructor_family_names ctxt registrations =
    let
      val backends =
        map
          (identifier_leaf o
            (fn ({hol_term, ...} : Micro_Rust_Names.entry) => hol_term))
          registrations

      fun sugar_families backend =
        Ctr_Sugar.ctr_sugars_of ctxt
        |> map_filter
          (fn ({kind, T, ctrs, ...} : Ctr_Sugar.ctr_sugar) =>
            if (kind = Ctr_Sugar.Datatype orelse
                kind = Ctr_Sugar.Codatatype) andalso
                exists
                  (fn constructor =>
                    Term.aconv_untyped
                      (backend, identifier_leaf constructor))
                  ctrs
            then
              (case T of
                 Type (name, _) => SOME name
               | _ => NONE)
            else NONE)

      fun backend_families backend =
        (case sugar_families backend of
           [] =>
             (case native_case_metadata ctxt backend of
                SOME {family_name, ...} => [family_name]
              | NONE => [])
         | families => families)
    in
      backends
      |> maps backend_families
      |> distinct (op =)
      |> sort_strings
    end

  fun report_free_path_segment ctxt segment =
    Context_Position.report ctxt
      (#2 (segment_identifier segment)) Markup.free

  fun notation_role Micro_Rust_Names.NLiteral = "literal"
    | notation_role Micro_Rust_Names.NFunction = "call"
    | notation_role Micro_Rust_Names.NField = "field"

  fun report_registered_path_segment ctxt kind name segment =
    let
      val pos = #2 (segment_identifier segment)
    in
      Context_Position.report_text ctxt pos Markup.typing
        ("registered " ^ notation_role kind ^
          " path qualifier for " ^ quote name)
    end

  fun identifier_qualifiers path =
    let
      val segments = path_segments path
      val qualifiers =
        if null segments then [] else take (length segments - 1) segments
    in
      if is_primitive_path path andalso not (null qualifiers)
      then tl qualifiers
      else qualifiers
    end

  fun report_path_qualifiers ctxt path =
    List.app (report_free_path_segment ctxt)
      (identifier_qualifiers path)

  fun report_registered_path_qualifiers ctxt kind name path =
    let val qualifiers = identifier_qualifiers path in
      List.app
        (report_registered_path_segment ctxt kind name)
        qualifiers
    end

  fun path_qualifier_positions path =
    map (#2 o segment_identifier) (identifier_qualifiers path)

  fun report_literal_path_qualifiers ctxt registrations path =
    let
      val name = render_path path
      val qualifiers = identifier_qualifiers path
      val families =
        registered_constructor_family_names ctxt registrations

      fun report_family segment family =
        let
          val pos = #2 (segment_identifier segment)
          val type_space = Proof_Context.type_space ctxt
        in
          List.app (Context_Position.report ctxt pos)
            [Name_Space.markup type_space family, Markup.keyword3]
        end
    in
      (case rev qualifiers of
         [] => ()
       | nearest :: earlier =>
           (List.app
              (report_registered_path_segment
                ctxt Micro_Rust_Names.NLiteral name)
              (rev earlier);
            if null families
            then
              report_registered_path_segment
                ctxt Micro_Rust_Names.NLiteral name nearest
            else List.app (report_family nearest) families))
    end

  fun path_terminal path = segment_identifier (final_segment path)

  fun item_lookup_path
      (UR_Path (head, segments, pos)) =
    UR_Path
      (head,
       map
         (fn Path_Segment (name, name_pos, _) =>
           Path_Segment (name, name_pos, NONE))
         segments,
       pos)

  fun exact_item_constructor ctxt path =
    I.lookup_constructor ctxt
      (render_path (item_lookup_path path))

  fun item_constructor_identities ctxt =
    I.dump_constructors ctxt
    |> map_filter
      (fn entry =>
        (case I.constructor_term entry of
           Const (name, _) => SOME name
         | _ => NONE))

  fun generated_basename_entries ctxt name =
    I.dump_constructors ctxt
    |> filter
      (fn entry =>
        (case I.constructor_term entry of
           Const (identity, _) =>
             Long_Name.base_name identity = name
         | _ => false))

  fun generated_basename_error ctxt role path =
    let
      val name = render_path path
      val pos = #2 (path_terminal path)
      val exact_paths =
        generated_basename_entries ctxt name
        |> map I.constructor_rust_path
        |> sort_strings
    in
      if null exact_paths then ()
      else
        error
          ("urust_expr: generated Rust " ^ role ^ " " ^
            quote name ^
            " requires an exact item path; available paths: " ^
            commas_quote exact_paths ^
            Position.here pos)
    end

  fun report_item_qualifiers ctxt path entry =
    let
      val qualifiers = identifier_qualifiers path
      fun report_type segment =
        let
          val pos = #2 (segment_identifier segment)
          val type_name = I.constructor_hol_type entry
          val type_entry =
            (case I.lookup_type ctxt
                (I.constructor_rust_type entry) of
               SOME registered => registered
             | NONE =>
                 error
                   ("urust_expr: generated Rust constructor " ^
                     quote (I.constructor_rust_path entry) ^
                     " has no source type identity"))
        in
          List.app (Context_Position.report ctxt pos)
            [Name_Space.markup
               (Proof_Context.type_space ctxt) type_name,
             Markup.keyword3];
          I.report_type_reference ctxt pos type_entry
        end
    in
      (case rev qualifiers of
         [] => ()
       | nearest :: earlier =>
           (List.app (report_free_path_segment ctxt) (rev earlier);
            report_type nearest))
    end

  fun report_item_constructor ctxt path entry =
    let
      val (_, pos) = path_terminal path
      val constructor = I.constructor_term entry
      val _ = report_item_qualifiers ctxt path entry
      val _ = Context_Position.report ctxt pos Markup.keyword3
      val _ =
        (case constructor of
           Const (name, _) =>
             Context_Position.report ctxt pos
               (Name_Space.markup
                 (Consts.space_of (Proof_Context.consts_of ctxt))
                 name)
         | _ => ())
      val _ = I.report_constructor_reference ctxt pos entry
    in () end

  fun item_constructor_arity ctxt entry =
    (case I.constructor_term entry of
       Const (name, _) =>
         length
           (binder_types
             (Consts.the_constraint
               (Proof_Context.consts_of ctxt) name))
     | _ =>
         error
           ("urust_expr: generated Rust item " ^
             quote (I.constructor_rust_path entry) ^
             " has no constant constructor identity"))

  fun reject_item_generics path =
    if exists (is_some o segment_generic_args) (path_segments path)
    then
      let
        val offending =
          the
            (find_first (is_some o segment_generic_args)
              (path_segments path))
        val Generic_Args (_, pos) =
          the (segment_generic_args offending)
      in
        error
          ("urust_expr: generic arguments are not supported on generated Rust item paths" ^
            Position.here pos)
      end
    else ()

  fun item_value_path ctxt path entry =
    let
      val _ = reject_item_generics path
      val _ =
        (case I.constructor_shape entry of
           I.Unit_Constructor => ()
         | I.Tuple_Constructor =>
             error
               ("urust_expr: generated Rust constructor " ^
                 quote (render_path path) ^
                 " requires positional call syntax" ^
                 Position.here (path_position path))
         | I.Named_Constructor =>
             error
               ("urust_expr: generated Rust constructor " ^
                 quote (render_path path) ^
                 " requires struct construction syntax" ^
                 Position.here (path_position path)))
      val _ = report_item_constructor ctxt path entry
    in
      T.source_position (#2 (path_terminal path))
        (I.constructor_term entry)
    end

  fun generic_sources (Generic_Args (arguments, _)) =
    map generic_argument_source arguments

  fun apply_generic_arguments ctxt environment function arguments =
    T.apply_parameters function
      (case arguments of
         NONE => []
       | SOME generic_arguments =>
           map (parse_antiquotation ctxt environment)
             (generic_sources generic_arguments))

  fun has_intermediate_generics path =
    let
      val segments = path_segments path
      val intermediate =
        if null segments then [] else take (length segments - 1) segments
    in List.exists (is_some o segment_generic_args) intermediate end

  fun reject_intermediate_generics path =
    if has_intermediate_generics path then
      let
        val offending =
          the
            (find_first (is_some o segment_generic_args)
              (path_segments path))
      in
        error
          ("urust_expr: generic arguments on an intermediate path segment require an exact registration" ^
            Position.here (#2 (segment_identifier offending)))
      end
    else ()

  fun opaque_path ctxt kind path =
    let
      val _ = report_path_qualifiers ctxt path
      val (name, pos) = path_terminal path
      val _ = Context_Position.report ctxt pos Markup.free
    in Free (render_path path, dummyT) end

  fun qualified_registration_error kind path displayed_name pos =
    error
      ("urust_expr: qualified path " ^ quote displayed_name ^
        " requires an exact micro_rust_notation (" ^
        notation_role kind ^ ") declaration" ^
        Position.here pos)

  fun resolve_generic_free_path ctxt environment kind local_first path =
    (case path_segments path of
       [Path_Segment (name, pos, NONE)] =>
         if local_first then
           (case use_local ctxt environment (name, pos) of
              SOME local_term => local_term
            | NONE => resolve_identifier ctxt kind name pos)
         else
           (case registered_identifier ctxt kind (name, pos) of
              SOME registered => registered
            | NONE =>
                (case use_local ctxt environment (name, pos) of
                   SOME local_term => local_term
                 | NONE => resolve_identifier ctxt kind name pos))
     | _ =>
         (case registered_identifier_at_positions ctxt kind
             (render_path path, #2 (path_terminal path))
             (path_qualifier_positions path) of
            SOME registered =>
              (report_registered_path_qualifiers ctxt kind
                 (render_path path) path;
               registered)
          | NONE =>
              if is_qualified_path path
              then
                qualified_registration_error kind path
                  (render_path path) (path_position path)
              else opaque_path ctxt kind path))

  fun exact_registered_path ctxt kind path =
    (case registered_identifier_at_positions ctxt kind
        (render_path path, #2 (path_terminal path))
        (path_qualifier_positions path) of
       SOME registered =>
         let
           val _ =
             if kind = Micro_Rust_Names.NLiteral
             then
               report_literal_path_qualifiers ctxt
                 (Micro_Rust_Names.lookups ctxt kind (render_path path))
                 path
             else
               report_registered_path_qualifiers ctxt kind
                 (render_path path) path
         in SOME registered end
     | NONE => NONE)

  fun primitive_registration_error kind path =
    let
      val name = render_path path
      val pos = #2 (path_terminal path)
      val role =
        (case kind of
           Micro_Rust_Names.NLiteral => "literal"
         | Micro_Rust_Names.NFunction => "call"
         | Micro_Rust_Names.NField => "field")
    in
      error
        ("urust_expr: primitive associated-item path " ^ quote name ^
          " requires an exact micro_rust_notation (" ^
          role ^ ") declaration" ^
          Position.here pos)
    end

  fun global_constant_path_value ctxt environment path =
    let
      val name = render_path path
      val (_, pos) = path_terminal path
      val _ = reject_intermediate_generics path
      val _ =
        (case segment_generic_args (final_segment path) of
           NONE => ()
         | SOME (Generic_Args (_, generic_pos)) =>
             error
               ("urust_expr: generic arguments are not allowed in an array repeat length" ^
                 Position.here generic_pos))
      val _ =
        (case path_segments path of
           [Path_Segment (local_name, local_pos, NONE)] =>
             if is_some (lookup_local environment local_name) then
               error
                 ("urust_expr: array repeat length cannot use lexical local " ^
                   quote local_name ^ Position.here local_pos)
             else ()
         | _ => ())

      fun resolve_global_constant () =
        (case try
            (Proof_Context.read_const
              {proper = true, strict = false} ctxt)
            name of
             SOME (Const (constant_name, _)) =>
               let
                 val consts = Proof_Context.consts_of ctxt
                 val constant_type =
                   Consts.the_constraint consts constant_name
                 val _ = report_path_qualifiers ctxt path
                 val _ =
                   List.app (Context_Position.report ctxt pos)
                     [Name_Space.markup
                        (Consts.space_of consts) constant_name,
                      Markup.const]
                 val _ =
                   Context_Position.report_text ctxt pos Markup.typing
                     (Syntax.string_of_typ ctxt constant_type)
               in
                 T.source_position pos
                   (Const (constant_name, dummyT))
               end
           | _ =>
               error
                 ("urust_expr: array repeat length path " ^
                   quote name ^
                   " does not resolve to a global constant, fixed parameter, or exact literal registration" ^
                   Position.here pos))

      fun resolve_contextual_or_global () =
        (case path_segments path of
           [Path_Segment (fixed_name, fixed_pos, NONE)] =>
             if Variable.is_fixed ctxt fixed_name
             then resolve_hol_identifier ctxt fixed_name fixed_pos
             else resolve_global_constant ()
         | _ => resolve_global_constant ())
    in
      (case exact_registered_path ctxt Micro_Rust_Names.NLiteral path of
         SOME registered => registered
       | NONE =>
           if is_primitive_path path then
             primitive_registration_error
               Micro_Rust_Names.NLiteral path
           else if is_qualified_path path then
             qualified_registration_error
               Micro_Rust_Names.NLiteral path name (path_position path)
           else resolve_contextual_or_global ())
    end

  fun literal_path_value ctxt environment path =
    if is_primitive_path path then
      (case exact_registered_path ctxt
          Micro_Rust_Names.NLiteral path of
         SOME registered => registered
       | NONE =>
           primitive_registration_error
             Micro_Rust_Names.NLiteral path)
    else
    (case path_segments path of
       [Path_Segment (name, pos, NONE)] =>
         (case use_local ctxt environment (name, pos) of
            SOME local_term => local_term
          | NONE =>
              (case exact_item_constructor ctxt path of
                 SOME entry => item_value_path ctxt path entry
               | NONE =>
                   (generated_basename_error ctxt "value" path;
                    resolve_identifier ctxt
                      Micro_Rust_Names.NLiteral name pos)))
     | _ =>
         (case exact_item_constructor ctxt path of
            SOME entry => item_value_path ctxt path entry
          | NONE =>
              (case exact_registered_path ctxt
                  Micro_Rust_Names.NLiteral path of
                 SOME registered => registered
               | NONE =>
                   let
                     val _ = reject_intermediate_generics path
                     val _ =
                       (case segment_generic_args
                           (final_segment path) of
                          NONE => ()
                        | SOME (Generic_Args (_, pos)) =>
                            error
                              ("urust_expr: generic arguments on a bare value require an exact literal registration" ^
                                Position.here pos))
                   in
                     resolve_generic_free_path ctxt environment
                       Micro_Rust_Names.NLiteral true path
                   end)))

  fun literal_path ctxt environment path =
    T.literal (literal_path_value ctxt environment path)

  fun literal_path_with_category ctxt environment path =
    if is_primitive_path path then
      (T.literal (literal_path_value ctxt environment path),
       Reference_Value)
    else
      (case path_segments path of
         [Path_Segment (name, pos, NONE)] =>
           (case use_local_with_category ctxt environment (name, pos) of
              SOME (local_term, category) =>
                (T.literal local_term, category)
            | NONE =>
                (T.literal
                  (literal_path_value ctxt environment path),
                 Reference_Value))
       | _ =>
           (T.literal (literal_path_value ctxt environment path),
            Reference_Value))

  fun function_identifier ctxt environment (identifier as (name, pos)) =
    (case use_declaration_argument ctxt environment identifier of
       SOME local_term => local_term
     | NONE =>
         (case registered_identifier ctxt Micro_Rust_Names.NFunction identifier of
            SOME registered => registered
          | NONE =>
              (case use_local ctxt environment identifier of
                 SOME local_term => local_term
               | NONE =>
                   resolve_identifier ctxt Micro_Rust_Names.NFunction name pos)))

  datatype item_call_role =
      Ordinary_Item_Call
    | Struct_Item_Call
    | No_Item_Call

  fun item_function_entry ctxt path entry =
    let
      val _ = reject_item_generics path
      val pos = #2 (path_terminal path)
      val _ = I.defer_function_reference ctxt pos entry
    in
      T.source_position pos (I.function_term entry)
    end

  fun item_function_path role ctxt path actual_arity entry =
    let
      val _ = reject_item_generics path
      val name = render_path path
      val pos = #2 (path_terminal path)
      val origin = I.constructor_origin entry
      val shape = I.constructor_shape entry
      val _ =
        (case (role, origin, shape) of
           (Ordinary_Item_Call, _, I.Tuple_Constructor) => ()
         | (Ordinary_Item_Call, _, I.Unit_Constructor) =>
             error
               ("urust_expr: generated unit constructor " ^
                 quote name ^ " is a bare value, not a call" ^
                 Position.here pos)
         | (Ordinary_Item_Call, I.Struct_Constructor,
              I.Named_Constructor) =>
             error
               ("urust_expr: generated named struct " ^
                 quote name ^
                 " must use struct construction syntax" ^
                 Position.here pos)
         | (Ordinary_Item_Call, I.Enum_Variant,
              I.Named_Constructor) =>
             error
               ("urust_expr: construction of named enum variant " ^
                 quote name ^ " requires metadata-aware struct construction" ^
                 Position.here pos)
         | (Struct_Item_Call, I.Struct_Constructor,
              I.Named_Constructor) => ()
         | (Struct_Item_Call, I.Enum_Variant,
              I.Named_Constructor) =>
             error
               ("urust_expr: construction of named enum variant " ^
                 quote name ^ " requires metadata-aware struct construction" ^
                 Position.here pos)
         | (Struct_Item_Call, _, _) =>
             error
               ("urust_expr: generated constructor " ^
                 quote name ^
                 " does not support struct construction syntax" ^
                 Position.here pos)
         | (No_Item_Call, _, _) =>
             error "urust_expr: internal generated item method resolution")
      val arity = item_constructor_arity ctxt entry
      val _ =
        if arity = actual_arity then ()
        else
          error
            ("Type unification failed: generated Rust constructor " ^
              quote name ^ " expects " ^ string_of_int arity ^
              " argument(s), but got " ^
              string_of_int actual_arity ^
              Position.here pos)
      val _ = report_item_constructor ctxt path entry
    in
      T.source_position pos
        (T.lift_function pos arity
          (I.constructor_term entry))
    end

  fun resolve_function_path item_role local_first actual_arity
      ctxt environment path =
    let
      val head_pos = #2 (path_terminal path)
      fun lexical_function () =
        if local_first then
          (case path_segments path of
             [Path_Segment (name, pos, generic_arguments)] =>
               Option.map
                 (fn local_term =>
                   apply_generic_arguments ctxt environment
                     local_term generic_arguments)
                 (use_declaration_argument ctxt environment (name, pos))
           | _ => NONE)
        else NONE
      val function =
        (case lexical_function () of
           SOME local_term => local_term
         | NONE =>
             (case
                if item_role = No_Item_Call
                then NONE
                else I.lookup_function ctxt (render_path path)
              of
                SOME entry =>
                  item_function_entry ctxt path entry
              | NONE =>
             (case
                if item_role = No_Item_Call
                then NONE
                else exact_item_constructor ctxt path
              of
                SOME entry =>
                  item_function_path item_role ctxt path
                    actual_arity entry
              | NONE =>
                  (case exact_registered_path ctxt
                      Micro_Rust_Names.NFunction path of
                     SOME registered => registered
                   | NONE =>
                       if is_primitive_path path then
                         primitive_registration_error
                           Micro_Rust_Names.NFunction path
                       else
                       let
                         val _ =
                           if is_qualified_path path then ()
                           else
                             generated_basename_error
                               ctxt "call" path
                         val _ = reject_intermediate_generics path
                         val base = remove_final_generic_args path
                         val function =
                           resolve_generic_free_path ctxt environment
                             Micro_Rust_Names.NFunction false base
                       in
                         apply_generic_arguments ctxt environment
                           function
                           (segment_generic_args
                             (final_segment path))
                       end))))
      fun same_range position =
        Position.offset_of position = Position.offset_of head_pos andalso
        Position.end_offset_of position = Position.end_offset_of head_pos
      val already_positioned =
        (case function of
           Const (\<^syntax_const>\<open>_type_constraint_\<close>,
               Type (\<^type_name>\<open>fun\<close>, [position_type, _])) $ _ =>
             exists (same_range o #pos)
               (Term_Position.decode_positionT position_type)
         | _ => false)
    in
      if already_positioned then function
      else T.source_position head_pos function
    end

  fun function_path ctxt environment path actual_arity =
    resolve_function_path Ordinary_Item_Call true actual_arity
      ctxt environment path

  fun struct_function_path ctxt environment path actual_arity =
    resolve_function_path Struct_Item_Call false actual_arity
      ctxt environment path

  fun method_path ctxt environment path =
    let
      val function =
        resolve_function_path No_Item_Call false 0
          ctxt environment path
      val (name, pos) = path_terminal path
      val lexical =
        (case path_segments path of
           [Path_Segment _] =>
             is_some (lookup_local environment name)
         | _ => false)
      fun strip_internal_positions
          (Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ inner) =
            strip_internal_positions inner
        | strip_internal_positions term = term
      val head = Term.head_of (strip_internal_positions function)
      val unresolved =
        (case head of
           Free (free_name, _) =>
             not lexical andalso
             not (Variable.is_fixed ctxt free_name)
         | _ => false)
    in
      if unresolved then
        let
          val _ =
            Context_Position.report_text ctxt pos Markup.typing
              "unregistered uRust method call head"
        in
          error
            ("Type unification failed: unregistered method call head " ^
              quote (render_path path) ^
              " has no lexical, fixed, or HOL constant resolution" ^
              Position.here pos)
        end
      else function
    end

  fun registered_function ctxt identifier =
    registered_identifier ctxt Micro_Rust_Names.NFunction identifier

  fun registered_macro_path ctxt path
      {complete_name, complete_pos, bang_pos} =
    if null
        (Micro_Rust_Names.lookups
          ctxt Micro_Rust_Names.NFunction complete_name)
    then
      if is_qualified_path path
      then
        qualified_registration_error Micro_Rust_Names.NFunction path
          complete_name complete_pos
      else NONE
    else
      let
        val terminal_pos =
          #2 (segment_identifier (final_segment path))
        val registered =
          Micro_Rust_Dispatch.mk_marker_positions_with_backend_targets
            Micro_Rust_Names.NFunction complete_name terminal_pos
            (path_qualifier_positions path) [bang_pos]
            (Free (complete_name, dummyT))
        val _ =
          report_registered_path_qualifiers ctxt
            Micro_Rust_Names.NFunction complete_name path
      in SOME registered end

  fun registered_function_path ctxt path =
    exact_registered_path ctxt Micro_Rust_Names.NFunction path

  fun function_body_arity
      (Type (\<^type_name>\<open>function_body\<close>, _)) = SOME 0
    | function_body_arity
        (Type (\<^type_name>\<open>fun\<close>, [_, result])) =
        Option.map (Integer.add 1) (function_body_arity result)
    | function_body_arity _ = NONE

  fun is_nullary_function_type T =
    function_body_arity T = SOME 0

  fun is_nullary_function_path ctxt
      ({locals, declaration_arguments, ...} : environment) path =
    let
      fun registered () =
        Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction
          (render_path path)
        |> exists
            (fn ({hol_term, ...} : Micro_Rust_Names.entry) =>
              is_nullary_function_type (fastype_of hol_term))

      fun hol_constant () =
        (case try
           (Proof_Context.read_const {proper = true, strict = false} ctxt)
            (render_path path) of
           SOME (Const (_, T)) => is_nullary_function_type T
         | _ => false)
    in
      if is_primitive_path path then registered ()
      else
      (case path_segments path of
         [Path_Segment (name, _, NONE)] =>
           (case Symtab.lookup locals name of
              SOME {free, ...} =>
                Symtab.defined declaration_arguments name andalso
                  is_nullary_function_type (fastype_of free)
            | NONE =>
                if Variable.is_fixed ctxt name
                then false
                else if registered () then true else hol_constant ())
       | _ =>
           registered ())
    end

  fun field_expression ctxt environment receiver name pos =
    T.focus_field
      (case registered_identifier ctxt Micro_Rust_Names.NField (name, pos) of
         SOME registered => registered
       | NONE =>
           (case use_local ctxt environment (name, pos) of
              SOME local_term => local_term
            | NONE =>
                resolve_identifier ctxt Micro_Rust_Names.NField name pos))
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
      {registered_by_identity: constructor_info Symtab.table,
       by_identity: constructor_info Symtab.table,
       by_basename: constructor_info list Symtab.table,
       type_fallbacks: (string * constructor_info) list,
       record_types: string list}

  datatype registered_literal_class =
      Unregistered_Literal
    | Registered_Value_Literal
    | Registered_Constructor_Literal

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
    String.isSubstring "::" name orelse
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
      val _ =
        if same_family (#family left, #family right) then ()
        else
          error
            ("urust_expr: inconsistent constructor family metadata for " ^
              quote identity ^ Position.here pos)
      val _ =
        if eq_list (op aconv) (#selectors left, #selectors right)
        then ()
        else
          error
            ("urust_expr: inconsistent constructor selector metadata for " ^
              quote identity ^ Position.here pos)
    in
      {identity = identity,
       constructor = #constructor left,
       arity = #arity left,
       family = #family left,
       selectors = #selectors left}
    end

  fun native_case_constructor_info ctxt backend =
    Option.map
      (fn {identity, constructor, arity, family_name,
            family_members} =>
        {identity = identity,
         constructor = constructor,
         arity = arity,
         family = SOME (family_name, family_members),
         selectors = []})
      (native_case_metadata ctxt backend)

  (* Keep bare native lookup aligned with Case_Term_Backend: typedef-backed constructors may be
     known through case translation even when the code generator does not classify them. Candidate
     metadata is still recovered and validated by native_case_constructor_info below. *)
  fun known_native_constructor ctxt (identity, typ) =
    let
      val theory = Proof_Context.theory_of ctxt
      val code_constructor =
        (Code.is_constr theory identity
          handle TYPE _ => false)
      val case_constructor =
        Option.isSome
          (Case_Translation.lookup_by_constr_permissive ctxt
            (identity, typ))
    in code_constructor orelse case_constructor end

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
      val item_identities = item_constructor_identities ctxt

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
            ({kind, T, ctrs, selss, ...} :
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
                     if kind = Ctr_Sugar.Datatype orelse
                         kind = Ctr_Sugar.Codatatype orelse
                         Code.is_constr theory identity
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

      val sugar_entries = maps catalog_entries sugars
      val sugar_by_identity =
        fold add_entry sugar_entries Symtab.empty

      val by_identity =
        Symtab.fold
          (fn (identity, info) =>
            if Code.is_constr theory identity andalso
                not (member (op =) item_identities identity)
            then Symtab.update (identity, info)
            else I)
          sugar_by_identity Symtab.empty

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
        {registered_by_identity = sugar_by_identity,
         by_identity = by_identity,
         by_basename = by_basename,
         type_fallbacks = type_fallbacks,
         record_types = record_types}
    end

  fun constructor_candidates ctxt
      (Constructor_Resolver
        {by_identity, by_basename, ...}) name =
    let
      val requested_name = name
      val sugar_candidates =
        if qualified_name name
        then
          (case Symtab.lookup by_identity requested_name of
             SOME info => [info]
           | NONE => [])
        else
          the_default [] (Symtab.lookup by_basename name)

      fun requested_identity identity =
        if qualified_name name
        then identity = requested_name
        else canonical_name identity = name

      val native_candidates =
        Proof_Context.consts_of ctxt
        |> Consts.dest
        |> #constants
        |> map_filter
          (fn (identity, (typ, _)) =>
            if requested_identity identity andalso
                not (Symtab.defined by_identity identity) andalso
                not (member (op =)
                  (item_constructor_identities ctxt)
                  identity) andalso
                known_native_constructor ctxt (identity, typ)
            then
              native_case_constructor_info ctxt
                (Const (identity, typ))
            else NONE)
    in
      sugar_candidates @ native_candidates
    end

  fun missing_literal_notation_guidance name =
    "\nMissing exact micro_rust_notation (literal) declaration for " ^
      quote name ^
      "; declare the intended backend under this name or qualify the constructor path."

  fun ambiguity_error role name pos has_exact_registration candidates =
    error
      ("urust_expr: " ^ role ^ " " ^ quote name ^
        " is ambiguous; candidates: " ^
        space_implode ", "
          (sort_strings
            (map constructor_identity candidates)) ^
        (if has_exact_registration
         then ""
         else missing_literal_notation_guidance name) ^
        Position.here pos)

  fun distinct_constructor_infos infos =
    fold
      (fn info => fn seen =>
        if List.exists (fn other => same_constructor_info (info, other)) seen
        then seen else info :: seen)
      infos []

  fun exact_literal_registrations ctxt path =
    Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral
      (render_path path)

  fun registered_constructor_candidates ctxt
      (Constructor_Resolver {registered_by_identity, ...}) registrations =
    let
      val constructors =
        map #2 (Symtab.dest registered_by_identity)

      fun backend_matches backend =
        let
          val sugar_matches =
            filter
              (fn info =>
                Term.aconv_untyped
                  (backend, constructor_term info))
              constructors
        in
          if null sugar_matches
          then the_list (native_case_constructor_info ctxt backend)
          else sugar_matches
        end

      fun registered_matches entry =
        backend_matches
          (identifier_leaf (#hol_term entry))
    in
      registrations
      |> maps registered_matches
      |> distinct_constructor_infos
    end

  fun item_constructor_candidates ctxt
      (Constructor_Resolver {registered_by_identity, ...}) entry =
    let
      val backend = identifier_leaf (I.constructor_term entry)
      val sugar_matches =
        map #2 (Symtab.dest registered_by_identity)
        |> filter
          (fn info =>
            Term.aconv_untyped
              (backend, constructor_term info))
      val candidates =
        if null sugar_matches
        then the_list (native_case_constructor_info ctxt backend)
        else sugar_matches
    in distinct_constructor_infos candidates end

  fun classify_registered_literal ctxt resolver path =
    (case exact_item_constructor ctxt path of
       SOME _ => Registered_Constructor_Literal
     | NONE =>
         (case exact_literal_registrations ctxt path of
            [] =>
              if is_qualified_path path
              then
                qualified_registration_error
                  Micro_Rust_Names.NLiteral path
                  (render_path path) (path_position path)
              else Unregistered_Literal
          | registrations =>
              if is_primitive_path path
              then Registered_Value_Literal
              else if null
                  (registered_constructor_candidates ctxt resolver
                    registrations)
              then Registered_Value_Literal
              else Registered_Constructor_Literal))

  fun resolve_constructor ctxt resolver path =
    if is_primitive_path path then NONE
    else
    let
      val name = render_path path
      val pos = #2 (path_terminal path)
      val item = exact_item_constructor ctxt path
      val registrations = exact_literal_registrations ctxt path
      val registered =
        registered_constructor_candidates ctxt resolver registrations
      val candidates =
        (case item of
           SOME entry =>
             (reject_item_generics path;
              item_constructor_candidates ctxt resolver entry)
         | NONE =>
             if null registrations
             then
               if is_qualified_path path
               then
                 qualified_registration_error
                   Micro_Rust_Names.NLiteral path
                   name (path_position path)
               else
                 (generated_basename_error
                    ctxt "constructor pattern" path;
                  reject_intermediate_generics path;
                  case segment_generic_args
                      (final_segment path) of
                    NONE =>
                      constructor_candidates ctxt resolver name
                  | SOME (Generic_Args (_, generic_pos)) =>
                      error
                        ("urust_expr: generic constructor paths require an exact literal registration" ^
                          Position.here generic_pos))
             else registered)
    in
      (case candidates of
         [] =>
           (case item of
              SOME _ =>
                error
                  ("urust_expr: generated Rust item " ^
                    quote name ^
                    " is not authenticated by native constructor metadata" ^
                    Position.here pos)
            | NONE => NONE)
       | [info] => SOME info
       | ambiguous =>
           ambiguity_error "constructor pattern" name pos
             (is_some item orelse not (null registrations))
             ambiguous)
    end

  fun report_named_term ctxt pos (Const (name, _)) =
        Context_Position.report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) name)
    | report_named_term _ _ _ = ()

  fun report_constructor ctxt path info =
    let
      val name = render_path path
      val pos = #2 (path_terminal path)
      val item = exact_item_constructor ctxt path
      val registrations = exact_literal_registrations ctxt path
      val item_registered =
        (case item of
           SOME entry =>
             Term.aconv_untyped
               (identifier_leaf (I.constructor_term entry),
                constructor_term info)
         | NONE => false)
      val authenticating =
        registrations
        |> filter
            (fn ({hol_term, ...} : Micro_Rust_Names.entry) =>
              Term.aconv_untyped
                (identifier_leaf hol_term, constructor_term info))
        |> sort
            (fn (left : Micro_Rust_Names.entry, right) =>
              int_ord (#serial left, #serial right))
      val selected = try hd authenticating
      val _ =
        if item_registered then
          report_item_constructor ctxt path (the item)
        else if is_some selected
        then report_literal_path_qualifiers ctxt registrations path
        else report_path_qualifiers ctxt path
    in
      if item_registered then ()
      else
        (case selected of
           SOME entry =>
             Micro_Rust_Dispatch.emit_selected_use_markup_at_positions
               ctxt Micro_Rust_Names.NLiteral name entry
               {terminal_pos = pos,
                qualifier_positions = path_qualifier_positions path,
                backend_only_positions = []}
         | NONE => report_named_term ctxt pos (constructor_term info))
    end

  fun report_field ctxt pos selector field =
    (report_named_term ctxt pos selector;
     Option.app (I.defer_field_reference ctxt pos) field)

  fun report_wildcard ctxt pos =
    Context_Position.report_text ctxt pos Markup.typing "wildcard pattern"

  fun report_struct_label ctxt (_, pos) =
    Context_Position.report_text ctxt pos Markup.typing
      "struct expression label"

  fun report_struct_labels ctxt path fields =
    let
      fun label (SE_Field (name, pos, _)) = (name, pos)
      fun report_alias aliases field =
        let val (name, pos) = label field in
          (case AList.lookup (op =) aliases name of
             SOME source_field =>
               (Context_Position.report_text ctxt pos Markup.typing
                  "generated Rust field";
                report_field ctxt pos
                  (I.field_selector source_field)
                  (SOME source_field))
           | NONE => report_struct_label ctxt (name, pos))
        end
    in
      (case exact_item_constructor ctxt path of
         SOME entry =>
           let
             val aliases =
               map
                 (fn source_field =>
                   (I.field_rust_name source_field,
                    source_field))
                 (I.constructor_field_entries entry)
           in
           List.app
             (report_alias aliases) fields
           end
       | NONE => List.app (report_struct_label ctxt o label) fields)
    end

  fun literal_value ctxt environment payload =
    (case payload of
       LP_Integer integer =>
         T.integer_value
           (integer_literal_position integer)
           (integer_literal_lexeme integer)
     | LP_Bool (value, _) => if value then T.true_value else T.false_value
     | LP_String (raw, pos) => T.string_value raw pos
     | LP_ValAntiq antiquotation =>
         parse_antiquotation ctxt environment
           (value_antiquotation_source antiquotation))

  fun literal_expression _ _ (LP_Bool (value, _)) =
        T.boolean_expression value
    | literal_expression ctxt environment payload =
        T.literal (literal_value ctxt environment payload)

  datatype struct_candidate =
      Constructor_Candidate of {info: constructor_info, selectors: term list}
    | Record_Candidate of {record_name: string, fields: term list}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info *
          (term * field_reference option *
            Position.T option * ur_pat) list
    | Resolved_Record_Struct of
        string *
          (term * field_reference option *
            Position.T option * ur_pat) list

  (* Struct heads accept either a constructor name or the type name of a single-constructor datatype.
     Records come only from Record.get_info; Ctr_Sugar's record entry belongs to a different lowering
     domain and must not compete with constructor candidates. *)
  fun resolve_struct_constructor ctxt
      (resolver as
        Constructor_Resolver
          {type_fallbacks, record_types, ...})
      head_path =
    let
      val theory = Proof_Context.theory_of ctxt
      val identifier_name = render_path head_path
      val pos = #2 (path_terminal head_path)
      val item = exact_item_constructor ctxt head_path
      val registrations = exact_literal_registrations ctxt head_path
      val qualified = is_qualified_path head_path
      val has_exact_registration =
        is_some item orelse not (null registrations)
      val _ =
        if qualified andalso not has_exact_registration
        then
          qualified_registration_error Micro_Rust_Names.NLiteral
            head_path identifier_name (path_position head_path)
        else ()

      fun name_matches identity =
        if qualified_name identifier_name
        then identity = identifier_name
        else canonical_name identity = identifier_name

      val direct_candidates =
        (case item of
           SOME entry =>
             item_constructor_candidates ctxt resolver entry
         | NONE =>
             if qualified
             then
               registered_constructor_candidates ctxt resolver
                 registrations
             else
               (generated_basename_error
                  ctxt "struct pattern" head_path;
                constructor_candidates ctxt resolver identifier_name))
        |> map
            (fn info =>
              (constructor_identity info,
               Constructor_Candidate
                 {info = info,
                  selectors = constructor_selectors info}))

      val fallback_candidates =
        if qualified orelse is_some item then []
        else
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
        if qualified orelse is_some item then []
        else
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
             (if has_exact_registration
              then ""
              else missing_literal_notation_guidance identifier_name) ^
             Position.here pos))
    end

  fun resolve_struct_pattern ctxt resolver
      (head_path, fields) =
    let
      val head = render_path head_path
      val head_pos = #2 (path_terminal head_path)
      val registrations = exact_literal_registrations ctxt head_path
      val item = exact_item_constructor ctxt head_path
      val _ = reject_intermediate_generics head_path
      val _ =
        (case segment_generic_args (final_segment head_path) of
           NONE => ()
         | SOME (Generic_Args (_, pos)) =>
             if null registrations andalso is_none item
             then
               error
                 ("urust_expr: generic struct-pattern paths require an exact literal registration" ^
                   Position.here pos)
             else ())
      val candidate =
        resolve_struct_constructor ctxt resolver head_path
      val (display_name, selectors) =
        (case candidate of
           Constructor_Candidate {info, selectors} =>
             (the_default head
                (Option.map canonical_name
                  (term_name_of (constructor_term info))),
              selectors)
         | Record_Candidate {record_name, fields} =>
             (canonical_name record_name, fields))

      fun native_selector_entry selector =
        (case term_name_of selector of
           SOME name => (canonical_name name, selector, NONE)
         | NONE =>
             error
               ("urust_expr: unnamed selector in struct metadata for " ^
                 quote display_name ^ Position.here head_pos))

      val selector_entries =
        (case item of
           SOME entry =>
             let
               val aliases = I.constructor_field_entries entry
               val alias_terms = map I.field_selector aliases
             in
               if eq_list (op aconv) (alias_terms, selectors)
               then
                 map
                   (fn source_field =>
                     (I.field_rust_name source_field,
                      I.field_selector source_field,
                      SOME source_field))
                   aliases
               else
                 error
                   ("urust_expr: generated Rust field aliases disagree with native selector metadata for " ^
                     quote head ^
                     Position.here head_pos)
             end
         | NONE => map native_selector_entry selectors)
      val selector_names = map #1 selector_entries

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
        map (fn (name, selector, field_reference) =>
          (case AList.lookup (op =) entries name of
             SOME (pos, pattern) =>
               (selector, field_reference, SOME pos, pattern)
           | NONE =>
               (selector, field_reference,
                NONE, P_Wild Position.none)))
          selector_entries
    in
      (case candidate of
         Constructor_Candidate {info, ...} =>
           Resolved_Constructor_Struct (info, ordered)
       | Record_Candidate {record_name, ...} =>
           Resolved_Record_Struct (record_name, ordered))
    end
end
\<close>

end
