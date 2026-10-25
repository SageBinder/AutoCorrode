theory Parser_Impl_Resolution
  imports
    Parser_Impl_Shallow_Terms
    Parser_Impl_Item_Scope
    Parser_Impl_Imports
    Parser_Impl_Grammar
    Parser_Impl_Trait_Mappings
    Parser_Utils
begin

section\<open> Names, binders, and metadata \<close>

text\<open>
Value lookup preserves lexical binding precedence. Unshadowed scoped const parameters supply
length values; a scoped type parameter used as a value is a positioned error. Associated constants
through a parameter head use its declared trait bounds, while concrete heads prefer exact literal
notations and then compatible registered traits, including aliases, imports and Self. Repeat
lengths use the same contextual constant resolution.

Generated generic calls obtain the current source-specific schemes and instantiate type/const
arguments in declared order. Genuine method and impl-source filters remain authoritative, and
responsible-owner arity, kind and bound failures retain their list or argument positions. The native
notation dispatcher owns final fresh candidate unification, covering, deduplication, ambiguity and
selected-backend navigation. Calls without generic arguments and explicit-only payloads keep their
ordinary behavior. Generic reference events use the lower context-aware reporter, retaining exact
scope records, callbacks and native report order. Sparse generated calls defer positioned source
argument validation until native full-type filtering. Each compatible candidate captures reports
and source/witness observations independently; only the selected candidate commits them.
Concrete source-sensitive impl paths compare expanded source identity with HOL Self. HOL-only
local receivers request an explicit associated spelling rather than recovering erased tags.
\<close>

ML\<open>
signature URUST_RESOLUTION =
sig
  type environment

  val empty_environment: environment
  val allocate_locals:
    Proof.context ->
      environment ->
      (string * Position.T) list ->
      environment
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
  val use_pattern_binder:
    Proof.context -> environment -> string * Position.T -> term option
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
  val global_constant_path_value:
    Proof.context -> environment -> URust_AST.ur_path -> term
  val function_identifier:
    Proof.context -> environment -> string * Position.T -> term
  val function_path:
    Proof.context -> environment -> URust_AST.ur_path -> int -> term
  val generated_struct_function:
    Proof.context -> URust_AST.ur_path -> URust_AST.struct_expr_field list -> term option
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
  val report_struct_constructor:
    Proof.context -> URust_AST.ur_path -> constructor_info -> unit
  type field_reference
  val report_field:
    Proof.context -> Position.T -> term -> field_reference option -> unit

  type resolved_struct_field =
    {selector: term, field_reference: field_reference option,
     source_position: Position.T option,
     pattern: URust_AST.ur_pat, shorthand: bool}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info *
          resolved_struct_field list
    | Resolved_Record_Struct of
        string *
          resolved_struct_field list

  val resolve_struct_pattern:
    Proof.context -> constructor_resolver ->
      URust_AST.ur_path * URust_AST.struct_field list ->
      resolved_struct_pattern
end
\<close>

text\<open>
Resolution owns every effectful name operation: binder IDs and navigation, local shadowing,
antiquotation capture, notation dispatch, constructor reports, and struct metadata. Its environment is
abstract so downstream modules cannot depend on the underlying binder record. It also resolves the
heads of impl-related paths: \<open>Self\<close> inside an impl member, type aliases and imported types
name their target, a path call \<open>T::f(..)\<close> follows Rust's rule for several inherent impls
(select the instance with \<open>T::<A>::f\<close>, \<open>Self\<close> or an alias), and a direct call never
reaches a method entry.
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
    while reporting their definitions. Closure formals use it for the binders of their complete
    formal list.
    allocate_expression_arguments and allocate_function_parameters reject duplicate named
    parameters through the same validation path. Named slots allocate the supplied type, enter the
    lexical environment with direct-call precedence, and return a source-ordered Term.lambda_name
    operation that names the abstraction by its source spelling. A `_` slot enters no environment and returns a typed anonymous Abs operation instead;
    repeated and mixed wildcards therefore retain their type slots and abstraction order without
    becoming resolvable names. Untyped expression clients supply dummy types for inference; typed
    clients supply argument or parameter types from the complete declaration type. A nested ordinary
    binder with the same name removes the declaration-argument precedence marker while shadowing the
    outer argument. use_local performs a positioned lookup, reports a bound reference on success, and
    returns NONE without fallback resolution. use_pattern_binder returns the same local but reports
    its entity identity with Position.none as the destination: pattern declarations, including later
    alternative occurrences, retain shared highlighting without becoming hyperlinks. lookup_local
    performs the same lexical lookup without reporting. Single-local allocation and the generic
    binder records are private implementation details.

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
    otherwise lifts literal_value. literal_identifier_value resolves a shadowing import, then
    locals, before NLiteral notation/HOL fallback without lifting, and literal_identifier lifts
    that result. A single-segment
    direct NFunction call head resolves a shadowing block import, then every lexical local, before an
    exact registration or HOL fallback. Qualified call paths and method names never select lexical
    locals. In the NField role an exact registered notation wins, otherwise a context-fixed or
    constant HOL lens is required.
    ordinary_identifier_value resolves a lexical local before ordinary HOL parsing and deliberately
    performs no micro_rust_notation lookup; log-data identifiers use this path. function_identifier
    returns the selected unlifted direct callee. apply_generic_arguments parses the retained
    restricted generic argument sources in the current lexical environment and applies them to an
    already-resolved term from left to right.
    global_constant_path_value is the stricter array-repeat-length route: it rejects lexical locals
    that no block import shadows,
    accepts exact literal registrations whose selected backend may depend on the proof context,
    direct fixed parameters, or genuine unqualified HOL constants. Qualified paths require exact
    literal registration, and the route never creates an unresolved Free.
    registered_function performs an exact registered NFunction lookup without imposing a caller
    naming policy. registered_macro_path performs the same lookup for the complete spelling including
    `!`, but rejects an unregistered qualified source path through the common call-role diagnostic.
    is_nullary_function_path is a report-free ambiguity query used by control-head
    validation: after any import that the shadowing rule selects, lexical locals retain
    direct-call precedence, fixed variables remain value paths, and otherwise an exact registered backend or proper HOL
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
    report_field buffers selector-constant markup and queues an authenticated generated source-field
    reference for replay after complete command checking, with the source field reported last;
    native fields have no source reference.

  - resolve_struct_pattern resolves a struct head as a constructor, a single-constructor datatype
    type name, or a HOL record type. It validates duplicate, unknown, missing, and repeated-rest
    fields, expands shorthand fields, and returns fields in metadata declaration order. Each ordered
    field carries its selector, an optional authenticated generated source-field identity, and
    (SOME source_position, pattern) when written or
    (NONE, P_Wild Position.none) when supplied by `..`.
    Resolved_Constructor_Struct carries constructor_info plus those fields;
    Resolved_Record_Struct carries the qualified record type name plus those fields. Policy for
    rejecting the currently unsupported HOL-record lowering belongs to URust_Patterns.

  - Rust imports. Before its ordinary route, every value, call, struct-expression, pattern,
    struct-pattern, repeat-length and report-free classification consumer consults
    URust_Import_Scope. A single-segment name bound in the requested namespace, or a multi-segment
    path whose head is a type-namespace import of a type, is rewritten to its canonical
    exact key; the same head routes rewrite a leading Self inside an impl member and a type alias
    head (unless the written key has an exact registration, D133), both carrying the instance they
    fix, which selects impls for associated-function path calls and instantiates constructors in
    every other role: the bound segment becomes the key segments, with the occurrence position and
    generic arguments on the final key segment and no position on synthetic prefix segments. The
    canonical path then follows only the exact branch of the owning resolver; a binding unusable
    in the requested role is rejected without any lexical, HOL, basename or unqualified fallback.
    For value and call occurrences, Rust block scoping decides between an import and a lexical
    local or declaration argument of the same name: a block's use items take effect at its entry,
    so the import wins exactly when its frame is deeper than the frames enclosing the local's
    binding. Locals bound inside the importing block, and every local against chunk
    aliases, win instead.
    Struct heads use the type namespace, extended to single-segment value bindings of the notation
    role the existing struct syntax uses. report_struct_constructor is report_constructor for
    struct-pattern heads. Method names, fields, macros and log-data identifiers are not imported.
    After the canonical reports, each alias occurrence queues a reference to its import
    declaration.

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
  structure S = URust_Import_Scope

  type field_reference = I.field_entry
  type local_table = Parser_Utils.var_info Symtab.table
  (* local_frames records, per lexical local, the number of import frames enclosing its binding.
     Frames are pushed at block entry before any binder of the block, so every visible local was
     bound in a prefix of the current frame list. *)
  type environment =
    {locals: local_table,
     local_frames: int Symtab.table}

  val variable_entity_kind = "urust_var"
  val report_reference = Parser_Utils.report_ref variable_entity_kind
  val bind_local = Parser_Utils.bind_var variable_entity_kind
  val bind_typed_local = Parser_Utils.bind_typed_var variable_entity_kind

  val empty_environment =
    {locals = Symtab.empty,
     local_frames = Symtab.empty}
  val anonymous_abstraction = Parser_Utils.anon_abs

  fun parse_antiquotation ctxt
      ({locals, ...} : environment) source =
    Parser_Utils.parse_antiq variable_entity_kind ctxt locals source

  (* Self is a keyword naming the implementing type; Rust rejects it as a binding name. *)
  fun reject_self_binder (name, pos) =
    if name = "Self" then
      error ("urust: Self is a keyword and cannot name a binding" ^ Position.here pos)
    else ()

  fun bind_ordinary_local ctxt
      ({locals, local_frames} : environment)
      (binding as (name, _)) =
    let
      val _ = reject_self_binder binding
      val (free, locals') = bind_local ctxt locals binding
    in
      (free,
       {locals = locals',
        local_frames = Symtab.update (name, S.frame_depth ctxt) local_frames})
    end

  fun bind_declaration_argument ctxt
      ({locals, local_frames} : environment)
      (parameter as (binding as (name, _), _)) =
    let
      val _ = reject_self_binder binding
      val (free, locals') = bind_typed_local ctxt locals parameter
    in
      (free,
       {locals = locals',
        local_frames = Symtab.update (name, S.frame_depth ctxt) local_frames})
    end

  fun allocate_locals ctxt environment signatures =
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
        #2 (bind_ordinary_local ctxt env binding)
    in fold allocate signatures environment end

  (* Self in a pattern position is a path, never a binder: self_pattern gives the type of the unit
     value it matches, or rejects it as a path pattern. The parameter allocators are completed
     with that resolution at the end of this structure; closure formals are patterns
     (URust_Patterns.prepare_closure_formals), which resolve Self as a path directly. *)
  fun gen_allocate_parameters self_pattern command role ctxt environment parameters =
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
                URust_Report_Transaction.report_text ctxt pos Markup.typing
                  ("uRust " ^ role ^ " :: " ^ Syntax.string_of_typ ctxt T)
              val (abstraction, env') =
                if name = "_" then
                  ((fn body => Abs (Name.uu, T, body)), env)
                else if name = "Self" then
                  let
                    val pattern_type = self_pattern ctxt pos
                    val _ =
                      if can (Sign.typ_unify (Proof_Context.theory_of ctxt) (T, pattern_type))
                          (Vartab.empty, Int.max (maxidx_of_typ T, maxidx_of_typ pattern_type) + 1)
                      then ()
                      else
                        error
                          ("urust_expr: mismatched types: the pattern Self has type " ^
                            quote (Syntax.string_of_typ ctxt pattern_type) ^
                            ", but the " ^ role ^ " has type " ^
                            quote (Syntax.string_of_typ ctxt T) ^ Position.here pos)
                  in ((fn body => Abs (Name.uu, T, body)), env) end
                else
                  let
                    val (free, env') =
                      bind_declaration_argument ctxt env parameter
                  in ((fn body => Term.lambda_name (name, free) body), env') end
            in allocate rest env' (abstraction :: abstractions) end
    in allocate parameters environment [] end


  fun use_local ctxt environment (name, pos) =
    (case Symtab.lookup (#locals environment) name of
       SOME {free, def_pos, id} =>
         (report_reference ctxt id (name, def_pos) pos; SOME free)
     | NONE => NONE)

  fun use_pattern_binder ctxt environment (name, pos) =
    (case Symtab.lookup (#locals environment) name of
       SOME {free, id, ...} =>
         (report_reference ctxt id (name, Position.none) pos; SOME free)
     | NONE => NONE)

  fun lookup_local environment name =
    Option.map #free (Symtab.lookup (#locals environment) name)

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
          List.app (URust_Report_Transaction.report ctxt pos)
            (Syntax_Phases.markup_free ctxt fixed)
      in T.source_position pos (Free (fixed, dummyT)) end
    else
      let
        val source =
          Parser_Lex_Util.positioned_content_source name
            (Position.no_range_position pos)
        val term =
          URust_Report_Transaction.native ctxt
            (fn read_ctxt => Syntax.parse_term read_ctxt (Syntax.implode_input source))
      in
        (case identifier_leaf term of
           Const (constant_name, _) =>
             let
               val consts = Proof_Context.consts_of ctxt
               val constant_type = Consts.the_constraint consts constant_name
               val _ =
                 List.app (URust_Report_Transaction.report ctxt pos)
                   [Name_Space.markup (Consts.space_of consts) constant_name,
                    Markup.const]
             in
               URust_Report_Transaction.report_text ctxt pos Markup.typing
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

  (* Registered notation witnesses stay source-spelled Frees for the marker's own witness policy.
     Lexical shadowing is decided before this point, and parser binders never capture them. *)
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

  fun scope_parameter ctxt name =
    (case URust_Type_Mappings.generic_scope ctxt of
       NONE => NONE
     | SOME {parameters} =>
         find_first (fn ({rust, ...}: URust_Type_Mappings.generic_parameter) =>
           rust = name) parameters)

  fun report_scope_parameter ctxt pos
      (parameter as {rust, hol, ...}: URust_Type_Mappings.generic_parameter) =
    (Micro_Rust_Semantic_Navigation.defer_report ctxt pos Markup.tfree;
     Micro_Rust_Semantic_Navigation.defer_report_text ctxt pos Markup.typing
       (rust ^ " = " ^ Syntax.string_of_typ (Config.put show_sorts true ctxt) (TFree hol));
     URust_Type_Mappings.report_generic_reference ctxt parameter pos)

  fun scope_value ctxt (name, pos) =
    Option.map
      (fn parameter as {kind, hol, ...}: URust_Type_Mappings.generic_parameter =>
        (report_scope_parameter ctxt pos parameter;
         case kind of
           Type_Parameter =>
             error ("urust: type parameter " ^ name ^ " cannot be used as a value" ^
               Position.here pos)
         | Const_Parameter =>
             let
               val length_type = TFree hol
               val length = Const (\<^const_name>\<open>len_of\<close>,
                 Term.itselfT length_type --> HOLogic.natT) $ Logic.mk_type length_type
             in T.source_position pos
               (Const (\<^const_name>\<open>of_nat\<close>, HOLogic.natT --> \<^typ>\<open>64 word\<close>) $ length)
             end))
      (scope_parameter ctxt name)

  fun ordinary_identifier_value ctxt environment
      (identifier as (name, pos)) =
    let
      val _ =
        URust_Report_Transaction.report_text ctxt pos Markup.typing
          "log data identifier"
    in
      (case use_local ctxt environment identifier of
         SOME local_term => local_term
       | NONE =>
           (case scope_value ctxt identifier of
              SOME value => value
            | NONE => resolve_hol_identifier ctxt name pos))
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
          let
            val typ = if typ = dummyT then
                Sign.the_const_type (Proof_Context.theory_of ctxt) identity
              else typ
          in (case Case_Translation.lookup_by_constr_permissive ctxt
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
               end) end
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
    URust_Report_Transaction.report ctxt
      (#2 (segment_identifier segment)) Markup.free

  fun notation_role Micro_Rust_Names.NLiteral = "literal"
    | notation_role Micro_Rust_Names.NFunction = "call"
    | notation_role Micro_Rust_Names.NField = "field"

  fun report_registered_path_segment ctxt kind name segment =
    let
      val pos = #2 (segment_identifier segment)
    in
      URust_Report_Transaction.report_text ctxt pos Markup.typing
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
          List.app (URust_Report_Transaction.report ctxt pos)
            [Name_Space.markup type_space family, Markup.keyword3]
        end
    in
      if is_primitive_path path then
        List.app
          (report_registered_path_segment ctxt Micro_Rust_Names.NLiteral name)
          qualifiers
      else
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
          List.app (Micro_Rust_Semantic_Navigation.defer_report ctxt pos)
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
      val _ = Micro_Rust_Semantic_Navigation.defer_report ctxt pos Markup.keyword3
      val _ =
        (case constructor of
           Const (name, _) =>
             Micro_Rust_Semantic_Navigation.defer_report ctxt pos
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

  fun item_constructor_instance ctxt path entry constructor =
    let
      val groups = map_filter segment_generic_args (path_segments path)
      val _ = if length groups <= 1 then () else
        error ("urust_expr: generated constructor accepts one generic argument group" ^ Position.here (path_position path))
      fun argument (Generic_Arg (_, source)) =
        URust_Parser.parse_generic_argument_source ctxt source
    in case groups of [] => constructor | [Generic_Args (arguments, _)] =>
      URust_Type_Mappings.instantiate_constructor ctxt (I.constructor_rust_type entry)
        (map argument arguments) constructor
    | _ => raise Match end

  fun item_has_generics path =
    not (null (map_filter segment_generic_args (path_segments path)))

  fun fresh_item_instance path term =
    term
    |> (if item_has_generics path then I else Term.map_types Logic.varifyT_global)
    |> Term.map_types (Logic.incr_tvar (serial ()) #> Type_Infer.paramify_vars)

  (* A head that fixes an instance (Self, a type alias, an imported alias) supplies the HOL type
     that the constructor builds: the scheme's result type is matched against it, so the head's
     generic arguments, including those of the alias expansion, instantiate the constructor in
     every role. Inference holes of omitted alias arguments stay open. *)
  fun instantiated_scheme ctxt path entry instance =
    let
      val native =
        I.constructor_scheme entry |> Term.map_types (Logic.varifyT_global o Type.legacy_freeze_type)
      val result = body_type (fastype_of native)
      val substitution =
        Sign.typ_match (Proof_Context.theory_of ctxt) (result, instance) Vartab.empty
          handle Type.TYPE_MATCH =>
            error
              ("urust_expr: generated Rust constructor " ^ quote (render_path path) ^
                " does not construct " ^ quote (Syntax.string_of_typ ctxt instance) ^
                Position.here (path_position path))
    in Term.map_types (Envir.subst_type substitution) native end

  fun source_constructor_scheme ctxt (SOME instance) path entry =
        instantiated_scheme ctxt path entry instance
    | source_constructor_scheme ctxt NONE path entry =
        item_constructor_instance ctxt path entry
          (I.constructor_scheme entry |> Term.map_types Type.legacy_freeze_type)

  fun source_constructor ctxt (SOME instance) path entry =
        instantiated_scheme ctxt path entry instance
    | source_constructor ctxt NONE path entry =
        if not (item_has_generics path) then I.constructor_term entry
        else fresh_item_instance path (source_constructor_scheme ctxt NONE path entry)

  fun item_value_path ctxt instance path entry =
    let

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
        (source_constructor ctxt instance path entry)
    end

  fun generic_sources (Generic_Args (arguments, _)) =
    map generic_argument_source arguments

  fun call_marker term =
    (case Micro_Rust_Dispatch.dest_marker_untyped term of
       SOME ((Micro_Rust_Names.NFunction, name, positions, filters), _) =>
         SOME (name, positions, filters)
     | _ =>
         (case term of
            left $ right =>
              (case call_marker left of NONE => call_marker right | marker => marker)
          | Abs (_, _, body) => call_marker body
          | _ => NONE))

  fun source_scheme ctxt ({serial, ...}: Micro_Rust_Names.entry) =
    URust_Type_Mappings.generic_scheme_for_source ctxt serial

  fun source_slots ctxt ({serial, ...}: Micro_Rust_Names.entry) =
    URust_Type_Mappings.generic_source_scheme_for_source ctxt serial

  fun generated_generic_entries ctxt filters name =
    Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name
    |> Micro_Rust_Names.eligible_entries ctxt filters
    |> filter (fn entry as {serial, ...} =>
        Micro_Rust_Names.is_automatic_serial (Context.Proof ctxt) serial andalso
          is_some (source_slots ctxt entry))

  fun reject_mixed_generic_key ctxt filters name generated pos =
    let
      val explicit = Micro_Rust_Names.registrations ctxt Micro_Rust_Names.NFunction name
        |> Micro_Rust_Names.eligible_entries ctxt filters
        |> exists (fn {serial, ...} =>
            not (Micro_Rust_Names.is_automatic_serial (Context.Proof ctxt) serial))
      val covered = exists (not o Micro_Rust_Names.is_automatic ctxt) generated
    in
      if explicit orelse covered then
        error ("urust: generic arguments are ambiguous on " ^ name ^
          "; the key has generated functions and explicit call notations" ^ Position.here pos)
      else ()
    end

  fun generic_count_error name count pos =
    error ("urust: wrong number of generic arguments for " ^ name ^
      ": supplied " ^ string_of_int count ^ Position.here pos)

  fun bare_generic_type (Group_Type (typ, _)) = bare_generic_type typ
    | bare_generic_type (Path_Type ([Rust_Type_Path_Segment (name, pos, NONE, _)], _)) =
        SOME (name, pos)
    | bare_generic_type _ = NONE

  fun hol_generic_type (Group_Type (typ, _)) = hol_generic_type typ
    | hol_generic_type (HOL_Type_Source _) = true
    | hol_generic_type _ = false

  fun prepared_generic_argument ctxt argument =
    let
      fun type_argument typ =
        (case Option.mapPartial (fn (name, pos) =>
            Option.map (fn parameter => (parameter, pos)) (scope_parameter ctxt name))
            (bare_generic_type typ) of
           SOME (parameter as {kind = Const_Parameter, hol, ...}, pos) =>
             (report_scope_parameter ctxt pos parameter;
              (SOME Const_Parameter, SOME (TFree hol), NONE, pos))
         | SOME ({kind = Type_Parameter, ...}, pos) =>
             (SOME Type_Parameter, NONE, SOME typ, pos)
         | NONE =>
             (if hol_generic_type typ then NONE else SOME Type_Parameter,
              NONE, SOME typ, rust_type_position typ))
    in
      (case argument of
         Rust_Type_Argument typ => type_argument typ
       | Rust_Numeric_Argument integer =>
           let
             val pos = integer_literal_position integer
             val _ = if is_none (integer_literal_suffix_position integer) then ()
               else error ("urust: const arguments must be unsuffixed integer literals" ^
                 Position.here pos)
             val value = case Parser_Utils.read_unsigned_integer (integer_literal_lexeme integer) of
                 SOME value => value
               | NONE => error ("urust: invalid complete const argument" ^ Position.here pos)
             val typ = URust_Report_Transaction.native ctxt
               (fn read_ctxt => Syntax.read_typ read_ctxt (string_of_int value))
           in (SOME Const_Parameter, SOME typ, NONE, pos) end
       | Rust_Lifetime_Argument (Rust_Lifetime (_, pos)) =>
           error ("urust: omit lifetime arguments on generated functions" ^ Position.here pos)
       | Rust_Associated_Type_Argument (_, pos, _) =>
           error ("urust: associated type arguments are not supported on generated functions" ^
             Position.here pos)
       | Rust_Const_Expression_Argument source =>
           error ("urust: const expression arguments are not supported on generated functions" ^
             Position.here (Input.pos_of source)))
    end

  fun sparse_generated_arguments ctxt name filters generated
      (Generic_Args (arguments, pos)) function =
    let
      val _ = reject_mixed_generic_key ctxt filters name generated pos
      val _ = if exists (fn entry => length (the (source_slots ctxt entry)) = length arguments)
          generated then () else generic_count_error name (length arguments) pos
      val sources = map (fn argument =>
        let val source = generic_argument_source argument
        in (Input.string_of source, Input.pos_of source) end) arguments
      (* Candidate-specific validation belongs after native receiver/full-type filtering. The
         pending carrier retains the original inputs and positions without inventing witnesses. *)
      val instances = map (fn {serial, ...}: Micro_Rust_Names.entry =>
        {source = serial, arguments = map (fn (_, pos) => (NONE, pos)) sources,
         identities = replicate (length sources) ""}) generated
    in Micro_Rust_Dispatch.with_sparse_generic_arguments
      {instances = instances, pos = pos, pending = SOME sources} function end

  fun generated_generic_arguments ctxt name filters generated
      (Generic_Args (arguments, pos)) function =
    let
      val _ = reject_mixed_generic_key ctxt filters name generated pos
      val count = length arguments
      val counted = filter (fn entry => length (the (source_scheme ctxt entry)) = count) generated
      val _ = if null counted then generic_count_error name count pos else ()
      val parsed = map (URust_Parser.parse_generic_argument_source ctxt o generic_argument_source)
        arguments
      val prepared = map (prepared_generic_argument ctxt) parsed
      fun kind_matches (NONE, _) = true
        | kind_matches (SOME kind, {kind = expected, ...}:
            URust_Type_Mappings.generic_scheme_parameter) = kind = expected
      fun matches entry = forall kind_matches
        (map #1 prepared ~~ the (source_scheme ctxt entry))
      val compatible = filter matches counted
      val _ =
        if null compatible then
          let
            val index = the_default 0 (find_index (fn index =>
              forall (fn entry => not (kind_matches
                (#1 (nth prepared index), nth (the (source_scheme ctxt entry)) index))) counted)
              (0 upto (count - 1)) |> (fn index => if index < 0 then NONE else SOME index))
            val argument_pos = #4 (nth prepared index)
          in error ("urust: generic argument has the wrong type or const kind for " ^ name ^
            Position.here argument_pos) end
        else ()
      val rust_types = map_filter #3 prepared
      val resolved = URust_Type_Mappings.resolve_signature ctxt rust_types
      fun collect (_, SOME typ, _, argument_pos) remaining = ((typ, argument_pos), remaining)
        | collect (_, NONE, SOME _, argument_pos) (typ :: remaining) =
            ((typ, argument_pos), remaining)
        | collect _ _ = raise Fail "uRust generic argument resolution is inconsistent"
      val (types, remaining) = fold_map collect prepared resolved
      val _ = if null remaining then () else raise Fail "unconsumed uRust generic argument types"
      val selected = map #serial compatible |> distinct (op =)
      val kinds = map (Option.map (fn kind => kind = Type_Parameter) o #1) prepared
    in
      function
      |> Micro_Rust_Dispatch.with_generic_source_arguments {sources = selected, kinds = kinds}
        {arguments = types, pos = pos}
    end

  (* Explicit notations keep their leading value payload. Generated generic calls instead carry
     typed occurrence arguments until native per-candidate selection. *)
  fun apply_generic_arguments _ _ function NONE = function
    | apply_generic_arguments ctxt environment function (SOME generic_arguments) =
        (case call_marker function of
           SOME (name, _, filters) =>
             (case generated_generic_entries ctxt filters name of
                [] =>
                  let
                    val entries = Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name
                      |> Micro_Rust_Names.eligible_entries ctxt filters
                    val Generic_Args (_, pos) = generic_arguments
                    val _ = if not (null entries) andalso
                        forall (Micro_Rust_Names.is_automatic ctxt) entries then
                      error ("urust_expr: generic arguments are not supported on generated Rust function paths" ^
                        Position.here pos)
                      else ()
                  in
                    T.apply_parameters (Micro_Rust_Dispatch.exclude_generated_backends function)
                      (map (parse_antiquotation ctxt environment) (generic_sources generic_arguments))
                  end
              | generated =>
                  if exists (fn entry => exists (is_none o #hol) (the (source_slots ctxt entry))) generated
                  then sparse_generated_arguments ctxt name filters generated generic_arguments function
                  else generated_generic_arguments ctxt name filters generated generic_arguments function)
         | NONE =>
             T.apply_parameters (Micro_Rust_Dispatch.exclude_generated_backends function)
               (map (parse_antiquotation ctxt environment) (generic_sources generic_arguments)))

  (* Monomorphic generated functions reject a turbofish. Generic sources are handled after
     call-form filters select the eligible entries; explicit-only sources keep their value payload. *)
  fun reject_generated_function_generics ctxt path =
    (case segment_generic_args (final_segment path) of
       NONE => ()
     | SOME (Generic_Args (_, pos)) =>
         let
           val entries =
             Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction
               (render_path (remove_final_generic_args path))
         in
           if not (null entries) andalso forall (Micro_Rust_Names.is_automatic ctxt) entries andalso
              null (generated_generic_entries ctxt [] (render_path (remove_final_generic_args path)))
           then
             error
               ("urust_expr: generic arguments are not supported on generated Rust function paths" ^
                 Position.here pos)
           else ()
         end)

  fun generic_candidate_transform ctxt
      ({arguments, pos}: Micro_Rust_Dispatch.generic_arguments) selection occurrence_type
      ({name, eligible = genuine, maximal = entries}: Micro_Rust_Dispatch.generic_candidate_sources) =
    let
      val counted = filter (fn entry =>
        (case source_scheme ctxt entry of
           SOME parameters => length parameters = length arguments
         | NONE => false)) entries
      val _ = if null counted andalso is_none selection
        then generic_count_error "generated function" (length arguments) pos
        else ()
      val thy = Proof_Context.theory_of ctxt
      fun type_eligible (entry as {serial, hol_term, ...}: Micro_Rust_Names.entry) =
        let
          val parameters = the (source_scheme ctxt entry)
          val actual_types = map fst arguments
          val groups = distinct (op =) actual_types
          val base_index = fold Term.maxidx_typ actual_types
            (Term.maxidx_typ occurrence_type (Term.maxidx_term hol_term (Variable.maxidx_of ctxt))) + 1
          fun requirement actual =
            (actual_types ~~ parameters)
            |> filter (fn (argument, _) => argument = actual)
            |> maps (snd o #hol o snd)
            |> Sign.minimize_sort thy
          val probes = map_index (fn (index, actual) =>
            (actual, TVar ((Name.internal "urust_generic_diagnostic", base_index + index),
              requirement actual))) groups
          val probe_arguments = map (fn (actual, argument_pos) =>
            (the (AList.lookup (op =) probes actual), argument_pos)) arguments
          val backend = singleton (Variable.polymorphic ctxt) hol_term
          val aligned = URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt
            serial backend probe_arguments
          (* Restore exact supplied types before comparison, including repeated variables and
             deliberate receiver/channel sharing. This diagnostic copy never enters dispatch. *)
          val restore = Term.map_types (Term.typ_subst_atomic (map swap probes))
        in
          (case aligned of
             NONE => false
           | SOME candidate => is_some (Micro_Rust_Dispatch.unify_fresh_and_instantiate ctxt
               occurrence_type (restore candidate)))
        end
      val eligible = filter type_eligible counted
      (* Syntactic selection must not erase the responsible receiver's header. Real filters
         remain authoritative; this ownership comparison consumes no inferred substitution. *)
      fun receiver_matches ({serial, hol_term, ...}: Micro_Rust_Names.entry) =
        if not (Micro_Rust_Names.is_method_only_serial (Context.Proof ctxt) serial) then false
        else
          (case binder_types occurrence_type of
             receiver :: _ =>
               (case binder_types (fastype_of (Micro_Rust_Dispatch.fresh_backend ctxt hol_term)) of
                  backend_receiver :: _ =>
                    can (Type.raw_unify (receiver,
                      Logic.incr_tvar (Term.maxidx_of_typ occurrence_type + 1) backend_receiver))
                      Vartab.empty
                | [] => false)
           | [] => false)
      fun kind_matches (NONE, _) = true
        | kind_matches (SOME is_type, {kind, ...}:
            URust_Type_Mappings.generic_scheme_parameter) =
            is_type = (kind = Type_Parameter)
      fun check_owner ({kinds, ...}: Micro_Rust_Dispatch.generic_source_selection) =
        let
          val owners = filter receiver_matches genuine
          val schemes = map_filter (source_scheme ctxt) owners
          val counted = filter (fn parameters => length parameters = length arguments) schemes
          val compatible = filter (fn parameters => forall kind_matches (kinds ~~ parameters)) counted
        in
          if null owners then ()
          else if null schemes then error
            ("urust_expr: generic arguments are not supported on generated Rust function paths" ^
              Position.here pos)
          else if null counted then generic_count_error name (length arguments) pos
          else if null compatible then
            let
              val index = find_index (fn index =>
                forall (fn parameters => not (kind_matches
                  (nth kinds index, nth parameters index))) counted)
                (0 upto (length arguments - 1))
              val argument_pos = #2 (nth arguments (if index < 0 then 0 else index))
            in error ("urust: generic argument has the wrong type or const kind for " ^ name ^
              Position.here argument_pos) end
          else ()
        end
      val _ = if null eligible then Option.app check_owner selection else ()
      fun supports entry =
        forall (fn ((argument, _), {hol = (_, sort), ...}:
            URust_Type_Mappings.generic_scheme_parameter) =>
          Sign.of_sort thy (argument, sort))
          (arguments ~~ the (source_scheme ctxt entry))
      val compatible = filter supports eligible
      val _ = if not (null eligible) andalso null compatible then
        let
          val requirements = the (source_scheme ctxt (hd eligible))
          val incompatible = filter (fn ((argument, _), {hol = (_, sort), ...}:
              URust_Type_Mappings.generic_scheme_parameter) =>
            not (Sign.of_sort (Proof_Context.theory_of ctxt) (argument, sort)))
            (arguments ~~ requirements)
          val ((argument, argument_pos), {hol = (_, sort), ...}) = hd incompatible
        in error ("urust: generic argument " ^
          Syntax.string_of_typ (Config.put show_sorts true ctxt) argument ^
          " does not satisfy sort " ^ Syntax.string_of_sort ctxt sort ^
          Position.here argument_pos) end
        else ()
    in fn entry as {serial, ...} => fn candidate =>
      if exists (fn compatible => #serial compatible = serial) compatible
      then URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt serial candidate arguments
      else NONE
    end

  val _ = Theory.setup (Micro_Rust_Dispatch.register_generic_candidate_transform
    \<^binding>\<open>urust_generated_function\<close> generic_candidate_transform)

  fun sparse_candidate_transform ctxt
      ({instances, pos, pending}: Micro_Rust_Dispatch.sparse_generic_arguments) occurrence_type
      ({name, eligible = genuine, maximal = entries}: Micro_Rust_Dispatch.generic_candidate_sources) =
    let
      fun selected {serial, ...} = exists (fn {source, ...} => source = serial) instances
      fun native_eligible ({hol_term, ...}: Micro_Rust_Names.entry) =
        is_some (Micro_Rust_Dispatch.unify_and_instantiate ctxt occurrence_type
          (Micro_Rust_Dispatch.fresh_backend ctxt hol_term))
      val eligible = filter (fn entry => selected entry andalso native_eligible entry) entries
      fun parameter_key ({kind, sort, hol, ...}: URust_Type_Mappings.generic_source_parameter) =
        (kind, sort, is_some hol)
      val cache = Unsynchronized.ref []
      fun prepare parameters sources =
        let
          val key = map parameter_key parameters
        in case AList.lookup (op =) (!cache) key of SOME result => result
         | NONE =>
             let
               val result = Exn.capture0 (fn () =>
                 let
                   val _ = if length parameters = length sources then ()
                     else generic_count_error name (length sources) pos
                   val ((resolved, events), reports) = URust_Report_Transaction.capture_isolated
                     (fn () => URust_Type_Mappings.capture_generic_argument_events ctxt
                       (fn observed =>
                         let val parsed = map (fn (text, position) =>
                           URust_Parser.parse_generic_argument_source observed
                             (Parser_Lex_Util.positioned_content_source text position)) sources
                         in URust_Type_Mappings.resolve_source_arguments observed parameters parsed end))
                   fun commit () =
                     (URust_Type_Mappings.replay_generic_argument_events ctxt events;
                      URust_Report_Transaction.replay ctxt reports)
                 in (#arguments resolved, commit) end) ()
               val _ = (case result of Exn.Exn exn =>
                 if Exn.is_interrupt exn then Exn.reraise exn else () | _ => ())
               val _ = cache := (key, result) :: !cache
             in result end
        end
      fun prepared (entry as {serial, ...}: Micro_Rust_Names.entry) =
        (case pending of
           NONE => (case find_first (fn {source, ...} => source = serial) instances of
             SOME {arguments, ...} => Exn.Res (arguments, fn () => ())
           | NONE => raise Fail "missing sparse candidate source")
         | SOME sources => prepare (the (source_slots ctxt entry)) sources)
      val results = map (fn entry => (entry, prepared entry)) eligible
      val successful = map_filter (fn (entry, Exn.Res result) => SOME (entry, result)
        | _ => NONE) results
      fun receiver_matches ({serial, hol_term, ...}: Micro_Rust_Names.entry) =
        Micro_Rust_Names.is_method_only_serial (Context.Proof ctxt) serial andalso
        (case (binder_types occurrence_type, binder_types (fastype_of hol_term)) of
           (receiver :: _, backend_receiver :: _) =>
             can (Type.raw_unify (receiver,
               Logic.incr_tvar (Term.maxidx_of_typ occurrence_type + 1) backend_receiver)) Vartab.empty
         | _ => false)
      val _ = if null successful then
          (case map_filter (fn (_, Exn.Exn exn) => SOME exn | _ => NONE) results of
             exn :: _ => Exn.reraise exn
           | [] => (case find_first receiver_matches genuine of
               NONE => ()
             | SOME owner => (case source_slots ctxt owner of
                 NONE => error ("urust_expr: generic arguments are not supported on generated Rust function paths" ^
                   Position.here pos)
               | SOME parameters => (case pending of
                   NONE => () | SOME sources => ignore (Exn.release (prepare parameters sources))))))
        else ()
    in fn {serial, ...} => fn candidate =>
      (case find_first (fn ({serial = source, ...}, _) => source = serial) successful of
         NONE => NONE
       | SOME (_, (arguments, commit)) => Option.map (fn term => (term, commit))
           (URust_Type_Mappings.instantiate_generic_source_scheme_for_source ctxt serial candidate arguments))
    end

  val _ = Theory.setup (Micro_Rust_Dispatch.register_sparse_generic_candidate_transform
    sparse_candidate_transform)

  fun check_source_inference ctxt entries pos =
    if exists (fn entry => case source_slots ctxt entry of
        SOME slots => exists (is_none o #hol) slots | NONE => false) entries then
      error ("urust: erased generic arguments require explicit source arguments" ^ Position.here pos)
    else ()

  val _ = Theory.setup (Micro_Rust_Dispatch.register_generic_inference_check check_source_inference)

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
      val _ = URust_Report_Transaction.report ctxt pos Markup.free
    in Free (render_path path, dummyT) end

  (* A head route rewrites a source path to its canonical exact key: through an import binding,
     through the Self type of the impl member being elaborated, or through a type alias. The routed
     head segment becomes the canonical key segments: its occurrence position (and, for an import,
     its generic arguments) moves to the final key segment, while synthetic prefix segments have no
     source position and therefore produce no reports. A multi-segment path is routed through its
     head only in the type namespace: an imported generated enum may own the remaining variant
     segment, and every imported mapped type, Self and every type alias the remaining associated
     item segment. A route through a type that fixes an instance carries the selection of that
     instance for associated-function path calls, as a lazily resolved HOL type with its written
     spelling. *)
  (* A selection type, its written spelling, and whether inference holes stand for omitted
     generic arguments. *)
  type selection = {typ: typ, written: string, inferred: bool, source_identity: string option}

  datatype route_origin =
      Import_Origin of S.binding
    | Self_Origin of URust_Type_Mappings.impl_self
    | Alias_Origin of string

  type import_route =
    {origin: route_origin, canonical: ur_path, occurrence: Position.T,
     selection: (unit -> selection) option}

  fun route_instance (SOME ({selection = SOME select, ...}: import_route)) =
        SOME (#typ (select ()))
    | route_instance _ = NONE

  fun canonical_segments key pos arguments =
    let val (prefix, final) = split_last (S.key_segments key) in
      map (fn name => Path_Segment (name, Position.none, NONE)) prefix @
        [Path_Segment (final, pos, arguments)]
    end

  fun import_route binding (UR_Path (head, Path_Segment (_, pos, arguments) :: rest, span)) =
        {origin = Import_Origin binding,
         canonical = UR_Path (head, canonical_segments (#key binding) pos arguments @ rest, span),
         occurrence = pos, selection = NONE}
    | import_route _ (UR_Path (_, [], pos)) =
        error ("urust_expr: internal empty imported path" ^ Position.here pos)

  val same_scope_item = URust_Imports.same_scope_item

  fun no_layout () = make_source_layout Position.none []

  fun generic_argument_types ctxt (Generic_Args (arguments, _)) =
    map (URust_Parser.parse_generic_argument_source ctxt o generic_argument_source) arguments

  fun written_type_name name arguments =
    name ^
      (case arguments of
         NONE => ""
       | SOME (Generic_Args (written, _)) =>
           "<" ^ commas (map (fn Generic_Arg (canonical, _) => canonical) written) ^ ">")

  (* The HOL type that a type key with written generic arguments denotes, resolved like a
     signature type. A generic type written without arguments selects among all its instances:
     each omitted argument is an inference hole. *)
  fun selection_type ctxt key pos arguments =
    let
      val hole = Rust_Type_Argument (HOL_Type_Source (Input.string "_"))
      val arities =
        (case URust_Type_Mappings.lookup ctxt key of
           SOME entry => URust_Type_Mappings.entry_arities entry
         | NONE => map (K 0) (S.key_segments key))
      val names = S.key_segments key
      val final_index = length names - 1
      fun segment (index, (name, arity)) =
        let
          val written =
            if index = final_index then Option.map (generic_argument_types ctxt) arguments
            else NONE
          val supplied =
            (case written of
               SOME types => SOME types
             | NONE => if arity = 0 then NONE else SOME (replicate arity hole))
        in
          Rust_Type_Path_Segment
            (name, if index = final_index then pos else Position.none, supplied, no_layout ())
        end
      val arities = if length arities = length names then arities else map (K 0) names
      (* The type is positioned at the written head, so resolution errors cite it. *)
      val typ = Path_Type (map_index segment (names ~~ arities), make_source_layout pos [])
      val inferred = is_none arguments andalso List.last arities > 0
      val _ = if inferred andalso (case URust_Type_Mappings.lookup ctxt key of
          SOME entry => not (null (URust_Type_Mappings.entry_erased_parameters entry))
        | NONE => false) then error
        ("urust: source identity requires explicit type arguments" ^ Position.here pos) else ()
      val (resolved, identity) = URust_Type_Mappings.resolve_type_identity ctxt typ
    in (resolved, Option.map URust_Type_Mappings.source_identity_name identity, inferred) end

  (* The canonical nominal key that a type alias key expands to. *)
  fun alias_expansion ctxt key =
    let
      val segments =
        map (fn name => Rust_Type_Path_Segment (name, Position.none, NONE, no_layout ()))
          (S.key_segments key)
    in
      (case URust_Type_Mappings.impl_target_key ctxt (Path_Type (segments, no_layout ())) of
         SOME base => if base <> key then SOME base else NONE
       | NONE => NONE)
    end

  fun self_outside_impl pos =
    error ("urust: Self is only available inside an impl block" ^ Position.here pos)

  (* Self denotes the full Self type of the impl, so a call through it selects the impl's own
     instance without resolving the type again. *)
  (* As in Rust (E0433), `Self` and `self` may only start a path; no later segment can name them,
     whatever a registry holds. Every path role routes through self_route first. *)
  fun reject_late_keyword_segments path =
    (case path_segments path of
       _ :: rest =>
         List.app
           (fn Path_Segment (name, pos, _) =>
             if name = "Self" orelse name = "self" then
               error ("urust_expr: `" ^ name ^ "` in paths can only be used in start position" ^
                 Position.here pos)
             else ())
           rest
     | [] => ())

  fun self_route ctxt path =
    (reject_late_keyword_segments path;
    case path_segments path of
       Path_Segment ("Self", pos, arguments) :: rest =>
         (case URust_Type_Mappings.impl_self ctxt of
            NONE => self_outside_impl pos
          | SOME (self as {canonical_path, self_type, ...}) =>
              let
                val _ =
                  (case arguments of
                     NONE => ()
                   | SOME (Generic_Args (_, generic_pos)) =>
                       error ("urust: Self cannot take generic arguments" ^
                         Position.here generic_pos))
                val UR_Path (head, _, span) = path
              in
                SOME
                  {origin = Self_Origin self,
                   canonical = UR_Path (head, canonical_segments canonical_path pos NONE @ rest, span),
                   occurrence = pos,
                   selection =
                     SOME (fn () => {typ = self_type, written = "Self", inferred = false,
                       source_identity = Option.map URust_Type_Mappings.source_identity_name
                         (URust_Type_Mappings.impl_source_identity ctxt)})}
              end)
     | _ => NONE)

  (* A head that denotes a type through an alias: the alias expands to its nominal target, and the
     alias with its written arguments selects the instance. *)
  fun alias_route ctxt (UR_Path (head, Path_Segment (name, pos, arguments) :: rest, span)) =
        (case alias_expansion ctxt name of
           SOME base =>
             SOME
               {origin = Alias_Origin name,
                canonical = UR_Path (head, canonical_segments base pos NONE @ rest, span),
                occurrence = pos,
                selection =
                  SOME (fn () =>
                    let val (typ, source_identity, inferred) = selection_type ctxt name pos arguments
                    in {typ = typ, written = written_type_name name arguments, inferred = inferred,
                      source_identity = source_identity}
                    end)}
         | NONE => NONE)
    | alias_route _ _ = NONE

  (* An imported type head: a generated enum keeps its variant route; any other mapped type, or a
     type alias, routes its associated items, the alias through its expansion. *)
  fun imported_type_route binding path =
    if exists (S.has_role binding) [S.Generated_Enum, S.Generated_Struct, S.Mapped_Type]
    then SOME (import_route binding path)
    else NONE

  fun imported_head_route ctxt binding
        (path as UR_Path (head, Path_Segment (name, pos, arguments) :: rest, span)) =
        (case alias_expansion ctxt (#key binding) of
           SOME base =>
             SOME
               {origin = Import_Origin binding,
                canonical = UR_Path (head, canonical_segments base pos NONE @ rest, span),
                occurrence = pos,
                selection =
                  SOME (fn () =>
                    let val (typ, source_identity, inferred) = selection_type ctxt (#key binding) pos arguments
                    in {typ = typ, written = written_type_name name arguments, inferred = inferred,
                      source_identity = source_identity}
                    end)}
         | NONE => imported_type_route binding path)
    | imported_head_route _ _ _ = NONE

  (* D133: a written key with an exact call or literal registration resolves as written, so an
     alias head, or an imported type head that is not an enum, routes only paths whose written key
     has none. An imported enum head routes its variants as at the base. *)
  fun exact_written_key ctxt path =
    exists
      (fn key =>
        exists (fn kind => not (null (Micro_Rust_Names.lookups ctxt kind key)))
          [Micro_Rust_Names.NFunction, Micro_Rust_Names.NLiteral])
      (distinct (op =) [render_path path, render_path (remove_final_generic_args path)])

  fun head_import_route ctxt path =
    (case self_route ctxt path of
       SOME route => SOME route
     | NONE =>
    (case path_segments path of
       Path_Segment (name, pos, _) :: _ :: _ =>
         (case S.lookup ctxt S.Type_Namespace name of
            NONE => if exact_written_key ctxt path then NONE else alias_route ctxt path
          | SOME binding =>
              (S.require_available pos binding;
               if not (S.has_role binding S.Generated_Enum) andalso exact_written_key ctxt path
               then NONE
               else
               case imported_head_route ctxt binding path of
                 SOME route => SOME route
               | NONE =>
                   error
                     ("urust_expr: imported " ^ quote name ^ " (" ^ quote (#key binding) ^
                       ") is not a generated enum and cannot qualify a path" ^ Position.here pos)))
     | _ => NONE))

  (* A single-segment struct head may also name a struct through a type alias, as in Rust; values,
     calls and patterns cannot name a tuple or unit struct through one. *)
  fun namespace_import_route ctxt namespace path =
    if is_primitive_path path then NONE
    else
      (case self_route ctxt path of
         SOME route => SOME route
       | NONE =>
      (case path_segments path of
         [Path_Segment (name, pos, _)] =>
           (case S.lookup ctxt namespace name of
              SOME binding => (S.require_available pos binding; SOME (import_route binding path))
            | NONE =>
                if namespace = S.Type_Namespace andalso not (exact_written_key ctxt path)
                then alias_route ctxt path
                else NONE)
       | _ => head_import_route ctxt path))

  (* Rust block scoping for value and call occurrences: the use items of a block take effect at its
     entry. An import therefore shadows a lexical local, including a declaration argument, exactly
     when its frame is deeper than the frames enclosing the local's binding; locals bound inside the
     importing block, and every local against chunk aliases, win. The comparison
     precedes availability checks, so a shadowed unavailable binding never rejects. *)
  fun import_shadows_local ctxt ({local_frames, ...} : environment) namespace name =
    (case Symtab.lookup local_frames name of
       NONE => true
     | SOME local_depth =>
         if local_depth > S.frame_depth ctxt then
           raise Fail ("uRust local " ^ quote name ^ " was bound under an inactive import frame")
         else
           (case S.lookup_scoped ctxt namespace name of
              SOME (_, import_depth) => import_depth > local_depth
            | NONE => false))

  (* Self is a keyword, never a lexical local. *)
  fun value_import_route ctxt environment path =
    (case self_route ctxt path of
       SOME route => SOME route
     | NONE =>
    (case path_segments path of
       [Path_Segment (name, _, _)] =>
         if import_shadows_local ctxt environment S.Value_Namespace name
         then namespace_import_route ctxt S.Value_Namespace path
         else NONE
     | _ => namespace_import_route ctxt S.Value_Namespace path))

  val pattern_import_route = fn ctxt => namespace_import_route ctxt S.Value_Namespace

  (* Struct heads resolve in the type namespace, as in Rust. The uRust struct-call and literal-struct
     registrations are exact notation keys, which imports place in the value namespace. Such a
     value binding may supply a single-segment head only when its key has the notation role the
     existing struct syntax uses and neither a type-namespace import nor an unimported Rust type
     resolves the head; a value import therefore never changes a Rust struct head. *)
  fun struct_import_route ctxt extension_role path =
    (case namespace_import_route ctxt S.Type_Namespace path of
       SOME route => SOME route
     | NONE =>
         (case path_segments path of
            [Path_Segment (name, _, _)] =>
              if is_some (same_scope_item ctxt S.Type_Namespace name) then NONE
              else
                (case S.lookup ctxt S.Value_Namespace name of
                   SOME binding =>
                     if #available binding andalso S.has_role binding extension_role
                     then namespace_import_route ctxt S.Value_Namespace path
                     else NONE
                 | NONE => NONE)
          | _ => NONE))

  (* The head of a routed path keeps its source token: an import occurrence references its
     import, Self references the entity its target head denotes with the canonical target as
     tooltip, and an alias head references the alias. *)
  fun report_import_use ctxt ({origin, occurrence, ...}: import_route) =
    (case origin of
       Import_Origin binding => S.defer_use_reference ctxt occurrence binding
     | Self_Origin {canonical_path, self_type, report_reference, ...} =>
         (Micro_Rust_Semantic_Navigation.defer_report ctxt occurrence Markup.keyword3;
          (case self_type of
             Type (name, _) => Micro_Rust_Semantic_Navigation.defer_type ctxt occurrence name
           | _ => ());
          report_reference occurrence;
          Micro_Rust_Semantic_Navigation.defer_report_text ctxt occurrence Markup.typing
            ("Self = " ^ canonical_path))
     | Alias_Origin key =>
         (Micro_Rust_Semantic_Navigation.defer_report ctxt occurrence Markup.keyword3;
          Option.app (URust_Type_Mappings.report_reference ctxt occurrence key)
            (URust_Type_Mappings.lookup ctxt key)))

  (* The roles that make a target usable in each import use. A use that its target supports only
     once a later declaration adds one of them reports that declaration as unavailable. *)
  val call_import_roles = [S.Generated_Constructor, S.Call_Notation]
  val value_import_roles = [S.Generated_Constructor, S.Literal_Notation]
  val repeat_length_import_roles = [S.Literal_Notation]

  fun unusable_import ctxt usable role ({origin, canonical, occurrence, ...}: import_route) =
    let
      val target = quote (render_path (item_lookup_path canonical))
      fun unusable written =
        error
          ("urust_expr: " ^ written ^ " resolves to " ^ target ^ ", which cannot be used as " ^
            role ^ Position.here occurrence)
    in
      (case origin of
         Import_Origin binding =>
           if exists (member (op =) usable) (S.pending_roles ctxt binding) then
             S.unavailable_use_error occurrence binding role
           else unusable ("imported name " ^ quote (#alias binding))
       | Self_Origin _ => unusable "the Self path"
       | Alias_Origin key => unusable ("the type alias path " ^ quote key))
    end

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

  fun report_associated_constant ctxt pos (entry: URust_Trait_Mappings.trait_entry) term =
    let
      val navigation = Micro_Rust_Semantic_Navigation.defer_report ctxt pos
      val _ = navigation (Position.entity_markup "urust_trait" (#path entry, #pos entry))
      val _ =
        (case Term.head_of (Term_Position.strip_positions term) of
           Const (name, _) =>
             List.app navigation
               [Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) name,
                Markup.const]
         | _ => ())
      val _ = Micro_Rust_Semantic_Navigation.defer_report_text ctxt pos Markup.typing
        (Syntax.string_of_term (Config.put show_sorts true ctxt) term)
    in T.source_position pos term end

  fun select_associated_constant ctxt head (name, pos) required candidates =
    (case candidates of
       [] =>
         if required then
           error ("urust: no associated constant " ^ name ^ " in the bounds of " ^ head ^
             Position.here pos)
         else NONE
     | [(entry, term)] => SOME (report_associated_constant ctxt pos entry term)
     | _ =>
         error ("urust: multiple applicable associated constants " ^ name ^ " for " ^ head ^
           ": " ^ commas (map (#path o fst) candidates) ^ Position.here pos))

  fun scope_associated_value ctxt path =
    (case path_segments path of
       [Path_Segment (head, head_pos, head_arguments), Path_Segment (name, pos, NONE)] =>
         (case scope_parameter ctxt head of
            SOME (parameter as {kind = Type_Parameter, hol, bounds, ...}) =>
              let
                val _ = case head_arguments of NONE => ()
                  | SOME (Generic_Args (_, arguments_pos)) =>
                      error ("urust: generic parameter " ^ head ^ " takes no generic arguments" ^
                        Position.here arguments_pos)
                val _ = report_scope_parameter ctxt head_pos parameter
                val typ = TFree hol
                fun candidate key =
                  let
                    val entry = the (URust_Trait_Mappings.lookup ctxt key)
                  in Option.map (fn {term, ...} =>
                    let
                      val fresh = Logic.incr_indexes
                        ([], Int.max (Variable.maxidx_of ctxt, Term.maxidx_of_typ typ) + 1) term
                      val Type (_, [Type (_, [domain]), _]) = fastype_of fresh
                      val applied = Term.map_types (Term.typ_subst_atomic [(domain, typ)]) fresh $
                        Logic.mk_type typ
                    in (entry, Proof_Context.cert_term ctxt applied) end)
                    (URust_Trait_Mappings.associated_constant ctxt entry name)
                  end
              in select_associated_constant ctxt head (name, pos) true
                (map_filter candidate (distinct (op =) bounds)) end
          | _ => NONE)
     | _ => NONE)

  fun concrete_associated_value ctxt instance path =
    (case rev (path_segments path) of
       Path_Segment (name, pos, NONE) :: (head as Path_Segment (_, head_pos, arguments)) :: rest =>
         let
           val type_segments = rev (head :: rest)
           val key = space_implode "::" (map (#1 o segment_identifier) type_segments)
           val typ = case instance of SOME typ => SOME typ
             | NONE =>
                 if is_some (URust_Type_Mappings.lookup ctxt key)
                 then SOME (#1 (selection_type ctxt key head_pos arguments))
                 else NONE
         in Option.mapPartial (fn typ =>
           select_associated_constant ctxt key (name, pos) false
             (URust_Trait_Mappings.traits_with_constant ctxt typ name)) typ end
     | _ => NONE)

  fun scoped_path_value ctxt environment path =
    (case scope_associated_value ctxt path of
       SOME value => SOME value
     | NONE =>
         (case path_segments path of
            [Path_Segment (name, pos, NONE)] =>
              if is_some (lookup_local environment name) then NONE else scope_value ctxt (name, pos)
          | _ => NONE))

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
      fun reject_lexical_local () =
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
                   List.app (URust_Report_Transaction.report ctxt pos)
                     [Name_Space.markup
                        (Consts.space_of consts) constant_name,
                      Markup.const]
                 val _ =
                   URust_Report_Transaction.report_text ctxt pos Markup.typing
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
      (case scoped_path_value ctxt environment path of
         SOME value => value
       | NONE =>
      (case value_import_route ctxt environment path of
         SOME (route as {canonical, ...}) =>
           (case exact_registered_path ctxt Micro_Rust_Names.NLiteral canonical of
              SOME registered => (report_import_use ctxt route; registered)
            | NONE =>
                 (case concrete_associated_value ctxt (route_instance (SOME route)) canonical of
                    SOME value => (report_import_use ctxt route; value)
                  | NONE =>
                      unusable_import ctxt repeat_length_import_roles "an array repeat length" route))
       | NONE =>
      (reject_lexical_local ();
      case exact_registered_path ctxt Micro_Rust_Names.NLiteral path of
         SOME registered => registered
       | NONE =>
          (case concrete_associated_value ctxt NONE path of
             SOME value => value
           | NONE =>
           if is_primitive_path path then
             primitive_registration_error
               Micro_Rust_Names.NLiteral path
           else if is_qualified_path path then
             qualified_registration_error
               Micro_Rust_Names.NLiteral path name pos
            else resolve_contextual_or_global ()))))
    end

  fun imported_literal_value ctxt (route as {canonical, ...}: import_route) =
    let
      val value =
        (case exact_item_constructor ctxt canonical of
           SOME entry => item_value_path ctxt (route_instance (SOME route)) canonical entry
         | NONE =>
             (case exact_registered_path ctxt Micro_Rust_Names.NLiteral canonical of
                SOME registered => registered
             | NONE =>
                 (case concrete_associated_value ctxt (route_instance (SOME route)) canonical of
                    SOME value => value
                  | NONE => unusable_import ctxt value_import_roles "a value" route)))
      val _ = report_import_use ctxt route
    in value end

  fun literal_path_value ctxt environment path =
    (case scoped_path_value ctxt environment path of
       SOME value => value
     | NONE =>
    (case value_import_route ctxt environment path of
       SOME route => imported_literal_value ctxt route
      | NONE => source_literal_path_value ctxt environment path))

  and source_literal_path_value ctxt environment path =
    if is_primitive_path path then
      (case exact_registered_path ctxt
          Micro_Rust_Names.NLiteral path of
         SOME registered => registered
       | NONE =>
          (case concrete_associated_value ctxt NONE path of
             SOME value => value
           | NONE =>
           primitive_registration_error
              Micro_Rust_Names.NLiteral path))
    else
    (case path_segments path of
       [Path_Segment (name, pos, NONE)] =>
         (case use_local ctxt environment (name, pos) of
            SOME local_term => local_term
          | NONE =>
              (case exact_item_constructor ctxt path of
                 SOME entry => item_value_path ctxt NONE path entry
               | NONE =>
                   (generated_basename_error ctxt "value" path;
                    resolve_identifier ctxt
                      Micro_Rust_Names.NLiteral name pos)))
     | _ =>
         (case exact_item_constructor ctxt path of
            SOME entry => item_value_path ctxt NONE path entry
          | NONE =>
              (case exact_registered_path ctxt
                  Micro_Rust_Names.NLiteral path of
                 SOME registered => registered
               | NONE =>
                  (case concrete_associated_value ctxt NONE path of
                     SOME value => value
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
                    end))))

  fun literal_path ctxt environment path =
    T.literal (literal_path_value ctxt environment path)

  fun literal_identifier_value ctxt environment (identifier as (name, pos)) =
    (case scoped_path_value ctxt environment (make_single_path identifier) of
       SOME value => value
     | NONE =>
    (case value_import_route ctxt environment (make_single_path identifier) of
       SOME route => imported_literal_value ctxt route
     | NONE =>
         (case use_local ctxt environment identifier of
            SOME local_term => local_term
           | NONE => resolve_identifier ctxt Micro_Rust_Names.NLiteral name pos)))

  fun literal_identifier ctxt environment identifier =
    T.literal (literal_identifier_value ctxt environment identifier)

  (* Rust E0034: the impls of an associated-function key are its owners grouped by identity, so the
     differently typed instances of one locale impl count as one impl. A path call through a type
     that fixes an instance (type-segment generic arguments, Self, an alias or imported type head)
     dispatches only to the path entries of the impls whose Self type unifies with it; without
     one, a key with two or more impls is ambiguous whatever the argument and expected types. *)
  fun unifying_self_types (selected, self_type) =
    let val shifted = Logic.incr_tvar (Term.maxidx_of_typ selected + 1) self_type
    in can (Type.raw_unify (selected, shifted)) Vartab.empty end

  (* One position per impl, in declaration order: identities are allocated in that order. *)
  fun impl_positions owners =
    fold
      (fn {identity, pos, ...} => fn seen =>
        if AList.defined (op =) seen identity then seen else seen @ [(identity, pos)])
      owners []
    |> sort (int_ord o apply2 #1)

  fun associated_selection ctxt route_selection path =
    (case path_segments path of
       segments as _ :: _ :: _ =>
         let
           val UR_Path (head, _, span) = path
           val (type_segments, final as Path_Segment (name, pos, _)) = split_last segments
           val (outer_segments, Path_Segment (type_name, type_pos, type_arguments)) =
             split_last type_segments
           val type_key = space_implode "::" (map (#1 o segment_identifier) type_segments)
           val key = type_key ^ "::" ^ name
           val owners = Micro_Rust_Names.associated_source_functions ctxt key
         in
           if null owners orelse is_primitive_path path then NONE
           else
             let
               val _ =
                 (case find_first (is_some o segment_generic_args) outer_segments of
                    SOME segment =>
                      error
                        ("urust_expr: generic arguments on an intermediate path segment " ^
                          "require an exact registration" ^
                          Position.here (#2 (segment_identifier segment)))
                  | NONE => ())
               val stripped =
                 UR_Path
                   (head,
                    map (fn Path_Segment (n, p, _) => Path_Segment (n, p, NONE)) type_segments @
                      [final],
                    span)
               val impls = impl_positions owners
               val selection : (unit -> selection) option =
                 (case route_selection of
                    SOME select => SOME select
                  | NONE =>
                      Option.map
                        (fn arguments => fn () =>
                          let val (typ, source_identity, _) =
                            selection_type ctxt type_key type_pos (SOME arguments)
                          in {typ = typ, source_identity = source_identity,
                            written = written_type_name type_name (SOME arguments), inferred = false} end)
                        type_arguments)
               fun ambiguous candidates =
                 error
                   ("urust: multiple applicable items in scope: " ^ key ^
                     " is defined in more than one impl; write `" ^ type_key ^
                     "::<\<dots>>::" ^ name ^ "`" ^ Position.here pos ^
                     implode (map (Position.here o #2) candidates))
             in
               (case selection of
                  NONE => if exists (is_some o #source_identity) owners then
                    error ("urust: source identity requires explicit type arguments on " ^ type_key ^
                      Position.here type_pos)
                  else if length impls >= 2 then ambiguous impls else SOME (stripped, [])
                | SOME select =>
                    let
                      val {typ = selected_type, source_identity, written, inferred} = select ()
                      val selected =
                        owners
                        |> filter (fn {self_type, source_identity = owner_source, ...} =>
                            (is_none owner_source orelse owner_source = source_identity) andalso
                            unifying_self_types (selected_type, self_type))
                        |> map #identity |> distinct (op =)
                    in
                      if null selected then
                        error
                          ("urust: no associated function " ^ name ^ " in impls of " ^ written ^
                            Position.here pos)
                      (* Omitted generic arguments of a type head leave the instance open. *)
                      else if inferred andalso length selected >= 2 then
                        ambiguous (filter (fn (identity, _) => member (op =) selected identity) impls)
                      else SOME (stripped, [Micro_Rust_Names.Only_Sources selected])
                    end)
             end
         end
     | _ => NONE)

  (* An exact call registration seen through backend filters: a key without an eligible entry
     behaves as unregistered. *)
  fun exact_registered_call ctxt filters path =
    if Micro_Rust_Names.has_eligible_entries ctxt filters Micro_Rust_Names.NFunction
        (render_path path)
    then
      Option.map
        (fn registered =>
          if null filters then registered
          else Micro_Rust_Dispatch.restrict_backends filters registered)
        (exact_registered_path ctxt Micro_Rust_Names.NFunction path)
    else NONE

  (* A direct call does not reach the method entries of impl members. *)
  fun call_filters direct = if direct then [Micro_Rust_Names.Exclude_Method_Only] else []

  fun registered_call ctxt environment direct route_selection path =
    (case associated_selection ctxt route_selection path of
       SOME (stripped, selection) =>
         let val base = remove_final_generic_args stripped in
           Option.map
             (fn registered =>
               (reject_generated_function_generics ctxt stripped;
                apply_generic_arguments ctxt environment registered
                  (segment_generic_args (final_segment stripped))))
             (exact_registered_call ctxt (call_filters direct @ selection) base)
         end
     | NONE => exact_registered_call ctxt (call_filters direct) path)

  fun method_only_key ctxt name =
    not (null (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name)) andalso
      not (Micro_Rust_Names.has_eligible_entries ctxt [Micro_Rust_Names.Exclude_Method_Only]
        Micro_Rust_Names.NFunction name)

  (* The associated paths that register the backends of a bare method key, for the hint. *)
  fun method_paths ctxt name =
    let
      val backends =
        map (identifier_leaf o #hol_term) (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name)
      fun same_backend ({hol_term, ...}: Micro_Rust_Names.entry) =
        exists (fn backend => Term.aconv_untyped (identifier_leaf hol_term, backend)) backends
    in
      Micro_Rust_Names.dump ctxt
      |> map_filter (fn (kind, key, entry) =>
          if kind = Micro_Rust_Names.NFunction andalso key <> name andalso
             String.isSuffix ("::" ^ name) key andalso same_backend entry
          then SOME key else NONE)
      |> distinct (op =) |> sort_strings
    end

  (* A key whose every entry is a method entry is unregistered for a direct call: an existing HOL
     constant or fixed variable of that name is called; otherwise the call is rejected with a
     hint naming the method call forms. *)
  fun method_only_call ctxt name pos =
    let
      val term = resolve_hol_identifier ctxt name pos
      val paths =
        (case method_paths ctxt name of
           [] => ["T::" ^ name]
         | paths => paths)
      val hint =
        name ^ " is a method; call it as `x." ^ name ^ "(..)` or " ^
          space_implode " or " (map (fn path => "`" ^ path ^ "(x, ..)`") paths)
    in
      (case identifier_leaf term of
         Const _ =>
           (constrain_call_head ctxt name pos term
             handle ERROR message => error (message ^ "\n" ^ hint))
       | Free (free_name, _) =>
           if Variable.is_fixed ctxt free_name then term
           else error ("urust_expr: " ^ hint ^ Position.here pos)
       | _ => term)
    end

  datatype item_call_role =
      Ordinary_Item_Call
    | Struct_Item_Call
    | No_Item_Call

  fun item_function_path role ctxt instance path actual_arity entry =
    let

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
      val constructor = source_constructor ctxt instance path entry
    in
      T.source_position pos
        (if arity = 0 then T.function_body (T.literal constructor)
         else T.lift_function pos arity constructor)
    end

  fun imported_function item_role actual_arity ctxt environment
      (route as {canonical, ...}: import_route) =
    let
      val role =
        (case item_role of
           Struct_Item_Call => "a struct expression head"
         | _ => "a call")
      val function =
             (case exact_item_constructor ctxt canonical of
                SOME entry =>
                  item_function_path item_role ctxt (route_instance (SOME route)) canonical
                    actual_arity entry
              | NONE =>
                  (case registered_call ctxt environment true (#selection route) canonical of
                     SOME registered => registered
                   | NONE =>
                       (case segment_generic_args (final_segment canonical) of
                          NONE => unusable_import ctxt call_import_roles role route
                        | SOME arguments =>
                            (case exact_registered_call ctxt (call_filters true)
                                (remove_final_generic_args canonical) of
                               SOME registered =>
                                 (reject_generated_function_generics ctxt canonical;
                                  apply_generic_arguments ctxt environment registered
                                    (SOME arguments))
                             | NONE => unusable_import ctxt call_import_roles role route))))
      val _ = report_import_use ctxt route
    in function end

  fun resolve_function_path item_role local_first actual_arity
      ctxt environment route path =
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
                 (use_local ctxt environment (name, pos))
           | _ => NONE)
        else NONE
      val function =
        (case route of
           SOME imported =>
             imported_function item_role actual_arity ctxt environment imported
         | NONE =>
        (case lexical_function () of
           SOME local_term => local_term
         | NONE =>
             (case
                if item_role = No_Item_Call
                then NONE
                else exact_item_constructor ctxt path
              of
                SOME entry =>
                  item_function_path item_role ctxt NONE path
                    actual_arity entry
              | NONE =>
                  (case registered_call ctxt environment (item_role <> No_Item_Call) NONE path of
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
                         (* Method entries are not callable directly, with or without a
                            turbofish. *)
                         val method_only =
                           item_role <> No_Item_Call andalso not (is_qualified_path base) andalso
                             method_only_key ctxt (render_path base)
                         val _ =
                           if method_only then () else reject_generated_function_generics ctxt path
                         val function =
                           if method_only
                           then
                             let val (name, pos) = path_terminal base
                             in method_only_call ctxt name pos end
                           else if item_role = No_Item_Call andalso
                              not (is_qualified_path base)
                           then
                             let val (name, pos) = path_terminal base
                             in resolve_identifier ctxt Micro_Rust_Names.NFunction name pos end
                           else
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
      ctxt environment (value_import_route ctxt environment path) path

  fun function_identifier ctxt environment identifier =
    function_path ctxt environment (make_single_path identifier) 0

  fun generated_struct_function ctxt source_path fields =
    let
      val route = struct_import_route ctxt S.Call_Notation source_path
      val path = (case route of SOME {canonical, ...} => canonical | NONE => source_path)
    in
    Option.map (fn entry =>
      let
        val _ = Option.app (report_import_use ctxt) route
        val pos = path_position path
        val _ = if I.constructor_shape entry = I.Named_Constructor then () else
          error ("urust_expr: generated constructor " ^ quote (render_path path) ^
            " does not support struct construction syntax" ^ Position.here pos)
        val source_fields = I.constructor_field_entries entry
        val names = map (fn SE_Field (name, _, _) => name) fields
        val _ = if null (duplicates (op =) names) then () else
          error ("urust_expr: duplicate struct initializer" ^ Position.here pos)
        val _ = List.app (fn name =>
          if exists (fn field => I.field_rust_name field = name) source_fields then ()
          else error ("urust_expr: unknown field " ^ quote name ^ Position.here pos)) names
        val _ = List.app (fn field => if member (op =) names (I.field_rust_name field) then ()
          else error ("urust_expr: missing field " ^ quote (I.field_rust_name field) ^ Position.here pos)) source_fields
        val _ = report_item_constructor ctxt path entry
        val unchanged = names = map I.field_rust_name source_fields
        val arity = length names
        val instance = route_instance route
        val function = if unchanged then source_constructor ctxt instance path entry else
          let
            val pure = source_constructor_scheme ctxt instance path entry
            val field_types = map I.field_rust_name source_fields ~~ binder_types (fastype_of pure)
            val variables = map_index (fn (index, name) =>
              let
                val typ = the (AList.lookup (op =) field_types name)
              in (name, Free ("_field_arg" ^ string_of_int index, typ)) end) names
            val arguments = map (fn field =>
              the (AList.lookup (op =) variables (I.field_rust_name field))) source_fields
            val wrapper = fold_rev (lambda o snd) variables (list_comb (pure, arguments))
          in if is_some instance then wrapper else fresh_item_instance path wrapper end
      in if arity = 0 then T.literal function else T.lift_function pos arity function end)
      (exact_item_constructor ctxt path)
    end

  fun struct_function_path ctxt environment path actual_arity =
    let
      val _ = List.app (fn segment =>
        case segment_generic_args segment of
          NONE => ()
        | SOME (Generic_Args (_, pos)) =>
            error ("urust_expr: generic arguments are not supported in struct-expression heads" ^
              Position.here pos)) (path_segments path)
    in
      resolve_function_path Struct_Item_Call false actual_arity
        ctxt environment (struct_import_route ctxt S.Call_Notation path) path
    end

  fun method_path ctxt environment path =
    let
      val function =
        resolve_function_path No_Item_Call false 0
          ctxt environment NONE path
      val (name, pos) = path_terminal path
      fun strip_internal_positions
          (Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ inner) =
            strip_internal_positions inner
        | strip_internal_positions term = term
      val head = Term.head_of (strip_internal_positions function)
      val unresolved =
        (case head of
           Free (free_name, _) =>
             not (Variable.is_fixed ctxt free_name)
         | _ => false)
    in
      if unresolved then
        let
          val _ =
            URust_Report_Transaction.report_text ctxt pos Markup.typing
              "unregistered uRust method call head"
        in
          error
            ("Type unification failed: unregistered method call head " ^
              quote (render_path path) ^
              " has no registered, fixed, or HOL constant resolution" ^
              Position.here pos)
        end
      else function
    end

  fun registered_function ctxt identifier =
    registered_identifier ctxt Micro_Rust_Names.NFunction identifier

  (* A macro path is a path role like any other: self_route rejects a later Self or self and
     substitutes a leading Self inside an impl (rejecting it outside one), so the lookup, and a
     missing-registration hint, use the canonical key. Self alone is a type, never a macro. *)
  fun registered_macro_path ctxt written_path
      {complete_name = written_name, complete_pos, bang_pos} =
    let
      val route = self_route ctxt written_path
      val _ =
        (case (route, path_segments written_path) of
           (SOME _, [Path_Segment (_, pos, _)]) =>
             error ("urust_expr: cannot find macro `Self`: Self names a type, not a macro" ^
               Position.here pos)
         | _ => ())
      val (path, complete_name) =
        (case route of
           SOME {canonical, ...} => (canonical, render_path canonical ^ "!")
         | NONE => (written_path, written_name))
    in
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
          val _ = Option.app (report_import_use ctxt) route
        in SOME registered end
    end

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

  (* The entries a direct call may reach, also through a type segment that selects impls. *)
  fun direct_call_entries ctxt path =
    let
      fun eligible key =
        Micro_Rust_Names.eligible_entries ctxt (call_filters true)
          (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction key)
    in
      (case eligible (render_path path) of
         [] =>
           (case path_segments path of
              _ :: _ :: _ => eligible (render_path (item_lookup_path path))
            | _ => [])
       | entries => entries)
    end

  fun is_nullary_function_path ctxt
      (environment as {locals, ...} : environment) source_path =
    (case value_import_route ctxt environment source_path of
       SOME {canonical, ...} =>
         exists
           (fn ({hol_term, ...} : Micro_Rust_Names.entry) =>
             is_nullary_function_type (fastype_of hol_term))
           (direct_call_entries ctxt canonical)
     | NONE =>
    let
      val path = source_path
      fun registered () =
        direct_call_entries ctxt path
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
                is_nullary_function_type (fastype_of free)
            | NONE =>
                if Variable.is_fixed ctxt name
                then false
                else if registered () then true else hol_constant ())
       | _ =>
           registered ())
    end)

  fun field_expression ctxt _ receiver name pos =
    let
      val lens =
        (case registered_identifier ctxt Micro_Rust_Names.NField (name, pos) of
           SOME registered => registered
         | NONE =>
             let
               val resolved = resolve_hol_identifier ctxt name pos
               val known =
                 (case identifier_leaf resolved of
                    Const _ => true
                  | Free (fixed_name, _) => Variable.is_fixed ctxt fixed_name
                  | _ => false)
             in
               if known then resolved
               else
                 error
                   ("urust_expr: unregistered field " ^ quote name ^
                     " has no fixed or HOL constant lens resolution" ^
                     Position.here pos)
             end)
    in T.focus_field lens receiver end

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
      (Constructor_Resolver {registered_by_identity, ...}) instance path entry =
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
      val selectors = map snd (I.constructor_fields entry)
      fun source_selectors ({identity, constructor, arity, family, ...}: constructor_info) =
        {identity = identity,
         constructor =
           (case instance of
              SOME typ => instantiated_scheme ctxt path entry typ
            | NONE =>
                if null (map_filter segment_generic_args (path_segments path))
                then constructor
                else item_constructor_instance ctxt path entry
                  (I.constructor_scheme entry |> Term.map_types Type.legacy_freeze_type)
                  |> fresh_item_instance path),
         arity = arity,
         family = family, selectors = selectors}: constructor_info
    in distinct_constructor_infos (map source_selectors candidates) end

  fun classify_imported_literal ctxt resolver ({canonical, ...}: import_route) =
    (case exact_item_constructor ctxt canonical of
       SOME _ => Registered_Constructor_Literal
     | NONE =>
         (case exact_literal_registrations ctxt canonical of
            [] => Unregistered_Literal
          | registrations =>
              if null (registered_constructor_candidates ctxt resolver registrations)
              then Registered_Value_Literal
              else Registered_Constructor_Literal))

  fun classify_registered_literal ctxt resolver path =
    (case pattern_import_route ctxt path of
       SOME route => classify_imported_literal ctxt resolver route
     | NONE =>
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
              else Registered_Constructor_Literal)))

  (* An imported pattern path is exact: only the canonical generated item or exact literal
     registration can supply a constructor, and absence is not a basename fallback. *)
  fun resolve_imported_constructor ctxt resolver (route as {canonical, ...}: import_route) =
    let
      val name = render_path canonical
      val pos = #2 (path_terminal canonical)
      val item = exact_item_constructor ctxt canonical
      val registrations = exact_literal_registrations ctxt canonical
      val candidates =
        (case item of
           SOME entry =>
             item_constructor_candidates ctxt resolver (route_instance (SOME route)) canonical entry
         | NONE => registered_constructor_candidates ctxt resolver registrations)
    in
      (case candidates of
         [] =>
           (case item of
              SOME _ =>
                error
                  ("urust_expr: generated Rust item " ^ quote name ^
                    " is not authenticated by native constructor metadata" ^ Position.here pos)
            | NONE => NONE)
       | [info] => SOME info
       | ambiguous => ambiguity_error "constructor pattern" name pos true ambiguous)
    end

  fun resolve_constructor ctxt resolver path =
    (case pattern_import_route ctxt path of
       SOME route => resolve_imported_constructor ctxt resolver route
     | NONE => resolve_source_constructor ctxt resolver path)

  and resolve_source_constructor ctxt resolver path =
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
             item_constructor_candidates ctxt resolver NONE path entry
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
        Micro_Rust_Semantic_Navigation.defer_report ctxt pos
          (Name_Space.markup (Consts.space_of (Proof_Context.consts_of ctxt)) name)
    | report_named_term _ _ _ = ()

  fun report_constructor_at ctxt path info =
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

  fun report_routed_constructor ctxt route path info =
    (case route of
       SOME (imported as {canonical, ...}) =>
         (report_constructor_at ctxt canonical info; report_import_use ctxt imported)
     | NONE => report_constructor_at ctxt path info)

  fun report_constructor ctxt path info =
    report_routed_constructor ctxt (pattern_import_route ctxt path) path info

  fun report_struct_constructor ctxt path info =
    report_routed_constructor ctxt (struct_import_route ctxt S.Literal_Notation path) path info

  fun report_field ctxt pos selector field =
    (report_named_term ctxt pos selector;
     Option.app (I.defer_field_reference ctxt pos) field)

  fun report_wildcard ctxt pos =
    URust_Report_Transaction.report_text ctxt pos Markup.typing "wildcard pattern"

  fun report_struct_label ctxt (_, pos) =
    URust_Report_Transaction.report_text ctxt pos Markup.typing
      "struct expression label"

  fun report_struct_labels ctxt source_path fields =
    let
      val path =
        (case struct_import_route ctxt S.Call_Notation source_path of
           SOME {canonical, ...} => canonical
         | NONE => source_path)
      fun label (SE_Field (name, pos, _)) = (name, pos)
      fun report_alias aliases field =
        let val (name, pos) = label field in
          (case AList.lookup (op =) aliases name of
             SOME source_field =>
               (URust_Report_Transaction.report_text ctxt pos Markup.typing
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

  type resolved_struct_field =
    {selector: term, field_reference: field_reference option,
     source_position: Position.T option,
     pattern: ur_pat, shorthand: bool}

  datatype resolved_struct_pattern =
      Resolved_Constructor_Struct of
        constructor_info *
          resolved_struct_field list
    | Resolved_Record_Struct of
        string *
          resolved_struct_field list

  (* Struct heads accept either a constructor name or the type name of a single-constructor datatype.
     Records come only from Record.get_info; Ctr_Sugar's record entry belongs to a different lowering
     domain and must not compete with constructor candidates. *)
  fun resolve_struct_constructor ctxt
      (resolver as
        Constructor_Resolver
          {type_fallbacks, record_types, ...})
      exact instance head_path =
    let
      val theory = Proof_Context.theory_of ctxt
      val identifier_name = render_path head_path
      val pos = #2 (path_terminal head_path)
      val item = exact_item_constructor ctxt head_path
      val registrations = exact_literal_registrations ctxt head_path
      val qualified = exact orelse is_qualified_path head_path
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
             item_constructor_candidates ctxt resolver instance head_path entry
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
      (source_head_path, fields) =
    let
      val route = struct_import_route ctxt S.Literal_Notation source_head_path
      val head_path =
        (case route of
           SOME {canonical, ...} => canonical
         | NONE => source_head_path)
      val head = render_path head_path
      val head_pos = #2 (path_terminal head_path)
      val registrations = exact_literal_registrations ctxt head_path
      val item = exact_item_constructor ctxt head_path
      val _ = if is_some item then () else reject_intermediate_generics head_path
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
        resolve_struct_constructor ctxt resolver (is_some route) (route_instance route) head_path
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

      fun add_field (name, pos, pattern, shorthand) (entries, rest_pos) =
        let val field = canonical_name name in
          (case AList.lookup (op =) entries field of
             SOME _ =>
               error ("urust_expr: struct pattern for " ^ quote display_name ^
                 " has duplicate field " ^ quote field ^ Position.here pos)
           | NONE => ((field, (pos, pattern, shorthand)) :: entries, rest_pos))
        end

      fun collect (SF_Field (name, pos, pattern)) state =
            add_field (name, pos, pattern, false) state
        | collect (SF_Shorthand (name, pos)) state =
            add_field (name, pos, P_Ident (name, pos), true) state
        | collect (SF_Rest pos) (entries, NONE) =
            (entries, SOME pos)
        | collect (SF_Rest pos) (_, SOME _) =
            error ("urust_expr: struct pattern has multiple `..` rest entries" ^
              Position.here pos)

      val (entries_rev, rest_pos) = fold collect fields ([], NONE)
      val entries = rev entries_rev
      val unknown =
        get_first (fn (name, (pos, _, _)) =>
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
             SOME (pos, pattern, shorthand) =>
               {selector = selector, field_reference = field_reference,
                source_position = SOME pos, pattern = pattern, shorthand = shorthand}
           | NONE =>
               {selector = selector, field_reference = field_reference,
                source_position = NONE, pattern = P_Wild Position.none, shorthand = false}))
          selector_entries
    in
      (case candidate of
         Constructor_Candidate {info, ...} =>
           Resolved_Constructor_Struct (info, ordered)
       | Record_Candidate {record_name, ...} =>
           Resolved_Record_Struct (record_name, ordered))
    end

  (* Self as a parameter pattern: inside an impl of a unit struct it matches
     the unit value, of the Self type; otherwise it gets the path-pattern errors of a binding
     site, and outside impls the outside-impl message. *)
  fun self_pattern ctxt pos =
    let val path = make_single_path ("Self", pos) in
      (case self_route ctxt path of
         SOME (route as {canonical, ...}) =>
           (case exact_item_constructor ctxt canonical of
              SOME entry =>
                if I.constructor_shape entry = I.Unit_Constructor andalso
                   I.constructor_origin entry = I.Struct_Constructor
                then
                  (report_item_constructor ctxt canonical entry; report_import_use ctxt route;
                   (case route_instance (SOME route) of SOME typ => typ | NONE => dummyT))
                else
                  error
                    ("urust_expr: constructor " ^ quote "Self" ^ " expects " ^
                      string_of_int (item_constructor_arity ctxt entry) ^
                      " pattern argument(s), but got 0" ^ Position.here pos)
            | NONE =>
                error
                  ("urust_expr: unsupported or refutable pattern in a binding position: Self (" ^
                    quote (render_path (item_lookup_path canonical)) ^ ") is not a unit struct" ^
                    Position.here pos))
       | NONE => raise Fail "urust_expr: internal Self route")
    end

  fun allocate_expression_arguments ctxt environment arguments =
    gen_allocate_parameters self_pattern "urust_expr" "argument" ctxt environment arguments

  fun allocate_function_parameters ctxt environment parameters =
    gen_allocate_parameters self_pattern "urust_fn" "parameter" ctxt environment parameters
end
\<close>

end
