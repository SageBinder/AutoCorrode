theory Parser_Impl_Quotation
  imports
    Parser_Impl
    Parser_Impl_Translate
begin

section\<open> Closed explicit-capture quotations \<close>

ML\<open>
signature URUST_QUOTATION =
sig
  type result = {abstraction: term, operands: term list}

  val elaborate:
    Proof.context ->
      ((string * Position.T) * term) list ->
      Input.source list ->
      URust_AST.ur_expr ->
      result
end
\<close>

text\<open>
Quotation elaboration is deliberately stricter than the declaration commands. It validates the
complete unresolved AST before lowering, selects one declared registration for every semantic global
use, lowers in an immutable no-fallback resolution environment, audits the resulting abstraction,
and only then applies the already-parsed capture operands.
\<close>

ML\<open>
structure URust_Quotation :> URUST_QUOTATION =
struct
  open URust_AST

  type result = {abstraction: term, operands: term list}

  datatype scope_origin = Capture | Lexical
  datatype pattern_site =
      Always_Bind
    | Resolve_Case
    | Resolve_Switch

  type dependency =
    {name: string, pos: Position.T}

  type dependency_use =
    Micro_Rust_Names.ctxt_kind * string * Position.T

  datatype usage =
    Usage of
      {captures: unit Symtab.table,
       dependencies: dependency_use list}

  val empty_usage =
    Usage
      {captures = Symtab.empty,
       dependencies = []}

  fun quotation_error message pos =
    error ("uRust quotation: " ^ message ^ Position.here pos)

  fun path_terminal_position path =
    #2 (segment_identifier (final_segment path))

  fun pattern_position (P_Wild pos) = pos
    | pattern_position (P_Ident (_, pos)) = pos
    | pattern_position (P_Literal payload) =
        literal_position payload
    | pattern_position (P_Path path) = path_position path
    | pattern_position (P_Constr (path, _)) =
        path_position path
    | pattern_position (P_Tuple (_, pos)) = pos
    | pattern_position (P_Group pattern) =
        pattern_position pattern
    | pattern_position (P_Borrow (_, _, pos)) = pos
    | pattern_position (P_Alias (_, _, _, pos)) = pos
    | pattern_position (P_Range (_, _, _, pos)) = pos
    | pattern_position (P_Slice (_, pos)) = pos
    | pattern_position (P_Struct (path, _)) =
        path_position path
    | pattern_position (P_Or (_, pos)) = pos

  fun path_has_generics path =
    exists (is_some o segment_generic_args) (path_segments path)

  fun reject_generic_path path =
    if path_has_generics path then
      quotation_error "generic arguments are not allowed"
        (path_position path)
    else ()

  fun parse_dependency ctxt source =
    (case URust_Parser.parse_source ctxt source of
       SOME (UE_Path path) =>
         {name = render_path path,
          pos = Input.pos_of source}
     | SOME expression =>
         quotation_error
           "a `using` entry must contain exactly one uRust path"
           (expression_position expression)
     | NONE =>
         quotation_error
           "a `using` entry must not be empty"
           (Input.pos_of source))

  fun validate_dependencies dependencies =
    let
      fun add ({name, pos} : dependency) table =
        (case Symtab.lookup table name of
           NONE => Symtab.update (name, pos) table
         | SOME original_pos =>
             quotation_error
               ("duplicate dependency " ^ quote name ^
                 "\nThe original dependency is here" ^
                 Position.here original_pos)
               pos)
    in fold add dependencies Symtab.empty end

  fun validate_captures captures =
    let
      fun add ((name, pos), _) table =
        if name = "_" then
          quotation_error "capture name cannot be `_`" pos
        else
          (case Symtab.lookup table name of
             NONE => Symtab.update (name, pos) table
           | SOME original_pos =>
               quotation_error
                 ("duplicate capture " ^ quote name ^
                   "\nThe original capture is here" ^
                   Position.here original_pos)
                 pos)
    in fold add captures Symtab.empty end

  fun validate_capture_dependency_overlap capture_table
      dependency_table =
    List.app
      (fn (name, dependency_pos) =>
        (case Symtab.lookup capture_table name of
           NONE => ()
         | SOME capture_pos =>
             quotation_error
               ("name " ^ quote name ^
                 " is both a capture and a dependency" ^
                 "\nThe capture is here" ^
                 Position.here capture_pos)
               dependency_pos))
      (Symtab.dest dependency_table)

  fun initial_scope capture_table =
    Symtab.map (K (K Capture)) capture_table

  fun mark_capture name
      (Usage {captures, dependencies}) =
    Usage
      {captures = Symtab.update (name, ()) captures,
       dependencies = dependencies}

  fun add_dependency_use use
      (Usage {captures, dependencies}) =
    Usage
      {captures = captures,
       dependencies = use :: dependencies}

  fun use_local scope name usage =
    (case Symtab.lookup scope name of
       SOME Capture => SOME (mark_capture name usage)
     | SOME Lexical => SOME usage
     | NONE => NONE)

  fun declared dependency_table name =
    Symtab.defined dependency_table name

  fun use_dependency dependency_table kind name pos usage =
    if declared dependency_table name then
      add_dependency_use (kind, name, pos) usage
    else
      quotation_error
        ("undeclared " ^ Micro_Rust_Names.kind_to_string kind ^
          " dependency " ^ quote name)
        pos

  fun use_identifier dependency_table scope kind (name, pos) usage =
    (case use_local scope name usage of
       SOME usage' => usage'
     | NONE =>
         use_dependency dependency_table kind name pos usage)

  fun use_path dependency_table scope kind local_first path usage =
    let
      val _ = reject_generic_path path
    in
      (case path_segments path of
         [Path_Segment (name, pos, NONE)] =>
           if local_first then
             use_identifier dependency_table scope kind
               (name, pos) usage
           else
             use_dependency dependency_table kind name pos usage
       | _ =>
           use_dependency dependency_table kind
             (render_path path) (path_terminal_position path) usage)
    end

  fun validate_local_name ctxt dependency_table (name, pos) =
    if declared dependency_table name then
      quotation_error
        ("lexical binder " ^ quote name ^
          " collides with a declared dependency")
        pos
    else
      let
        val registered_roles =
          map_filter
            (fn kind =>
              if null (Micro_Rust_Names.lookups ctxt kind name)
              then NONE
              else
                SOME
                  (Micro_Rust_Names.kind_to_string kind))
            [Micro_Rust_Names.NLiteral,
             Micro_Rust_Names.NFunction,
             Micro_Rust_Names.NField]
      in
        if null registered_roles then ()
        else
          quotation_error
            ("lexical binder " ^ quote name ^
              " collides with registered " ^
              commas registered_roles ^ " name resolution")
            pos
      end

  fun validate_unique_binders ctxt dependency_table binders =
    let
      fun add (name, pos) table =
        let
          val _ =
            validate_local_name ctxt dependency_table
              (name, pos)
        in
          (case Symtab.lookup table name of
             NONE => Symtab.update (name, pos) table
           | SOME original_pos =>
               quotation_error
                 ("duplicate lexical binder " ^ quote name ^
                   "\nThe original binder is here" ^
                   Position.here original_pos)
                 pos)
        end
      val _ = fold add binders Symtab.empty
    in binders end

  fun extend_scope ctxt dependency_table scope binders =
    fold
      (fn (name, pos) =>
        (validate_local_name ctxt dependency_table (name, pos);
         Symtab.update (name, Lexical)))
      binders scope

  fun same_binder_names left right =
    eq_set (op =)
      (map fst left, map fst right)

  fun validate_or_binders pos [] = []
    | validate_or_binders pos (first :: rest) =
        (List.app
           (fn alternative =>
             if same_binder_names first alternative then ()
             else
               quotation_error
                 "or-pattern alternatives must bind the same names"
                 pos)
           rest;
         first)

  fun inspect_literal payload usage =
    (case payload of
       LP_ValAntiq source =>
         quotation_error
           "value antiquotations are not allowed"
           (Input.pos_of source)
     | _ => usage)

  fun inspect_pattern ctxt dependency_table scope site pattern usage =
    let
      val resolver =
        URust_Resolution.make_constructor_resolver ctxt
          URust_Resolution.empty_environment
          (pattern_position pattern)

      fun declared_constructor name pos =
        declared dependency_table name andalso
          (case
              URust_Resolution.classify_registered_literal
                ctxt resolver (make_single_path (name, pos)) of
             URust_Resolution.Registered_Constructor_Literal =>
               true
           | _ => false)

      fun combine results =
        validate_unique_binders ctxt dependency_table
          (maps I results)

      fun inspect source_pattern state =
        (case source_pattern of
           P_Wild _ => ([], state)
         | P_Ident (name, pos) =>
             (case site of
                Always_Bind =>
                  (validate_local_name ctxt dependency_table
                     (name, pos);
                   ([(name, pos)], state))
              | Resolve_Case =>
                  if declared_constructor name pos then
                    ([],
                     use_dependency dependency_table
                       Micro_Rust_Names.NLiteral name pos state)
                  else
                    (validate_local_name ctxt dependency_table
                       (name, pos);
                     ([(name, pos)], state))
              | Resolve_Switch =>
                  ([],
                   use_dependency dependency_table
                     Micro_Rust_Names.NLiteral name pos state))
         | P_Path path =>
             ([],
              use_path dependency_table scope
                Micro_Rust_Names.NLiteral false path state)
         | P_Literal payload =>
             ([], inspect_literal payload state)
         | P_Constr (path, arguments) =>
             let
               val state' =
                 use_path dependency_table scope
                   Micro_Rust_Names.NLiteral false path state
               val (results, state'') =
                 inspect_list arguments state'
             in (combine results, state'') end
         | P_Tuple (arguments, _) =>
             let
               val (results, state') =
                 inspect_list arguments state
             in (combine results, state') end
         | P_Group inner => inspect inner state
         | P_Borrow (_, inner, _) => inspect inner state
         | P_Alias (name, pos, inner, _) =>
             let
               val _ =
                 validate_local_name ctxt dependency_table
                   (name, pos)
               val (binders, state') = inspect inner state
             in
               (validate_unique_binders ctxt dependency_table
                  ((name, pos) :: binders),
                state')
             end
         | P_Range (_, lower, upper, _) =>
             let
               fun endpoint endpoint_pattern current =
                 (case endpoint_pattern of
                    P_Literal payload =>
                      inspect_literal payload current
                  | P_Ident identifier =>
                      use_identifier dependency_table scope
                        Micro_Rust_Names.NLiteral identifier current
                  | P_Path path =>
                      use_path dependency_table scope
                        Micro_Rust_Names.NLiteral false path current
                  | P_Group nested => endpoint nested current
                  | _ =>
                      quotation_error
                        "invalid range-pattern endpoint"
                        (case endpoint_pattern of
                           P_Wild pos => pos
                         | P_Tuple (_, pos) => pos
                         | P_Borrow (_, _, pos) => pos
                         | P_Alias (_, _, _, pos) => pos
                         | P_Range (_, _, _, pos) => pos
                         | P_Slice (_, pos) => pos
                         | P_Or (_, pos) => pos
                         | P_Constr (path, _) => path_position path
                         | P_Struct (path, _) => path_position path))
               val state' = endpoint lower state
             in ([], endpoint upper state') end
         | P_Slice (items, _) =>
             let
               val nested =
                 map_filter
                   (fn SI_Pat item => SOME item
                     | SI_Rest _ => NONE)
                   items
               val (results, state') = inspect_list nested state
             in (combine results, state') end
         | P_Struct (path, fields) =>
             let
               val state' =
                 use_path dependency_table scope
                   Micro_Rust_Names.NLiteral false path state
               fun inspect_field (SF_Field (_, _, nested))
                     (results, current) =
                     let
                       val (binders, next) =
                         inspect nested current
                     in (binders :: results, next) end
                 | inspect_field (SF_Shorthand (name, pos))
                     (results, current) =
                     (validate_local_name ctxt dependency_table
                        (name, pos);
                      ([(name, pos)] :: results, current))
                 | inspect_field (SF_Rest _)
                     (results, current) =
                     (results, current)
               val (results, state'') =
                 fold inspect_field fields ([], state')
             in (combine (rev results), state'') end
         | P_Or (alternatives, pos) =>
             let
               val (results, state') =
                 inspect_list alternatives state
             in
               (validate_or_binders pos results, state')
             end)

      and inspect_list patterns state =
        let
          fun inspect_one source_pattern (results, current) =
            let
              val (binders, next) =
                inspect source_pattern current
            in (binders :: results, next) end
          val (results, final) =
            fold inspect_one patterns ([], state)
        in (rev results, final) end
    in inspect pattern usage end

  fun inspect_expression ctxt dependency_table scope expression usage =
    let
      fun inspect_list expressions state =
        fold (inspect_expression ctxt dependency_table scope)
          expressions state

      fun inspect_binding site pattern rhs body state =
        let
          val state' =
            inspect_expression ctxt dependency_table scope rhs state
          val (binders, state'') =
            inspect_pattern ctxt dependency_table scope site
              pattern state'
          val body_scope =
            extend_scope ctxt dependency_table scope binders
        in
          inspect_expression ctxt dependency_table body_scope
            body state''
        end

      fun inspect_branch pattern scrutinee success fallback state =
        let
          val state' =
            inspect_expression ctxt dependency_table scope
              scrutinee state
             val site =
            (case pattern of
               P_Tuple _ => Always_Bind
             | _ => Resolve_Case)
          val (binders, state'') =
            inspect_pattern ctxt dependency_table scope site
              pattern state'
          val success_scope =
            extend_scope ctxt dependency_table scope binders
          val state''' =
            inspect_expression ctxt dependency_table success_scope
              success state''
        in
          (case fallback of
             NONE => state'''
           | SOME branch =>
               inspect_expression ctxt dependency_table scope
                 branch state''')
        end

      fun inspect_place place state =
        (case place of
           UP_Path path =>
             use_path dependency_table scope
               Micro_Rust_Names.NLiteral true path state
         | UP_Deref (inner, _) =>
             inspect_expression ctxt dependency_table scope inner state
         | UP_Field (base, name, pos) =>
             use_identifier dependency_table scope
               Micro_Rust_Names.NField (name, pos)
               (inspect_place base state)
         | UP_Index (base, index, _) =>
             inspect_expression ctxt dependency_table scope index
               (inspect_place base state)
         | UP_Antiq source =>
             quotation_error
               "expression antiquotations are not allowed"
               (Input.pos_of source))
    in
      (case expression of
         UE_Unit _ => usage
       | UE_Tuple (elements, _) => inspect_list elements usage
       | UE_Array (elements, _) => inspect_list elements usage
       | UE_Struct (head, fields, _) =>
           let
             val usage' =
               use_path dependency_table scope
                 Micro_Rust_Names.NFunction false head usage
             val initializers =
               map (fn SE_Field (_, _, value) => value) fields
           in inspect_list initializers usage' end
       | UE_Path path =>
           use_path dependency_table scope
             Micro_Rust_Names.NLiteral true path usage
       | UE_Literal payload => inspect_literal payload usage
       | UE_ExprAntiq source =>
           quotation_error
             "expression antiquotations are not allowed"
             (Input.pos_of source)
       | UE_Yield _ => usage
       | UE_Log (_, _, pos) =>
           quotation_error
             "primitive log operands are embedded HOL and are not allowed"
             pos
       | UE_LogData (entries, _) =>
           fold
             (fn LDE_String _ => I
               | LDE_Identifier (name, pos) =>
                   (fn state =>
                     (case use_local scope name state of
                        SOME state' => state'
                      | NONE =>
                          quotation_error
                            ("log-data identifier " ^ quote name ^
                              " must be captured or lexical")
                            pos)))
             entries usage
       | UE_Closure (formals, body, _) =>
           let
             fun formal (P_Ident formal_name) = formal_name
               | formal (P_Wild pos) =
                   quotation_error
                     "closure formal must be an identifier" pos
               | formal other =
                   quotation_error
                     "closure formal must be an identifier"
                     (case other of
                        P_Path path => path_position path
                      | P_Literal payload => literal_position payload
                      | P_Constr (path, _) => path_position path
                      | P_Tuple (_, pos) => pos
                      | P_Group inner =>
                          (case inner of
                             P_Ident (_, pos) => pos
                           | _ => Position.none)
                      | P_Borrow (_, _, pos) => pos
                      | P_Alias (_, _, _, pos) => pos
                      | P_Range (_, _, _, pos) => pos
                      | P_Slice (_, pos) => pos
                      | P_Struct (path, _) => path_position path
                      | P_Or (_, pos) => pos
                      | P_Wild pos => pos)
             val signatures =
               validate_unique_binders ctxt dependency_table
                 (map formal formals)
             val body_scope =
               extend_scope ctxt dependency_table scope signatures
           in
             inspect_expression ctxt dependency_table body_scope
               body usage
           end
       | UE_Let (pattern, rhs, body) =>
           inspect_binding Always_Bind pattern rhs body usage
       | UE_LetMut (pattern, rhs, body, _) =>
           inspect_binding Always_Bind pattern rhs body usage
       | UE_Const (pattern, rhs, body) =>
           inspect_binding Always_Bind pattern rhs body usage
       | UE_Seq (first, second) =>
           inspect_expression ctxt dependency_table scope second
             (inspect_expression ctxt dependency_table scope first usage)
       | UE_Return (NONE, _) => usage
       | UE_Return (SOME value, _) =>
           inspect_expression ctxt dependency_table scope value usage
       | UE_Bin (_, left, right, _) =>
           inspect_expression ctxt dependency_table scope right
             (inspect_expression ctxt dependency_table scope left usage)
       | UE_Cast (operand, _, _) =>
           inspect_expression ctxt dependency_table scope operand usage
       | UE_Unary (_, operand, _) =>
           inspect_expression ctxt dependency_table scope operand usage
       | UE_Group (inner, _) =>
           inspect_expression ctxt dependency_table scope inner usage
       | UE_Block (inner, _) =>
           inspect_expression ctxt dependency_table scope inner usage
       | UE_If (condition, then_branch, else_branch, _) =>
           let
             val usage' =
               inspect_expression ctxt dependency_table scope
                 condition usage
             val usage'' =
               inspect_expression ctxt dependency_table scope
                 then_branch usage'
           in
             (case else_branch of
                NONE => usage''
              | SOME branch =>
                  inspect_expression ctxt dependency_table scope
                    branch usage'')
           end
       | UE_IfLet (pattern, scrutinee, success, fallback, _) =>
           inspect_branch pattern scrutinee success fallback usage
       | UE_LetElse
           (pattern, scrutinee, fallback, continuation, _) =>
           inspect_branch pattern scrutinee continuation
             (SOME fallback) usage
       | UE_While (_, _, _, pos) =>
           quotation_error
             "fuelled loops are not allowed" pos
       | UE_Loop (_, _, pos) =>
           quotation_error
             "fuelled loops are not allowed" pos
       | UE_For (pattern, iterable, body, _) =>
           inspect_binding Resolve_Case pattern iterable body usage
       | UE_WhileLet (_, _, _, _, pos) =>
           quotation_error
             "fuelled loops are not allowed" pos
       | UE_Call (callee, arguments, _) =>
           let
             val usage' =
               (case callee of
                  UC_Path path =>
                    use_path dependency_table scope
                      Micro_Rust_Names.NFunction true path usage
                | UC_Method (receiver, segment) =>
                    let
                      val _ =
                        (case segment_generic_args segment of
                           NONE => ()
                         | SOME (Generic_Args (_, pos)) =>
                             quotation_error
                               "generic arguments are not allowed" pos)
                      val usage0 =
                        inspect_expression ctxt dependency_table scope
                          receiver usage
                    in
                      use_identifier dependency_table scope
                        Micro_Rust_Names.NFunction
                        (segment_identifier segment) usage0
                    end
                | UC_Antiq source =>
                    quotation_error
                      "antiquotation callees are not allowed"
                      (Input.pos_of source)
                | UC_FunLiteral (_, _, pos, _) =>
                    quotation_error
                      "HOL function literals are not allowed" pos)
           in inspect_list arguments usage' end
       | UE_Field (receiver, name, pos) =>
           use_identifier dependency_table scope
             Micro_Rust_Names.NField (name, pos)
             (inspect_expression ctxt dependency_table scope
               receiver usage)
       | UE_Index (receiver, index, _) =>
           inspect_expression ctxt dependency_table scope index
             (inspect_expression ctxt dependency_table scope
               receiver usage)
       | UE_TupleProjection (receiver, _, _) =>
           inspect_expression ctxt dependency_table scope receiver usage
       | UE_Range (_, lower, upper, _) =>
           inspect_expression ctxt dependency_table scope upper
             (inspect_expression ctxt dependency_table scope lower usage)
       | UE_Assign (_, place, rhs, _) =>
           inspect_expression ctxt dependency_table scope rhs
             (inspect_place place usage)
       | UE_Macro (_, _, _, pos) =>
           quotation_error "macros are not allowed" pos
       | UE_Match (flavour, scrutinee, arms, _) =>
           let
             val usage' =
               inspect_expression ctxt dependency_table scope
                 scrutinee usage
             val resolver =
               URust_Resolution.make_constructor_resolver ctxt
                 URust_Resolution.empty_environment
                 (case arms of
                    UR_Arm (pattern, _, _) :: _ =>
                      pattern_position pattern
                  | [] => Position.none)

             fun strip_groups (P_Group pattern) =
                   strip_groups pattern
               | strip_groups pattern = pattern

             datatype match_capability =
               Match_Capability of
                 {case_ok: bool, switch_ok: bool}

             fun registered_capability unregistered_switch path =
               if declared dependency_table (render_path path) then
                 (case
                     URust_Resolution.classify_registered_literal
                       ctxt resolver path of
                    URust_Resolution.Registered_Constructor_Literal =>
                      Match_Capability
                        {case_ok = true, switch_ok = false}
                  | _ =>
                      Match_Capability
                        {case_ok = true, switch_ok = true})
               else
                 Match_Capability
                   {case_ok = true,
                    switch_ok = unregistered_switch}

             fun capability pattern =
               (case strip_groups pattern of
                  P_Literal (LP_Integer _) =>
                    Match_Capability
                      {case_ok = false, switch_ok = true}
                | P_Ident identifier =>
                    registered_capability true
                      (make_single_path identifier)
                | P_Path path =>
                    registered_capability false path
                | P_Wild _ =>
                    Match_Capability
                      {case_ok = true, switch_ok = true}
                | _ =>
                    Match_Capability
                      {case_ok = true, switch_ok = false})

             fun arm_pattern (UR_Arm (pattern, _, _)) = pattern
             fun arm_has_guard (UR_Arm (_, guard, _)) =
               is_some guard
             fun case_compatible
                 (Match_Capability {case_ok, ...}) = case_ok
             fun switch_compatible
                 (Match_Capability {switch_ok, ...}) = switch_ok

             val selected_flavour =
               (case flavour of
                  MF_Auto =>
                    let
                      val capabilities =
                        map (capability o arm_pattern) arms
                    in
                      if List.exists arm_has_guard arms then
                        MF_Case
                      else if List.all case_compatible capabilities then
                        MF_Case
                      else if List.all switch_compatible capabilities then
                        MF_Switch
                      else
                        quotation_error
                          "mixed numeral and constructor patterns in bare `match`"
                          (case arms of
                             UR_Arm (pattern, _, _) :: _ =>
                               pattern_position pattern
                           | [] => Position.none)
                    end
                | explicit => explicit)
             val pattern_site =
               (case selected_flavour of
                  MF_Switch => Resolve_Switch
                | MF_Case => Resolve_Case
                | MF_Auto =>
                    error
                      "uRust quotation: internal unresolved match flavour")
             fun inspect_arm
                 (UR_Arm (pattern, guard, body)) state =
               let
                 val (binders, state') =
                   inspect_pattern ctxt dependency_table scope
                     pattern_site pattern state
                 val arm_scope =
                   extend_scope ctxt dependency_table scope binders
                 val state'' =
                   (case guard of
                      NONE => state'
                    | SOME (guard_expression, _) =>
                        inspect_expression ctxt dependency_table arm_scope
                          guard_expression state')
               in
                 inspect_expression ctxt dependency_table arm_scope
                   body state''
               end
           in fold inspect_arm arms usage' end)
    end

  fun validate_capture_usage capture_table
      (Usage {captures, ...}) =
    List.app
      (fn (name, pos) =>
        if Symtab.defined captures name then ()
        else
          quotation_error
            ("unused capture " ^ quote name) pos)
      (Symtab.dest capture_table)

  fun dependency_key kind name =
    Micro_Rust_Names.kind_to_string kind ^ "\000" ^ name

  fun select_dependencies ctxt dependency_table
      (Usage {dependencies = uses, ...}) =
    let
      fun select (kind, name, pos) selected =
        let
          val key = dependency_key kind name
        in
          if Symtab.defined selected key then selected
          else
            (case Micro_Rust_Names.lookups ctxt kind name of
               [] =>
                 quotation_error
                   ("dependency " ^ quote name ^
                     " has no registered " ^
                     Micro_Rust_Names.kind_to_string kind ^
                     " backend")
                   pos
             | [entry] =>
                 Symtab.update
                   (key, (kind, name, entry)) selected
             | _ =>
                 quotation_error
                   ("dependency " ^ quote name ^
                     " has multiple registered " ^
                     Micro_Rust_Names.kind_to_string kind ^
                     " backends")
                   pos)
        end
      val selected = fold select uses Symtab.empty
      val used_names =
        fold
          (fn (_, name, _) => Symtab.update (name, ()))
          uses Symtab.empty
      val _ =
        List.app
          (fn (name, pos) =>
            if Symtab.defined used_names name then ()
            else
              quotation_error
                ("unused dependency " ^ quote name) pos)
          (Symtab.dest dependency_table)
    in map #2 (Symtab.dest selected) end

  fun internal_marker
      (Const (name, _)) =
        name = \<^const_name>\<open>urust_dispatch\<close> orelse
        name = \<^syntax_const>\<open>_type_constraint_\<close>
    | internal_marker (Free (name, _)) =
        String.isPrefix "_urust_dispatch_payload___" name
    | internal_marker _ = false

  fun audit_abstraction abstraction =
    let
      val frees = Term.add_frees abstraction []
      val variables = Term.add_vars abstraction []
      val _ =
        if null frees then ()
        else
          error
            ("uRust quotation: internal residual free variable(s): " ^
              commas_quote (map fst frees))
      val _ =
        if null variables then ()
        else
          error
            ("uRust quotation: internal residual schematic variable(s): " ^
              commas_quote (map (Term.string_of_vname o fst) variables))
      val _ =
        if Term.exists_subterm internal_marker abstraction then
          error "uRust quotation: internal resolution marker survived lowering"
        else ()
    in abstraction end

  (* Parse translations must distinguish logical constants from syntax constructors. Quotation
     lowering constructs logical constants directly, so encode only those constant names before
     returning the term to the surrounding syntax pipeline. This does not inspect, strip, or
     reconstruct type constraints: quotation lowering must not produce an internal
     `_type_constraint_`, and audit_abstraction rejects one if it does. *)
  fun encode_logical_constants ctxt =
    Term.map_aterms
      (fn constant as Const (name, T) =>
            if Lexicon.is_marked_entity name orelse
                Proof_Context.is_syntax_const ctxt name
            then constant
            else Const (Lexicon.mark_const name, T)
        | atom => atom)

  fun elaborate ctxt captures dependency_sources expression =
    let
      val dependencies = map (parse_dependency ctxt) dependency_sources
      val dependency_table = validate_dependencies dependencies
      val capture_table = validate_captures captures
      val _ =
        validate_capture_dependency_overlap capture_table
          dependency_table
      val scope = initial_scope capture_table
      val usage =
        inspect_expression ctxt dependency_table scope expression
          empty_usage
      val _ = validate_capture_usage capture_table usage
      val selected =
        select_dependencies ctxt dependency_table usage
      val signatures =
        map (fn (name_pos, _) => (name_pos, dummyT)) captures
      val abstraction =
        URust_Translate.mk_quotation_expression ctxt selected
          signatures expression
        |> encode_logical_constants ctxt
        |> audit_abstraction
      val operands = map snd captures
    in
      {abstraction = abstraction,
       operands = operands}
    end
end
\<close>

end
