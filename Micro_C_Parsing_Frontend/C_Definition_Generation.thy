theory C_Definition_Generation
  imports
    C_Translation_Engine
    Frontend_Common.Frontend_Common
  keywords "c_source" :: thy_decl
       and "c_file" :: thy_decl
       and "abi" and "compiler" and "addr" and "gv" and "abort"
       and "types" and "functions" and "manifest"
       and "verbose"
begin

subsection \<open>Definition Generation\<close>

ML \<open>
structure C_Def_Gen : sig
  type manifest = {functions: string list option, types: string list option}
  type config =
    {frontend: C_Frontend_Config.t,
     manifest: manifest,
     define_abi_metadata: bool}
  type analysis =
    {struct_tab: (string * C_Ast_Utils.c_numeric_type) list Symtab.table,
     union_names: string list,
     parametric_struct_names: unit Symtab.table,
     struct_record_defs: (string * (string * typ option) list) list,
     struct_array_field_tab: string list Symtab.table,
     enum_tab: int Symtab.table,
     typedef_tab: C_Ast_Utils.c_numeric_type Symtab.table,
     fundefs: C_Ast.nodeInfo C_Ast.cFunctionDef list,
     fundefs_raw: C_Ast.nodeInfo C_Ast.cFunctionDef list,
     param_cty_of_decl:
       C_Ast.nodeInfo C_Ast.cDeclaration -> C_Ast_Utils.c_numeric_type,
     pure_function_names: unit Symtab.table,
     func_ret_types: C_Ast_Utils.c_numeric_type Symtab.table,
     func_param_types: C_Ast_Utils.c_numeric_type list Symtab.table,
     list_backed_param_modes: bool list Symtab.table}
  val analyze_translation_unit :
    C_Frontend_Config.t -> manifest ->
    C_Ast.nodeInfo C_Ast.cTranslationUnit -> analysis
  val declaration_plan :
    config -> C_Ast.nodeInfo C_Ast.cTranslationUnit ->
    local_theory -> Frontend_Declaration_Plan.T
  val process_translation_unit : config -> C_Ast.nodeInfo C_Ast.cTranslationUnit
                                 -> local_theory -> local_theory
end =
struct
  structure Declaration_Plan = Frontend_Declaration_Plan

  type manifest = {functions: string list option, types: string list option}
  type config =
    {frontend: C_Frontend_Config.t,
     manifest: manifest,
     define_abi_metadata: bool}
  type analysis =
    {struct_tab: (string * C_Ast_Utils.c_numeric_type) list Symtab.table,
     union_names: string list,
     parametric_struct_names: unit Symtab.table,
     struct_record_defs: (string * (string * typ option) list) list,
     struct_array_field_tab: string list Symtab.table,
     enum_tab: int Symtab.table,
     typedef_tab: C_Ast_Utils.c_numeric_type Symtab.table,
     fundefs: C_Ast.nodeInfo C_Ast.cFunctionDef list,
     fundefs_raw: C_Ast.nodeInfo C_Ast.cFunctionDef list,
     param_cty_of_decl:
       C_Ast.nodeInfo C_Ast.cDeclaration -> C_Ast_Utils.c_numeric_type,
     pure_function_names: unit Symtab.table,
     func_ret_types: C_Ast_Utils.c_numeric_type Symtab.table,
     func_param_types: C_Ast_Utils.c_numeric_type list Symtab.table,
     list_backed_param_modes: bool list Symtab.table}

  fun binding_of_long_name full_name =
    (case rev (Long_Name.explode full_name) of
       [] => error "c_source: empty generated binding"
     | base :: reversed_qualifiers =>
         fold
           (Binding.qualify true)
           reversed_qualifiers
           (Binding.name base))

  fun map_binding_base map full_name =
    (case rev (Long_Name.explode full_name) of
       [] => error "c_source: empty generated binding"
     | base :: reversed_qualifiers =>
         Long_Name.implode
           (rev reversed_qualifiers @ [map base]))

  fun define_c_function (config : C_Frontend_Config.t) prefix name term lthy =
    let
      val full_name = prefix ^ name
      val binding = binding_of_long_name full_name
      val term' = term |> Syntax.check_term lthy
      val ((lhs_term, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [shallow_computation_simps]}), term'))
          lthy
      val morphed_lhs = Morphism.term (Local_Theory.target_morphism lthy') lhs_term
      val (registered_term, head_desc) =
        let
          val (head, args) = Term.strip_comb morphed_lhs
          (* Replace phantom TYPE args whose type variable became schematic
             (TVar) with TYPE(unit).  This prevents "Illegal schematic type
             variable" errors in callers that reference this constant.
             Only phantom TYPE args are affected — TFree TYPE args (locale
             parameters) and non-TYPE args are preserved. *)
          val non_type_args =
            List.filter (fn Const (n, Type ("itself", _)) =>
                              n <> \<^const_name>\<open>Pure.type\<close>
                          | _ => true) args
          val used_tfrees =
            List.foldl (fn (a, acc) => Term.add_tfrees a acc) [] non_type_args
            |> map fst
          fun fix_type_arg (Const (n, Type ("itself", [TFree (tv, _)]))) =
                if n = \<^const_name>\<open>Pure.type\<close> andalso
                   not (member (op =) used_tfrees tv)
                then Const (n, Type ("itself", [@{typ unit}]))
                else Const (n, Type ("itself", [TFree (tv, @{sort type})]))
            | fix_type_arg (Const (n, Type ("itself", [TVar _]))) =
                if n = \<^const_name>\<open>Pure.type\<close>
                then Const (n, Type ("itself", [@{typ unit}]))
                else Const (n, Type ("itself", [@{typ unit}]))
            | fix_type_arg arg = arg
          val args' = map fix_type_arg args
        in
          case head of
            Term.Const (c, _) =>
              (Term.list_comb (Const (c, dummyT), args'), "const: " ^ c)
          | _ => (morphed_lhs, "registered term")
        end
      (* Verbose diagnostics report extra type variables after definition.
         Note: used_tfrees is computed inside the registered_term let block
         above, so we recompute it here for the verbose check. *)
      (* Collect locale TFrees from the expression type constraint + morphed args *)
      val verbose_used_tfrees =
        let val (_, args) = Term.strip_comb morphed_lhs
            val from_args =
              List.foldl (fn (a, acc) => Term.add_tfrees a acc) [] args |> map fst
            val from_constraint =
              Term.add_tfreesT (#ref_addr_ty config) []
              @ Term.add_tfreesT (#ref_gv_ty config) []
              |> map fst
        in distinct (op =) (from_args @ from_constraint) end
      val _ =
        if #verbose config then
          let
            val all_tvars = Term.add_tvars term' []
            val all_tfrees = Term.add_tfrees term' []
            val extra_tfrees = List.filter
              (fn (n, _) => not (member (op =) verbose_used_tfrees n)) all_tfrees
          in
            if null all_tvars andalso null extra_tfrees then ()
            else
              (writeln ("  [verbose] " ^ full_name ^ " type diagnostics:");
               List.app (fn ((n, idx), sort) =>
                 writeln ("    TVar: ?" ^ n ^ "." ^ Int.toString idx ^
                          " :: " ^ @{make_string} sort)) all_tvars;
               List.app (fn (n, sort) =>
                 writeln ("    extra TFree: " ^ n ^
                          " :: " ^ @{make_string} sort)) extra_tfrees)
          end
        else ()
      val _ = writeln ("Defined: " ^ full_name ^ " (" ^ head_desc ^ ")")
    in (registered_term, lthy') end

  fun define_c_global_value prefix name term lthy =
    let
      val full_name = prefix ^ name
      val binding = binding_of_long_name full_name
      val term' = term |> Syntax.check_term lthy
      val ((_, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [shallow_computation_simps]}), term'))
          lthy
      val _ = writeln ("Defined: " ^ full_name)
    in lthy' end

  fun define_named_value full_name term lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val exists_const = can (Proof_Context.read_const {proper = true, strict = true} ctxt) full_name
      val exists_fixed = is_some (Variable.lookup_fixed ctxt full_name)
      val _ =
        if exists_const orelse exists_fixed then
          error
            ("c_source/c_file: generated constant " ^ quote full_name ^
             " already exists")
        else ()
      val binding = binding_of_long_name full_name
      val term' = term |> Syntax.check_term lthy
      val ((_, (_, _)), lthy') =
        Local_Theory.define
          ((binding, NoSyn),
           ((Thm.def_binding binding, @{attributes [shallow_computation_simps]}), term'))
          lthy
      val _ = writeln ("Defined: " ^ full_name)
    in
      lthy'
    end

  val abi_is_big_endian = C_ABI.big_endian

  fun mk_bool_term true = @{term True}
    | mk_bool_term false = @{term False}

  fun define_abi_metadata prefix abi_profile compiler_profile lthy =
    let
      val defs = [
          ("abi_pointer_bits", HOLogic.mk_nat (C_ABI.pointer_bits abi_profile)),
          ("abi_long_bits", HOLogic.mk_nat (C_ABI.long_bits abi_profile)),
          ("abi_char_is_signed", mk_bool_term (#char_is_signed compiler_profile)),
          ("abi_big_endian", mk_bool_term (abi_is_big_endian abi_profile))
        ]
    in
      List.foldl (fn ((suffix, tm), lthy_acc) =>
        define_named_value (prefix ^ suffix) tm lthy_acc) lthy defs
    end

  val intinf_to_int_checked = C_Ast_Utils.intinf_to_int_checked
  val struct_name_of_cty = C_Ast_Utils.struct_name_of_cty

  fun type_exists ctxt tname =
    can (Proof_Context.read_type_name {proper = true, strict = true} ctxt) tname

  fun qualify_typ ctxt (Term.Type (name, args)) =
        let
          val qualified_name =
            (case try (Proof_Context.read_type_name {proper = true, strict = false} ctxt) name of
               SOME ty => fst (Term.dest_Type ty)
             | NONE => name)
        in Term.Type (qualified_name, List.map (qualify_typ ctxt) args) end
    | qualify_typ _ ty = ty

  fun ensure_struct_record prefix (sname, fields) lthy =
    let
      val tname = prefix ^ sname
      val ctxt = Local_Theory.target_of lthy
      val _ =
        if type_exists ctxt tname then
          error
            ("c_source/c_file: generated type " ^ quote tname ^
             " already exists")
        else ()
      val bad_fields =
        List.filter (fn (_, ty_opt) => case ty_opt of NONE => true | SOME _ => false) fields
      val _ =
        if null bad_fields then ()
        else
          error ("c_source: cannot auto-declare struct " ^ tname ^
                 " because field type(s) are unsupported: " ^
                 String.concatWith ", " (List.map #1 bad_fields) ^
                 ". Please provide an explicit datatype_record declaration.")
      val namespace =
        Long_Name.explode tname
        |> rev
        |> tl
        |> rev
      val record_fields =
        List.map (fn (fname, SOME ty) =>
                    (Binding.name (sname ^ "_" ^ fname), ty)
                  | (_, NONE) => raise Match) fields
      val tfrees =
        record_fields
        |> List.foldl (fn ((_, ty), acc) => Term.add_tfreesT ty acc) []
        |> distinct (op =)
      val tfree_subst =
        tfrees
        |> map_index (fn (i, (n, sort)) =>
             ((n, sort), Term.TFree ("'ac" ^ Int.toString i, sort)))
      fun subst_tfree (n, sort) =
        case List.find (fn ((n', s'), _) => n = n' andalso sort = s') tfree_subst of
          SOME (_, t) => t
        | NONE => Term.TFree (n, sort)
      fun subst_ty ty = Term.map_atyps (fn Term.TFree ns => subst_tfree ns | t => t) ty
      val record_fields = List.map (fn (b, ty) => (b, subst_ty ty)) record_fields
      val record_fields = List.map (fn (b, ty) => (b, qualify_typ ctxt ty)) record_fields
      val tyargs =
        List.map (fn (_, t as Term.TFree (_, sort)) => (NONE, (t, sort))
                  | _ => raise Fail "tfree_subst: unexpected non-TFree") tfree_subst
      val (_, lthy') =
        Local_Theory.background_theory_result
          (fn thy =>
            let
              val global_lthy =
                thy
                |> Sign.map_naming (K Name_Space.global_naming)
                |> Named_Target.theory_init
              val global_lthy_scoped =
                fold
                  (fn qualifier =>
                    Local_Theory.map_background_naming
                      (Name_Space.mandatory_path qualifier))
                  namespace
                  global_lthy
              val global_lthy' =
                Datatype_Records.record
                  (Binding.name sname)
                  Datatype_Records.default_ctr_options
                  tyargs
                  record_fields
                  global_lthy_scoped
                |> Local_Theory.restore_background_naming global_lthy
            in
              ((), Local_Theory.exit_global global_lthy')
            end)
          lthy
      val _ = writeln ("Declared datatype_record: " ^ tname)
    in
      lthy'
    end

  fun extract_global_consts (frontend : C_Frontend_Config.t)
      parametric_struct_names union_names typedef_tab struct_tab enum_tab ctxt
      (C_Ast.CTranslUnit0 (ext_decls, _)) =
    let
      val decl_prefix = #decl_prefix frontend
      fun hol_type_of cty = C_Ast_Utils.hol_type_of frontend cty
      val struct_names = Symtab.keys struct_tab
      fun resolve_make_const sname =
        let
          val raw =
            Proof_Context.read_const {proper = true, strict = false} ctxt
              (map_binding_base (fn base => "make_" ^ base)
                (decl_prefix ^ sname))
        in
          (case raw of
             Const (n, _) => Const (n, dummyT)
           | Free (x, _) =>
               (case Variable.lookup_const ctxt x of
                  SOME c => Const (c, dummyT)
                | NONE => Free (x, dummyT))
           | _ => raw)
        end
      fun has_const_qual specs =
        List.exists (fn C_Ast.CTypeQual0 (C_Ast.CConstQual0 _) => true | _ => false) specs
      fun has_static_storage specs =
        List.exists (fn C_Ast.CStorageSpec0 (C_Ast.CStatic0 _) => true | _ => false) specs
      fun has_array_declr (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.exists (fn C_Ast.CArrDeclr0 _ => true | _ => false) derived
      fun array_decl_size (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.mapPartial
              (fn C_Ast.CArrDeclr0 (_, C_Ast.CArrSize0 (_, C_Ast.CConst0
                    (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _))), _) =>
                    if n < 0 then
                      error "c_source: negative array bound not supported"
                    else
                      SOME (intinf_to_int_checked "array bound" n)
                | _ => NONE) derived
            |> (fn n :: _ => SOME n | [] => NONE)
      fun init_scalar_const_value (C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _))) = n
        | init_scalar_const_value (C_Ast.CConst0 (C_Ast.CCharConst0 (C_Ast.CChar0 (c, _), _))) =
            C_Ast.integer_of_char c
        | init_scalar_const_value (C_Ast.CConst0 (C_Ast.CCharConst0 (C_Ast.CChars0 _, _))) =
            error "c_source: multi-character constant not supported in initializers"
        | init_scalar_const_value (C_Ast.CVar0 (ident, _)) =
            let val name = C_Ast_Utils.ident_name ident
            in case Symtab.lookup enum_tab name of
                 SOME value => IntInf.fromInt value
               | NONE =>
                   error ("c_source: unsupported global initializer element: " ^ name)
            end
        | init_scalar_const_value (C_Ast.CUnary0 (C_Ast.CMinOp0, e, _)) =
            IntInf.~ (init_scalar_const_value e)
        | init_scalar_const_value (C_Ast.CUnary0 (C_Ast.CPlusOp0, e, _)) =
            init_scalar_const_value e
        | init_scalar_const_value (C_Ast.CCast0 (_, e, _)) =
            init_scalar_const_value e
        | init_scalar_const_value _ =
            error "c_source: non-constant global initializer element"
      fun default_const_term (C_Ast_Utils.CBool) = Const (\<^const_name>\<open>False\<close>, @{typ bool})
        | default_const_term (C_Ast_Utils.CPtr _) =
            Const (\<^const_name>\<open>c_uninitialized\<close>, dummyT)
        | default_const_term (C_Ast_Utils.CStruct sname) =
            let
              val fields =
                (case Symtab.lookup struct_tab sname of
                   SOME fs => fs
                 | NONE => error ("c_source: unknown struct in global initializer: " ^ sname))
              val make_const = resolve_make_const sname
              val field_vals = List.map (fn (_, field_cty) => default_const_term field_cty) fields
            in
              List.foldl (fn (v, acc) => acc $ v) make_const field_vals
            end
        | default_const_term cty =
            HOLogic.mk_number (hol_type_of cty) 0
      fun init_expr_const_term (C_Ast_Utils.CPtr _)
              (C_Ast.CConst0 (C_Ast.CStrConst0 (C_Ast.CString0 (abr_str, _), _))) =
            let val s = C_Ast_Utils.abr_string_to_string abr_str
                val char_ty = hol_type_of C_Ast_Utils.CChar
                val bytes = List.map (fn c => HOLogic.mk_number char_ty (Char.ord c))
                              (String.explode s)
                val with_null = bytes @ [HOLogic.mk_number char_ty 0]
            in HOLogic.mk_list char_ty with_null end
        | init_expr_const_term (C_Ast_Utils.CPtr _) _ =
            Const (\<^const_name>\<open>c_uninitialized\<close>, dummyT)
        | init_expr_const_term _ (C_Ast.CConst0 (C_Ast.CStrConst0 (C_Ast.CString0 (_, _), _))) =
                 error "c_source: string literal initializer requires char pointer target"
        | init_expr_const_term target_cty expr =
            HOLogic.mk_number (hol_type_of target_cty)
              (intinf_to_int_checked "global initializer literal"
                (init_scalar_const_value expr))
      fun init_struct_const_term sname init_list =
            let
              val fields =
                (case Symtab.lookup struct_tab sname of
                   SOME fs => fs
                 | NONE => error ("c_source: unknown struct in global initializer: " ^ sname))
              fun find_field_index _ [] _ =
                    error "c_source: struct field not found in global initializer"
                | find_field_index fname ((n, _) :: rest) i =
                    if n = fname then i else find_field_index fname rest (i + 1)
              fun resolve_field_desig [] pos = pos
                | resolve_field_desig [C_Ast.CMemberDesig0 (ident, _)] _ =
                    find_field_index (C_Ast_Utils.ident_name ident) fields 0
                | resolve_field_desig _ _ =
                    error "c_source: complex designator in global struct initializer"
              fun collect_field_items [] _ = []
                | collect_field_items ((desigs, init_item) :: rest) pos =
                    let val idx = resolve_field_desig desigs pos
                    in (idx, init_item) :: collect_field_items rest (idx + 1) end
              val field_items = collect_field_items init_list 0
              val _ = List.app (fn (idx, _) =>
                        if idx < 0 orelse idx >= List.length fields
                        then error "c_source: struct designator index out of bounds in global initializer"
                        else ()) field_items
              val base_vals = List.map (fn (_, field_cty) => default_const_term field_cty) fields
              val filled =
                List.foldl
                  (fn ((idx, init_item), acc) =>
                    let
                      val (_, field_cty) = List.nth (fields, idx)
                      val v = init_value_term field_cty init_item
                    in
                      nth_map idx (K v) acc
                    end)
                  base_vals
                  field_items
              val make_const = resolve_make_const sname
            in
              List.foldl (fn (v, acc) => acc $ v) make_const filled
            end
      and init_value_term target_cty (C_Ast.CInitExpr0 (expr, _)) =
            init_expr_const_term target_cty expr
        | init_value_term (C_Ast_Utils.CStruct sname) (C_Ast.CInitList0 (init_list, _)) =
            init_struct_const_term sname init_list
        | init_value_term target_cty (C_Ast.CInitList0 (init_list, _)) =
            (* Sub-array initializer: build a list of recursively initialized elements *)
            let
              val elem_hol_ty = hol_type_of target_cty
              fun collect [] _ = []
                | collect (([], item) :: rest) pos =
                    (pos, item) :: collect rest (pos + 1)
                | collect ((desigs, item) :: rest) _ =
                    let val idx =
                      (case desigs of
                         [C_Ast.CArrDesig0 (C_Ast.CConst0 (C_Ast.CIntConst0
                            (C_Ast.CInteger0 (n, _, _), _)), _)] =>
                           intinf_to_int_checked "sub-array designator" n
                       | _ => error "c_source: complex designator in nested array initializer")
                    in (idx, item) :: collect rest (idx + 1) end
              val indexed = collect init_list 0
              val arr_size =
                List.foldl (fn ((i, _), acc) => Int.max (acc, i + 1)) 0 indexed
              val zero = default_const_term target_cty
              val base = List.tabulate (arr_size, fn _ => zero)
              val filled = List.foldl
                (fn ((i, item), acc) =>
                  nth_map i (K (init_value_term target_cty item)) acc)
                base indexed
            in HOLogic.mk_list elem_hol_ty filled end
        | init_value_term _ _ =
            error "c_source: unsupported non-constant global initializer shape"
      fun process_decl specs declarators =
        if not (has_const_qual specs orelse has_static_storage specs) then []
        else
          let
            val base_cty =
              (case C_Ast_Utils.resolve_c_type_full frontend typedef_tab specs of
                 SOME C_Ast_Utils.CVoid => C_Ast_Utils.CInt
               | SOME t => t
               | NONE =>
                   (case C_Ast_Utils.extract_struct_type_from_specs_full struct_names specs of
                      SOME sn => C_Ast_Utils.CStruct sn
                    | NONE =>
                        (case C_Ast_Utils.extract_union_type_from_specs_full
                          union_names specs of
                           SOME un => C_Ast_Utils.CUnion un
                         | NONE => C_Ast_Utils.CInt)))
            fun process_one ((C_Ast.Some declr, C_Ast.Some (C_Ast.CInitExpr0 (init, _))), _) =
                  let
                    val name = C_Ast_Utils.declr_name declr
                    val ptr_depth = C_Ast_Utils.pointer_depth_of_declr declr
                    val actual_cty = C_Ast_Utils.apply_ptr_depth base_cty ptr_depth
                    val init_term = init_expr_const_term actual_cty init
                    val arr_meta =
                      (case array_decl_size declr of
                         SOME n =>
                           if ptr_depth > 0
                           then SOME (C_Ast_Utils.apply_ptr_depth base_cty (ptr_depth - 1), n)
                           else NONE
                       | NONE => NONE)
                  in SOME (name, init_term, actual_cty, arr_meta, struct_name_of_cty actual_cty) end
              | process_one ((C_Ast.Some declr, C_Ast.Some (C_Ast.CInitList0 (init_list, _))), _) =
                  let
                    val name = C_Ast_Utils.declr_name declr
                    val _ =
                      if has_array_declr declr then ()
                      else error "c_source: initializer list for non-array global declaration"
                    val ptr_depth = C_Ast_Utils.pointer_depth_of_declr declr
                    val actual_cty = C_Ast_Utils.apply_ptr_depth base_cty ptr_depth
                    val elem_cty =
                      if ptr_depth > 0 then C_Ast_Utils.apply_ptr_depth base_cty (ptr_depth - 1) else base_cty
                    fun expand_desig [] pos init_item = [(pos, init_item)]
                      | expand_desig [C_Ast.CArrDesig0 (C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (n, _, _), _)), _)] _ init_item =
                          [(intinf_to_int_checked "global array designator" n, init_item)]
                      | expand_desig [C_Ast.CRangeDesig0 (
                            C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (lo_n, _, _), _)),
                            C_Ast.CConst0 (C_Ast.CIntConst0 (C_Ast.CInteger0 (hi_n, _, _), _)), _)] _ init_item =
                          let val lo = intinf_to_int_checked "range designator lo" lo_n
                              val hi = intinf_to_int_checked "range designator hi" hi_n
                          in List.tabulate (hi - lo + 1, fn i => (lo + i, init_item)) end
                      | expand_desig _ _ _ =
                          error "c_source: complex designator in global array initializer"
                    fun collect_indices [] _ = []
                      | collect_indices ((desigs, init_item) :: rest) pos =
                          let val items = expand_desig desigs pos init_item
                              val next_pos = #1 (List.last items) + 1
                          in items @ collect_indices rest next_pos end
                    val indexed_items = collect_indices init_list 0
                    val declared_size = array_decl_size declr
                    val arr_size =
                      case declared_size of
                        SOME n => n
                      | NONE =>
                          List.foldl (fn ((idx, _), acc) => Int.max (acc, idx + 1)) 0 indexed_items
                    val _ = List.app (fn (idx, _) =>
                              if idx < 0 orelse idx >= arr_size
                              then error ("c_source: designator index " ^
                                          Int.toString idx ^ " out of bounds for global array of size " ^
                                          Int.toString arr_size)
                              else ()) indexed_items
                    val zero_value = default_const_term elem_cty
                    val base_values = List.tabulate (arr_size, fn _ => zero_value)
                    val filled_values =
                      List.foldl
                        (fn ((idx, init_item), acc) =>
                          nth_map idx (K (init_value_term elem_cty init_item)) acc)
                        base_values
                        indexed_items
                    val list_term = HOLogic.mk_list (hol_type_of elem_cty) filled_values
                    val arr_meta =
                      SOME (elem_cty, arr_size)
                  in SOME (name, list_term, actual_cty, arr_meta, struct_name_of_cty actual_cty) end
              | process_one ((C_Ast.Some _, C_Ast.None), _) = NONE
              | process_one _ =
                  error "c_source: unsupported global declarator"
          in List.mapPartial process_one declarators end
      fun resolve_decl_type_early (C_Ast.CDecl0 (specs, _, _)) =
            C_Ast_Utils.resolve_c_type_full frontend typedef_tab specs
        | resolve_decl_type_early _ = NONE
      fun check_static_assert expr msg_lit =
            let val v =
              C_Ast_Utils.eval_const_int_expr frontend resolve_decl_type_early expr
            in if v = 0 then
                 error ("c_source: _Static_assert failed: " ^
                        C_Ast_Utils.extract_string_literal msg_lit)
               else ()
            end
      fun from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CDecl0 (specs, declarators, _))) =
            process_decl specs declarators
        | from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CStaticAssert0 (expr, msg_lit, _))) =
            (check_static_assert expr msg_lit; [])
        | from_ext_decl _ = []
    in
      List.concat (List.map from_ext_decl ext_decls)
    end

  (* Phase 2: Extract struct, union, enum, and typedef definitions from the
     translation unit.  Returns all type-level tables needed by later phases. *)
  fun extract_type_definitions frontend keep_type tu =
    let
      val decl_prefix = #decl_prefix (frontend : C_Frontend_Config.t)
      val builtin_typedefs = C_Ast_Utils.builtin_typedefs frontend
      (* Use fold/update to allow user typedefs to override builtins. *)
      val typedef_defs_early =
        builtin_typedefs @ C_Ast_Utils.extract_typedefs frontend tu
      val typedef_tab_early = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                                Symtab.empty typedef_defs_early
      (* Selection controls which HOL type declarations are installed, not
         which source-level type information is available while translating
         selected functions.  Keep the complete aggregate environment here so
         a later, function-only extraction phase can use an already-installed
         record type. *)
      val struct_defs =
        C_Ast_Utils.extract_struct_defs_with_types frontend typedef_tab_early tu
      val parametric_struct_names =
        C_Ast_Utils.derive_parametric_struct_names struct_defs
      val parametric_struct_tab =
        Symtab.make (map (fn name => (name, ())) parametric_struct_names)
      val struct_record_defs =
        List.filter (fn (n, _) => keep_type n)
          (C_Ast_Utils.extract_struct_record_defs frontend parametric_struct_tab
            decl_prefix typedef_tab_early tu)
      val struct_array_field_tab =
        Symtab.make (C_Ast_Utils.extract_struct_array_fields tu)
      val union_defs =
        C_Ast_Utils.extract_union_defs_with_types frontend typedef_tab_early tu
      val union_names = List.map #1 union_defs
      val struct_tab = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                         (Symtab.make struct_defs) union_defs
      val _ = List.app (fn (sname, fields) =>
        writeln ("Registered struct: " ^ sname ^ " with fields: " ^
                 String.concatWith ", " (List.map #1 fields))) struct_defs
      val _ = List.app (fn (uname, fields) =>
        writeln ("Registered union: " ^ uname ^ " with fields: " ^
                 String.concatWith ", " (List.map #1 fields))) union_defs
      val enum_defs = C_Ast_Utils.extract_enum_defs tu
      val enum_tab = Symtab.make enum_defs
      val _ = if null enum_defs then () else
        List.app (fn (name, value) =>
          writeln ("Registered enum constant: " ^ name ^ " = " ^
                   Int.toString value)) enum_defs
      val typedef_defs =
        builtin_typedefs @ C_Ast_Utils.extract_typedefs frontend tu
      val typedef_tab = List.foldl (fn ((n, v), tab) => Symtab.update (n, v) tab)
                          Symtab.empty typedef_defs
      val _ = if null typedef_defs then () else
        List.app (fn (name, _) =>
          writeln ("Registered typedef: " ^ name)) typedef_defs
      (* Check _Static_assert declarations at top level *)
      val C_Ast.CTranslUnit0 (all_ext_decls, _) = tu
      fun resolve_decl_type_sa (C_Ast.CDecl0 (specs, _, _)) =
            C_Ast_Utils.resolve_c_type_full frontend typedef_tab specs
        | resolve_decl_type_sa _ = NONE
      val _ = List.app
        (fn C_Ast.CDeclExt0 (C_Ast.CStaticAssert0 (expr, msg_lit, _)) =>
              let val v =
                C_Ast_Utils.eval_const_int_expr frontend resolve_decl_type_sa expr
              in if v = 0 then
                   error ("c_source: _Static_assert failed: " ^
                          C_Ast_Utils.extract_string_literal msg_lit)
                 else ()
              end
          | _ => ()) all_ext_decls
    in
      { struct_tab = struct_tab, union_names = union_names,
        parametric_struct_names = parametric_struct_tab,
        struct_record_defs = struct_record_defs,
        struct_array_field_tab = struct_array_field_tab,
        enum_tab = enum_tab, typedef_tab = typedef_tab }
    end

  (* Phase 3: Extract function definitions, compute signatures, topologically
     sort by call dependencies, and identify pure functions. *)
  fun extract_and_order_functions frontend keep_func typedef_tab tu =
    let
      val fundefs_raw =
        List.filter
          (fn C_Ast.CFunDef0 (_, declr, _, _, _) => keep_func (C_Ast_Utils.declr_name declr))
          (C_Ast_Utils.extract_fundefs tu)
      fun param_cty_of_decl pdecl =
            (case pdecl of
               C_Ast.CDecl0 (specs, _, _) =>
                 let
                   val base =
                     (case C_Ast_Utils.resolve_c_type_full frontend typedef_tab specs of
                                 SOME t => t
                               | NONE => C_Ast_Utils.CInt)
                   val depth = C_Ast_Utils.pointer_depth_of_decl pdecl
                 in C_Ast_Utils.apply_ptr_depth base depth end
             | _ => C_Ast_Utils.CInt)
      fun signature_of_declr specs declr =
            let val fname = C_Ast_Utils.declr_name declr
                val _ =
                  if C_Ast_Utils.declr_is_variadic declr then
                    error ("c_source: unsupported C construct: variadic function declaration: " ^ fname)
                  else ()
                val rty_base =
                  (case C_Ast_Utils.resolve_c_type_full frontend typedef_tab specs of
                                  SOME C_Ast_Utils.CVoid => C_Ast_Utils.CVoid
                                | SOME t => t | NONE => C_Ast_Utils.CInt)
                val rty = C_Ast_Utils.apply_ptr_depth rty_base
                            (C_Ast_Utils.pointer_depth_of_declr declr)
                val ptys = List.map param_cty_of_decl (C_Ast_Utils.extract_param_decls declr)
            in (fname, (rty, ptys)) end
      fun declr_is_function (C_Ast.CDeclr0 (_, derived, _, _, _)) =
            List.exists (fn C_Ast.CFunDeclr0 _ => true | _ => false) derived
      fun signatures_from_ext_decl (C_Ast.CDeclExt0 (C_Ast.CDecl0 (specs, declarators, _))) =
            List.mapPartial
              (fn ((C_Ast.Some declr, _), _) =>
                    if declr_is_function declr andalso keep_func (C_Ast_Utils.declr_name declr)
                    then SOME (signature_of_declr specs declr) else NONE
                | _ => NONE)
              declarators
        | signatures_from_ext_decl _ = []
      val C_Ast.CTranslUnit0 (ext_decls, _) = tu
      fun fundef_signature (C_Ast.CFunDef0 (specs, declr, _, _, _)) =
            signature_of_declr specs declr
      val decl_signatures = List.concat (List.map signatures_from_ext_decl ext_decls)
      fun fundef_name (C_Ast.CFunDef0 (_, declr, _, _, _)) = C_Ast_Utils.declr_name declr
      val fun_names = List.map fundef_name fundefs_raw
      val fun_name_tab = Symtab.make (List.map (fn n => (n, ())) fun_names)
      val dep_tab =
        List.foldl
          (fn (fdef, tab) =>
            let
              val name = fundef_name fdef
              val deps =
                List.filter (fn n => n <> name andalso Symtab.defined fun_name_tab n)
                  (C_Ast_Utils.find_called_functions fdef)
            in
              Symtab.update (name, deps) tab
            end)
          Symtab.empty fundefs_raw
      val fundef_tab = Symtab.make (List.map (fn fdef => (fundef_name fdef, fdef)) fundefs_raw)
      val decl_order_names = distinct (op =) (List.map #1 decl_signatures)
      val preferred_names =
        decl_order_names @
        List.filter (fn n => not (List.exists (fn m => m = n) decl_order_names)) fun_names
      fun visit stack seen order name =
        if Symtab.defined seen name then (seen, order, false)
        else if List.exists (fn n => n = name) stack then
          (seen, order, true)
        else
          let
            val deps = the_default [] (Symtab.lookup dep_tab name)
            val (seen', order', has_cycle) =
              List.foldl
                (fn (d, (s, ord, cycle)) =>
                  let val (s', ord', cycle') = visit (name :: stack) s ord d
                  in (s', ord', cycle orelse cycle') end)
                (seen, order, false) deps
            val seen'' = Symtab.update (name, ()) seen'
          in
            (seen'', order' @ [name], has_cycle)
          end
      val (_, topo_names, has_cycle) =
        List.foldl
          (fn (n, (s, ord, cycle)) =>
            let val (s', ord', cycle') = visit [] s ord n
            in (s', ord', cycle orelse cycle') end)
          (Symtab.empty, [], false) preferred_names
      val _ =
        if has_cycle then
          writeln "c_source: recursion cycle detected; using deterministic SCC fallback order"
        else ()
      val fundefs = List.mapPartial (fn n => Symtab.lookup fundef_tab n) topo_names
      val _ = List.app (fn C_Ast.CFunDef0 (_, declr, _, _, _) =>
                  let val name = C_Ast_Utils.declr_name declr
                  in if C_Ast_Utils.declr_is_variadic declr then
                       error ("c_source: unsupported C construct: variadic function definition: " ^ name)
                     else ()
                  end) fundefs
      fun refine_pure_functions pure_tab =
        let
          val pure_tab' =
            List.foldl
              (fn (fdef, tab) =>
                let val name = fundef_name fdef
                in
                  if C_Ast_Utils.fundef_is_pure_with pure_tab fdef then
                    Symtab.update (name, ()) tab
                  else tab
                end)
              Symtab.empty fundefs_raw
        in
          if Symtab.dest pure_tab' = Symtab.dest pure_tab then pure_tab
          else refine_pure_functions pure_tab'
        end
      val pure_fun_tab = refine_pure_functions fun_name_tab
      val signatures = decl_signatures @ List.map fundef_signature fundefs
      val func_ret_table = List.foldl
        (fn ((n, (rty, _)), tab) => Symtab.update (n, rty) tab)
        Symtab.empty signatures
      val func_ret_types = func_ret_table
      val func_param_table = List.foldl
        (fn ((n, (_, ptys)), tab) => Symtab.update (n, ptys) tab)
        Symtab.empty signatures
      val func_param_types = func_param_table
    in
      { fundefs = fundefs, fundefs_raw = fundefs_raw,
        param_cty_of_decl = param_cty_of_decl,
        pure_function_names = pure_fun_tab,
        func_ret_types = func_ret_types,
        func_param_types = func_param_types }
    end

  (* Phase 4: Determine which pointer parameters are list-backed (passed as
     arrays at all call sites). *)
  fun analyze_list_backed_params struct_tab struct_array_field_tab union_names
        param_cty_of_decl fundefs_raw =
    let
      val all_struct_names = Symtab.keys struct_tab
      fun has_static_storage specs =
        List.exists (fn C_Ast.CStorageSpec0 (C_Ast.CStatic0 _) => true | _ => false) specs
      fun param_declr_of_decl (C_Ast.CDecl0 (_, declarators, _)) =
            (case declarators of
               ((C_Ast.Some declr, _), _) :: _ => SOME declr
             | _ => NONE)
        | param_declr_of_decl _ = NONE
      fun param_decl_has_array pdecl =
        (case param_declr_of_decl pdecl of
           SOME (C_Ast.CDeclr0 (_, derived, _, _, _)) =>
             List.exists (fn C_Ast.CArrDeclr0 _ => true | _ => false) derived
         | NONE => false)
      fun fundef_name (C_Ast.CFunDef0 (_, declr, _, _, _)) = C_Ast_Utils.declr_name declr
      val list_backed_alias_envs =
        List.foldl
          (fn (fdef, tab) =>
            Symtab.update (fundef_name fdef, C_Ast_Utils.find_list_backed_aliases struct_tab struct_array_field_tab fdef) tab)
          Symtab.empty fundefs_raw
      val caller_struct_envs =
        List.foldl
          (fn (C_Ast.CFunDef0 (_, declr, _, _, _), tab) =>
            let
              val fname = C_Ast_Utils.declr_name declr
              val pdecls = C_Ast_Utils.extract_param_decls declr
              val struct_env =
                List.foldl
                  (fn (pdecl, env) =>
                    case (param_declr_of_decl pdecl,
                          C_Ast_Utils.extract_struct_type_from_decl_full all_struct_names pdecl) of
                      (SOME pdeclr, SOME sname) =>
                        Symtab.update (C_Ast_Utils.declr_name pdeclr, sname) env
                    | _ =>
                        (case (param_declr_of_decl pdecl,
                               C_Ast_Utils.extract_union_type_from_decl_full union_names pdecl) of
                           (SOME pdeclr, SOME uname) =>
                             Symtab.update (C_Ast_Utils.declr_name pdeclr, uname) env
                         | _ => env))
                  Symtab.empty pdecls
            in
              Symtab.update (fname, struct_env) tab
            end)
          Symtab.empty fundefs_raw
      val call_sites =
        List.concat
          (List.map
            (fn fdef =>
              let
                val caller = fundef_name fdef
                val caller_aliases = the_default [] (Symtab.lookup list_backed_alias_envs caller)
                val caller_struct_env = the_default Symtab.empty (Symtab.lookup caller_struct_envs caller)
              in
                List.map (fn (callee, args) => (caller_aliases, caller_struct_env, callee, args))
                  (C_Ast_Utils.find_named_calls_with_args fdef)
              end)
            fundefs_raw)
      fun arg_is_list_backed caller_aliases caller_struct_env arg =
        (case arg of
           C_Ast.CVar0 (ident, _) =>
             List.exists (fn n => n = C_Ast_Utils.ident_name ident) caller_aliases
         | C_Ast.CMember0 (base, field_ident, _, _) =>
             let
               fun expr_struct_name (C_Ast.CVar0 (ident, _)) =
                     Symtab.lookup caller_struct_env (C_Ast_Utils.ident_name ident)
                 | expr_struct_name (C_Ast.CCast0 (_, e, _)) = expr_struct_name e
                 | expr_struct_name _ = NONE
             in
               (case expr_struct_name base of
                  SOME struct_name =>
                    List.exists (fn fname => fname = C_Ast_Utils.ident_name field_ident)
                      (the_default [] (Symtab.lookup struct_array_field_tab struct_name))
                | NONE => false)
             end
         | _ => false)
      val list_backed_param_modes =
        List.foldl
          (fn (fdef as C_Ast.CFunDef0 (specs, declr, _, _, _), tab) =>
            let
              val fname = fundef_name fdef
              val indexed_names = C_Ast_Utils.find_indexed_base_vars fdef
              val pdecls = C_Ast_Utils.extract_param_decls declr
              fun mode_for_param (i, pdecl) =
                let
                  val pname = the_default "" (C_Ast_Utils.param_name pdecl)
                  val p_cty = param_cty_of_decl pdecl
                  val relevant_calls =
                    List.filter (fn (_, _, callee, args) => callee = fname andalso i < List.length args) call_sites
                in
                  if param_decl_has_array pdecl then true
                  else if not (C_Ast_Utils.is_ptr p_cty) then false
                  else if not (has_static_storage specs) then false
                  else if not (List.exists (fn n => n = pname) indexed_names) then false
                  else not (null relevant_calls) andalso
                    List.all (fn (caller_aliases, caller_struct_env, _, args) =>
                      arg_is_list_backed caller_aliases caller_struct_env (List.nth (args, i))) relevant_calls
                end
              val modes = map_index mode_for_param pdecls
            in
              Symtab.update (fname, modes) tab
            end)
          Symtab.empty fundefs_raw
    in list_backed_param_modes end

  fun selected_name_filter names =
    (case names of
       NONE => K true
     | SOME selected =>
         let
           val table =
             fold (fn name => Symtab.update (name, ()))
               selected Symtab.empty
         in
           Symtab.defined table
         end)

  (* The immutable result of the analysis pass.  It contains every side table
     needed by lowering; no command-global configuration or translation state
     is consulted after this point. *)
  fun analyze_translation_unit frontend
      ({functions = selected_functions, types = selected_types}: manifest) tu =
    let
      val keep_func = selected_name_filter selected_functions
      val keep_type = selected_name_filter selected_types
      val {struct_tab, union_names, parametric_struct_names,
            struct_record_defs, struct_array_field_tab, enum_tab, typedef_tab} =
        extract_type_definitions frontend keep_type tu
      val {fundefs, fundefs_raw, param_cty_of_decl, pure_function_names,
            func_ret_types, func_param_types} =
        extract_and_order_functions frontend keep_func typedef_tab tu
      val list_backed_param_modes =
        analyze_list_backed_params struct_tab struct_array_field_tab
          union_names param_cty_of_decl fundefs_raw
    in
      {struct_tab = struct_tab,
       union_names = union_names,
       parametric_struct_names = parametric_struct_names,
       struct_record_defs = struct_record_defs,
       struct_array_field_tab = struct_array_field_tab,
       enum_tab = enum_tab,
       typedef_tab = typedef_tab,
       fundefs = fundefs,
       fundefs_raw = fundefs_raw,
       param_cty_of_decl = param_cty_of_decl,
       pure_function_names = pure_function_names,
       func_ret_types = func_ret_types,
       func_param_types = func_param_types,
       list_backed_param_modes = list_backed_param_modes}: analysis
    end

  fun planned_global_names
      (C_Ast.CTranslUnit0 (ext_decls, _)) =
    let
      fun has_const_qual specs =
        List.exists
          (fn C_Ast.CTypeQual0 (C_Ast.CConstQual0 _) => true
            | _ => false)
          specs
      fun has_static_storage specs =
        List.exists
          (fn C_Ast.CStorageSpec0 (C_Ast.CStatic0 _) => true
            | _ => false)
          specs
      fun from_declarator
          ((C_Ast.Some declr, C_Ast.Some _), _) =
            SOME (C_Ast_Utils.declr_name declr)
        | from_declarator _ = NONE
      fun from_ext_decl
          (C_Ast.CDeclExt0
            (C_Ast.CDecl0 (specs, declarators, _))) =
            if has_const_qual specs orelse has_static_storage specs
            then map_filter from_declarator declarators
            else []
        | from_ext_decl _ = []
    in
      maps from_ext_decl ext_decls
    end

  fun declaration_plan ({frontend, manifest, define_abi_metadata}: config) tu _ =
    let
      val decl_prefix = #decl_prefix frontend
      val {functions, types} = manifest
      val keep_func = selected_name_filter functions
      val keep_type = selected_name_filter types
      val typedef_defs =
        C_Ast_Utils.builtin_typedefs frontend @
        C_Ast_Utils.extract_typedefs frontend tu
      val typedef_tab =
        fold (fn (name, cty) => Symtab.update (name, cty))
          typedef_defs Symtab.empty
      val struct_defs =
        C_Ast_Utils.extract_struct_defs_with_types frontend typedef_tab tu
      val parametric_struct_names =
        C_Ast_Utils.derive_parametric_struct_names struct_defs
        |> map (fn name => (name, ()))
        |> Symtab.make
      val struct_records =
        C_Ast_Utils.extract_struct_record_defs
          frontend parametric_struct_names decl_prefix typedef_tab tu
        |> filter (keep_type o #1)
      val function_names =
        C_Ast_Utils.extract_fundefs tu
        |> map (fn C_Ast.CFunDef0 (_, declr, _, _, _) =>
             C_Ast_Utils.declr_name declr)
        |> filter keep_func
      val global_names = planned_global_names tu
      val pos = Position.none
      fun declare kind name plan =
        Declaration_Plan.declare kind
          (binding_of_long_name name) plan
      fun declare_record (sname, fields) plan =
        let
          val plan =
            declare Declaration_Plan.Type_Constructor
              (decl_prefix ^ sname) plan
          val plan =
            declare Declaration_Plan.Constant
              (decl_prefix ^ "make_" ^ sname) plan
          fun declare_field (field_name, _) plan =
            plan
            |> declare Declaration_Plan.Constant
                 (decl_prefix ^ sname ^ "_" ^ field_name)
            |> declare Declaration_Plan.Constant
                 (decl_prefix ^ "update_" ^ sname ^ "_" ^ field_name)
        in
          fold declare_field fields plan
        end
      val plan =
        Declaration_Plan.empty
        |> Declaration_Plan.require_term
             "configured C abort handler" pos (#abort_handler frontend)
        |> fold declare_record struct_records
        |> fold
             (fn name =>
               declare Declaration_Plan.Constant
                 (decl_prefix ^ name))
             global_names
        |> fold
             (fn name =>
               declare Declaration_Plan.Constant
                 (decl_prefix ^ name))
             function_names
      val plan =
        if define_abi_metadata then
          fold
            (fn suffix =>
              declare Declaration_Plan.Constant
                (decl_prefix ^ suffix))
            ["abi_pointer_bits", "abi_long_bits",
             "abi_char_is_signed", "abi_big_endian"]
            plan
        else plan
    in
      plan
    end

  (* Pass 3: lower the original AST using the immutable analysis side tables,
     then install the already-planned declarations transactionally. *)
  fun process_translation_unit
      ({frontend, manifest, define_abi_metadata = install_abi_metadata}: config) tu lthy =
    let
      val decl_prefix = #decl_prefix frontend
      val abi_profile = #abi_profile frontend
      val compiler_profile = #compiler_profile frontend
      val {struct_tab, union_names, parametric_struct_names,
            struct_record_defs, struct_array_field_tab, enum_tab, typedef_tab,
            fundefs, fundefs_raw = _, param_cty_of_decl = _,
            pure_function_names, func_ret_types, func_param_types,
            list_backed_param_modes} =
        analyze_translation_unit frontend manifest tu

      val lthy =
        List.foldl (fn (sdef, lthy_acc) => ensure_struct_record decl_prefix sdef lthy_acc)
          lthy struct_record_defs
      val global_const_inits =
        extract_global_consts frontend parametric_struct_names union_names
          typedef_tab struct_tab enum_tab (Local_Theory.target_of lthy) tu
      val (lthy, global_consts) =
        List.foldl (fn ((gname, init_term, gcty, garr_meta, gstruct), (lthy_acc, acc)) =>
          let
            val lthy' = define_c_global_value decl_prefix gname init_term lthy_acc
            val ctxt' = Local_Theory.target_of lthy'
            val (full_name, _) =
              Term.dest_Const
                (Proof_Context.read_const {proper = true, strict = false} ctxt'
                  (decl_prefix ^ gname))
            val gterm = Const (full_name, dummyT)
          in
            (lthy', acc @ [(gname, gterm, gcty, garr_meta, gstruct)])
          end)
        (lthy, []) global_const_inits
      val lthy =
        (* Define ABI metadata after type-generation commands (e.g. datatype_record)
           so locale-target equations from these definitions cannot interfere with
           datatype package obligations. *)
        if install_abi_metadata
        then define_abi_metadata decl_prefix abi_profile compiler_profile lthy
        else lthy
      fun translate_one
          (fundef, (lthy_acc, defined_func_consts, defined_func_fuels)) =
        let
          val lowering_env : C_Lowering_Env.t =
            {config = frontend,
             parametric_struct_names = parametric_struct_names,
             pure_function_names = pure_function_names,
             union_names = union_names,
             struct_array_fields = struct_array_field_tab,
             list_backed_param_modes = list_backed_param_modes,
             defined_func_consts = defined_func_consts,
             defined_func_fuels = defined_func_fuels,
             return_cty = C_Ast_Utils.CInt,
             loop_written_vars = []}
          val (name, term, fuel_count) =
            C_Translate.translate_fundef lowering_env
              struct_tab enum_tab typedef_tab func_ret_types func_param_types
              global_consts lthy_acc fundef
          val (registered_term, lthy_acc') =
            define_c_function frontend decl_prefix name term lthy_acc
          val full_name = decl_prefix ^ name
          val defined_func_consts' =
            Symtab.update (full_name, registered_term) defined_func_consts
          val defined_func_fuels' =
            if fuel_count = 0 then defined_func_fuels
            else Symtab.update (full_name, fuel_count) defined_func_fuels
        in
          (lthy_acc', defined_func_consts', defined_func_fuels')
        end
    in
      (* Phase 6: Translate and define each function one at a time, so that later
         functions can reference earlier ones via Syntax.check_term. *)
      #1 (List.foldl translate_one
        (lthy, Symtab.empty, Symtab.empty) fundefs)
    end
end
\<close>

subsection \<open>Shared command configuration\<close>

ML \<open>
  val parse_abi_ident = Scan.one (Token.ident_with (K true)) >> Token.content_of
  val parse_abi_dash =
      Scan.one (fn tok => Token.is_kind Token.Sym_Ident tok andalso Token.content_of tok = "-") >> K ()
  val parse_abi_name =
      parse_abi_ident -- Scan.repeat (parse_abi_dash |-- parse_abi_ident)
      >> (fn (h, t) => String.concatWith "-" (h :: t))

  type translate_opts = {
    prefix: string option, addr: string option, gv: string option,
    abi: string option, abort: string option,
    ptr_add: string option, ptr_shift_signed: string option, ptr_diff: string option,
    compiler: string option,
    verbose: bool
  }

  fun read_abort_handler cmd_name lthy source =
    let
      val handler =
        source
        |> Syntax.read_term lthy
        |> Syntax.check_term lthy
      val (head, arguments) = Term.strip_comb handler
      val _ =
        (case (head, arguments) of
           (Const _, []) => ()
         | _ =>
             error
               (cmd_name ^ ": abort option must name a HOL constant, found " ^
                quote (Syntax.string_of_term lthy handler)))
      val handler_type = fastype_of handler
      val argument_types = binder_types handler_type
      val result_type = body_type handler_type
      val abort_type =
        (case result_type of
           Type (name, [_, _, _, abort_type, _, _]) =>
             if name = \<^type_name>\<open>expression\<close>
             then abort_type
             else
               error
                 (cmd_name ^
                  ": abort constant must return a shallow expression")
         | _ =>
             error
               (cmd_name ^
                ": abort constant must return a shallow expression"))
      val _ =
        (case argument_types of
           [payload_type] =>
             if Type.could_unify (payload_type, \<^typ>\<open>c_abort\<close>) then ()
             else
               error
                 (cmd_name ^
                  ": abort constant must accept a c_abort reason")
         | [] =>
             error
               (cmd_name ^
                ": abort constant must accept an abort payload")
         | _ =>
             error
               (cmd_name ^
                ": abort constant must accept exactly one c_abort reason"))
    in
      (handler, abort_type)
    end

  fun setup_translation_context cmd_name (opts : translate_opts) lthy =
    let
      val prefix =
        (case #prefix opts of
           SOME value => value
         | NONE => error (cmd_name ^ ": missing mandatory unit namespace"))
      val abi_profile = C_ABI.parse_profile (the_default "lp64-le" (#abi opts))
      val compiler_profile =
        (case #compiler opts of
           SOME name => C_Compiler.parse_compiler name
         | NONE => C_Compiler.default_profile)
      val addr_ty = Syntax.read_typ lthy (the_default "'addr" (#addr opts))
      val gv_ty = Syntax.read_typ lthy (the_default "'gv" (#gv opts))
      val (abort_handler, configured_abort_ty) =
        read_abort_handler cmd_name lthy
          (the_default "c_abort" (#abort opts))
      fun require_visible_const_name name =
        (case try (Syntax.check_term lthy) (Free (name, dummyT)) of
           SOME _ => name
         | NONE => error (cmd_name ^ ": missing required pointer-model constant: " ^ name))
      val pointer_model =
        { ptr_add = SOME (require_visible_const_name (the_default "c_ptr_add" (#ptr_add opts)))
        , ptr_shift_signed = SOME (require_visible_const_name (the_default "c_ptr_shift_signed" (#ptr_shift_signed opts)))
        , ptr_diff = SOME (require_visible_const_name (the_default "c_ptr_diff" (#ptr_diff opts)))
        }
      val expr_constraint =
        let
          val ref_args =
            (case try (Syntax.check_term lthy) (Free ("reference_types", dummyT)) of
               SOME (Free (_, ref_ty)) =>
                 C_Translate.strip_isa_fun_type ref_ty
             | _ => [])
          val (state_ty, prompt_in_ty, prompt_out_ty) =
            (case ref_args of
               [s, _, _, _, pi, po] => (s, pi, po)
             | _ => (dummyT, dummyT, dummyT))
        in
          SOME (Type (\<^type_name>\<open>expression\<close>,
            [state_ty, dummyT, dummyT, configured_abort_ty,
             prompt_in_ty, prompt_out_ty]))
        end

    in
      {decl_prefix = prefix,
       abi_profile = abi_profile,
       compiler_profile = compiler_profile,
       ref_addr_ty = addr_ty,
       ref_gv_ty = gv_ty,
       ref_expr_constraint = expr_constraint,
       abort_handler = abort_handler,
       pointer_model = pointer_model,
       verbose = #verbose opts} : C_Frontend_Config.t
    end
\<close>

ML_val \<open>
  val (handler, abort_type) =
    read_abort_handler "c_source" \<^context> "c_abort"
  val _ =
    (case handler of
       Const (name, _) =>
         if name = \<^const_name>\<open>c_abort\<close> andalso
            abort_type = \<^typ>\<open>c_abort\<close>
         then ()
         else error "c_source: abort-handler resolution check failed"
     | _ => error "c_source: abort-handler constant check failed")
  val nonconstant =
    Exn.capture
      (read_abort_handler "c_source" \<^context>)
      "(\<lambda>reason. c_abort reason)"
  val _ =
    (case nonconstant of
       Exn.Exn (ERROR _) => ()
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ =>
         error "c_source: non-constant abort handler was accepted")
\<close>

subsection \<open>Unit-scoped C commands\<close>

ML \<open>
local
  structure Declaration_Plan = Frontend_Declaration_Plan
  structure Transaction = Frontend_Transaction

  fun parse_translation_unit_ast source thy =
    Micro_C_Isabelle_C_Adapter.parse_translation_unit source thy
    |> Micro_C_Isabelle_C_Adapter.ast

  datatype selection = Select_All | Select_Names of string list

  datatype unit_option =
      Unit_Abi of string
    | Unit_Compiler of string
    | Unit_Addr of string
    | Unit_Gv of string
    | Unit_Abort of string
    | Unit_Types of selection
    | Unit_Functions of selection
    | Unit_Manifest of (theory -> Token.file)
    | Unit_Verbose

  type unit_options =
    {abi: string option,
     compiler: string option,
     addr: string option,
     gv: string option,
     abort: string option,
     types: selection option,
     functions: selection option,
     manifest: (theory -> Token.file) option,
     verbose: bool}

  val empty_unit_options : unit_options =
    {abi = NONE, compiler = NONE, addr = NONE, gv = NONE, abort = NONE,
     types = NONE, functions = NONE, manifest = NONE, verbose = false}

  fun duplicate name =
    error ("c_source/c_file: duplicate " ^ quote name ^ " option")

  fun set_once name NONE value = SOME value
    | set_once name (SOME _) _ = duplicate name

  fun apply_unit_option (Unit_Abi value) (opts: unit_options) =
        {abi = set_once "abi" (#abi opts) value,
         compiler = #compiler opts, addr = #addr opts, gv = #gv opts,
         abort = #abort opts, types = #types opts, functions = #functions opts,
         manifest = #manifest opts, verbose = #verbose opts}
    | apply_unit_option (Unit_Compiler value) (opts: unit_options) =
        {abi = #abi opts,
         compiler = set_once "compiler" (#compiler opts) value,
         addr = #addr opts, gv = #gv opts, abort = #abort opts,
         types = #types opts, functions = #functions opts,
         manifest = #manifest opts, verbose = #verbose opts}
    | apply_unit_option (Unit_Addr value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts,
         addr = set_once "addr" (#addr opts) value,
         gv = #gv opts, abort = #abort opts, types = #types opts,
         functions = #functions opts, manifest = #manifest opts,
         verbose = #verbose opts}
    | apply_unit_option (Unit_Gv value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
         gv = set_once "gv" (#gv opts) value,
         abort = #abort opts, types = #types opts, functions = #functions opts,
         manifest = #manifest opts, verbose = #verbose opts}
    | apply_unit_option (Unit_Abort value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
         gv = #gv opts, abort = set_once "abort" (#abort opts) value,
         types = #types opts, functions = #functions opts,
         manifest = #manifest opts, verbose = #verbose opts}
    | apply_unit_option (Unit_Types value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
         gv = #gv opts, abort = #abort opts,
         types = set_once "types" (#types opts) value,
         functions = #functions opts, manifest = #manifest opts,
         verbose = #verbose opts}
    | apply_unit_option (Unit_Functions value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
         gv = #gv opts, abort = #abort opts, types = #types opts,
         functions = set_once "functions" (#functions opts) value,
         manifest = #manifest opts, verbose = #verbose opts}
    | apply_unit_option (Unit_Manifest value) (opts: unit_options) =
        {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
         gv = #gv opts, abort = #abort opts, types = #types opts,
         functions = #functions opts,
         manifest = set_once "manifest" (#manifest opts) value,
         verbose = #verbose opts}
    | apply_unit_option Unit_Verbose (opts: unit_options) =
        if #verbose opts then duplicate "verbose"
        else
          {abi = #abi opts, compiler = #compiler opts, addr = #addr opts,
           gv = #gv opts, abort = #abort opts, types = #types opts,
           functions = #functions opts, manifest = #manifest opts,
           verbose = true}

  fun collect_unit_options options =
    fold apply_unit_option options empty_unit_options

  val equals = Parse.$$$ "="

  val parse_selection =
    (Parse.$$$ "[" |-- Parse.list Parse.name --| Parse.$$$ "]"
      >> Select_Names) ||
    (Parse.name >> (fn "all" => Select_All
      | name => error ("c_source/c_file: expected selection list or all, found " ^
          quote name)))

  val parse_unit_option =
    (Parse.$$$ "abi" |-- equals |-- parse_abi_name >> Unit_Abi) ||
    (Parse.$$$ "compiler" |-- equals |-- parse_abi_name >> Unit_Compiler) ||
    (Parse.$$$ "addr" |-- equals |-- Parse.typ >> Unit_Addr) ||
    (Parse.$$$ "gv" |-- equals |-- Parse.typ >> Unit_Gv) ||
    (Parse.$$$ "abort" |-- equals |-- Parse.term >> Unit_Abort) ||
    (Parse.$$$ "types" |-- equals |-- parse_selection >> Unit_Types) ||
    (Parse.$$$ "functions" |-- equals |-- parse_selection >> Unit_Functions) ||
    (Parse.$$$ "manifest" |-- equals |-- Resources.parse_file >> Unit_Manifest) ||
    (Parse.$$$ "verbose" >> K Unit_Verbose) ||
    (Parse.name >> (fn name =>
      error ("c_source/c_file: unknown option " ^ quote name)))

  val parse_unit_options =
    Scan.optional
      (Parse.$$$ "[" |-- Parse.enum "," parse_unit_option --| Parse.$$$ "]")
      []

  type unit_config =
    {abi: string, compiler: string, addr: string, gv: string, abort: string}

  fun eq_config
      ({abi = abi1, compiler = compiler1, addr = addr1, gv = gv1,
        abort = abort1}: unit_config,
       {abi = abi2, compiler = compiler2, addr = addr2, gv = gv2,
        abort = abort2}: unit_config) =
    abi1 = abi2 andalso compiler1 = compiler2 andalso
    addr1 = addr2 andalso gv1 = gv2 andalso abort1 = abort2

  fun string_of_config
      ({abi, compiler, addr, gv, abort}: unit_config) =
    "{abi=" ^ quote abi ^
    ", compiler=" ^ quote compiler ^
    ", addr=" ^ quote addr ^
    ", gv=" ^ quote gv ^
    ", abort=" ^ quote abort ^ "}"

  structure C_Unit_Data = Theory_Data
  (
    type T = unit_config Symtab.table
    val empty = Symtab.empty
    val merge =
      Symtab.join
        (fn unit => fn (left, right) =>
          if eq_config (left, right) then left
          else error
            ("c_source/c_file: incompatible configurations for unit " ^
             quote unit))
  )

  fun check_unit_name unit =
    let
      val _ =
        if unit = "" orelse unit = "_"
        then error
          "c_source/c_file: UNIT must be a non-empty, non-anonymous Isabelle name"
        else ()
      val _ =
        if Long_Name.is_qualified unit
        then error
          ("c_source/c_file: UNIT must be an unqualified Isabelle name: " ^
           quote unit)
        else ()
      val _ = Binding.check (Binding.name unit)
    in
      unit
    end

  fun register_unit unit config lthy =
    let
      val thy = Proof_Context.theory_of lthy
    in
      (case Symtab.lookup (C_Unit_Data.get thy) unit of
         NONE =>
           Local_Theory.background_theory
             (C_Unit_Data.map (Symtab.update (unit, config))) lthy
       | SOME old =>
           if eq_config (old, config) then lthy
           else error
             ("c_source/c_file: configuration mismatch while extending unit " ^
              quote unit ^ "\nexisting: " ^ string_of_config old ^
             "\nrequested: " ^ string_of_config config))
    end

  fun check_unit_extension unit config lthy =
    let
      val thy = Proof_Context.theory_of lthy
    in
      (case Symtab.lookup (C_Unit_Data.get thy) unit of
         NONE => true
       | SOME old =>
           if eq_config (old, config) then false
           else error
             ("c_source/c_file: configuration mismatch while extending unit " ^
              quote unit ^ "\nexisting: " ^ string_of_config old ^
              "\nrequested: " ^ string_of_config config))
    end

  fun manifest_selection NONE = NONE
    | manifest_selection (SOME Select_All) = NONE
    | manifest_selection (SOME (Select_Names names)) = SOME names

  fun explicit_selection (opts: unit_options) =
    is_some (#types opts) orelse is_some (#functions opts)

  type configured_unit =
    {unit: string,
     config: unit_config,
     translate_opts: translate_opts,
     manifest: C_Def_Gen.manifest,
     define_abi_metadata: bool}

  fun configure_unit command unit (opts: unit_options)
      (manifest: C_Def_Gen.manifest) lthy : configured_unit =
    let
      val unit = check_unit_name unit
      val abi = the_default "lp64-le" (#abi opts)
      val compiler = the_default "default" (#compiler opts)
      val addr = the_default "'addr" (#addr opts)
      val gv = the_default "'gv" (#gv opts)
      val abort = the_default "c_abort" (#abort opts)
      val _ =
        if compiler = "default" then ()
        else ignore (C_Compiler.parse_compiler compiler)
      val addr_ty = Syntax.read_typ lthy addr
      val gv_ty = Syntax.read_typ lthy gv
      val (abort_term, _) =
        read_abort_handler command lthy abort
      val config =
        {abi = C_ABI.profile_name (C_ABI.parse_profile abi),
         compiler = compiler,
         addr = Syntax.string_of_typ lthy addr_ty,
         gv = Syntax.string_of_typ lthy gv_ty,
         abort = Syntax.string_of_term lthy abort_term}
      val define_abi_metadata =
        check_unit_extension unit config lthy
      val translate_opts : translate_opts =
        {prefix = SOME (unit ^ "."), addr = SOME addr, gv = SOME gv,
         abi = SOME abi, abort = SOME abort,
         ptr_add = NONE, ptr_shift_signed = NONE,
         ptr_diff = NONE,
         compiler = if compiler = "default" then NONE else SOME compiler,
         verbose = #verbose opts}
    in
      {unit = unit, config = config,
       translate_opts = translate_opts, manifest = manifest,
       define_abi_metadata = define_abi_metadata}
    end

  fun configure_translation command
      ({translate_opts, manifest, define_abi_metadata, ...}:
        configured_unit) lthy =
    {frontend = setup_translation_context command translate_opts lthy,
     manifest = manifest,
     define_abi_metadata = define_abi_metadata} : C_Def_Gen.config

  fun trim text = Symbol.trim_blanks text

  fun drop_comment line =
    (case String.fields (fn c => c = #"#") line of
       [] => ""
     | first :: _ => first)

  datatype manifest_section =
      No_Manifest_Section
    | Manifest_Functions
    | Manifest_Types

  fun parse_manifest_text text =
    let
      fun add_name section raw (functions, types) =
        let
          val name0 = trim raw
          val bullet = String.isPrefix "-" name0
          val name =
            if bullet
            then trim (String.extract (name0, 1, NONE))
            else name0
        in
          if bullet andalso name = ""
          then error ("c_file: malformed empty manifest entry: " ^ raw)
          else if name = "" then (functions, types)
          else
            (case section of
               Manifest_Functions => (name :: functions, types)
             | Manifest_Types => (functions, name :: types)
             | No_Manifest_Section =>
                 error
                   ("c_file: manifest entry outside functions:/types: section: " ^
                    raw))
        end

      fun step raw (section, functions, types) =
        let val line = trim (drop_comment raw)
        in
          if line = "" then (section, functions, types)
          else if line = "functions:"
          then (Manifest_Functions, functions, types)
          else if line = "types:"
          then (Manifest_Types, functions, types)
          else if String.isSuffix ":" line
          then error ("c_file: unknown manifest section: " ^ line)
          else
            let
              val (functions', types') =
                add_name section line (functions, types)
            in
              (section, functions', types')
            end
        end

      val (_, functions, types) =
        fold step
          (String.tokens (fn c => c = #"\n" orelse c = #"\r") text)
          (No_Manifest_Section, [], [])
    in
      {functions = if null functions then NONE else SOME (rev functions),
       types = if null types then NONE else SOME (rev types)}
    end

  fun provide_source_file (src_path, digest) lthy =
    Local_Theory.background_theory
      (fn thy =>
        Resources.provide (src_path, digest) thy
        handle ERROR message =>
          if String.isSubstring "Duplicate use of source file" message
          then thy
          else error message) lthy

  type declaration_snapshot =
    {constants: unit Symtab.table,
     types: unit Symtab.table,
     facts: unit Symtab.table}

  fun names_table names =
    fold (fn name => Symtab.update (name, ())) names Symtab.empty

  fun declaration_snapshot lthy : declaration_snapshot =
    let
      val ctxt = Local_Theory.target_of lthy
      val thy = Proof_Context.theory_of ctxt
      val constants =
        #constants (Consts.dest (Sign.consts_of thy))
        |> map #1
        |> names_table
      val types =
        #types (Type.rep_tsig (Sign.tsig_of thy))
        |> Name_Space.dest_table
        |> map #1
        |> names_table
      val facts =
        Facts.fold_static
          (fn (name, _) => Symtab.update (name, ()))
          (Proof_Context.facts_of ctxt)
          Symtab.empty
    in
      {constants = constants, types = types, facts = facts}
    end

  fun added_names old_table new_table =
    Symtab.fold
      (fn (name, ()) => fn names =>
        if Symtab.defined old_table name then names
        else name :: names)
      new_table []
    |> sort_strings

  fun exact_declaration_plan
      ({constants = before_constants, types = before_types,
        facts = before_facts}: declaration_snapshot)
      ({constants = after_constants, types = after_types,
        facts = after_facts}: declaration_snapshot) =
    let
      val pos = Position.none
    in
      Declaration_Plan.empty
      |> fold
           (fn name =>
             Declaration_Plan.declare_full
               Declaration_Plan.Type_Constructor name pos)
           (added_names before_types after_types)
      |> fold
           (fn name =>
             Declaration_Plan.declare_full
               Declaration_Plan.Constant name pos)
           (added_names before_constants after_constants)
      |> fold
           (fn name =>
             Declaration_Plan.declare_full
               Declaration_Plan.Fact name pos)
           (added_names before_facts after_facts)
    end

  fun install_transaction command
      (configured:
        {unit: string,
         config: unit_config,
         translate_opts: translate_opts,
         manifest: C_Def_Gen.manifest,
         define_abi_metadata: bool})
      dependencies tu lthy =
    let
      val old_snapshot = declaration_snapshot lthy
      val lthy =
        register_unit (#unit configured) (#config configured) lthy
      val lthy = fold provide_source_file dependencies lthy
      val translation_config = configure_translation command configured lthy
      val lthy =
        C_Def_Gen.process_translation_unit translation_config tu lthy
      val new_snapshot = declaration_snapshot lthy
    in
      (exact_declaration_plan old_snapshot new_snapshot, lthy)
    end

  fun preflight_and_install command configured dependencies tu lthy =
    let
      val translation_config = configure_translation command configured lthy
      val _ =
        C_Def_Gen.declaration_plan translation_config tu lthy
        |> Declaration_Plan.preflight lthy
        |> K ()
      fun validate exact_plan original_lthy =
        (Declaration_Plan.preflight original_lthy exact_plan; ())
      val (_, lthy') =
        Transaction.preflight_then_commit_with validate
          (install_transaction command configured dependencies tu)
          lthy
    in
      lthy'
    end

  fun inline_manifest (opts: unit_options) : C_Def_Gen.manifest =
    {functions = manifest_selection (#functions opts),
     types = manifest_selection (#types opts)}

  fun parse_source unit raw_options source lthy =
    let
      val options = collect_unit_options raw_options
      val _ =
        if is_some (#manifest options)
        then error "c_source: manifest is only available for c_file"
        else ()
      val configured =
        configure_unit "c_source" unit options
          (inline_manifest options) lthy
      val thy = Proof_Context.theory_of lthy
      val tu = parse_translation_unit_ast source thy
    in
      preflight_and_install "c_source" configured [] tu lthy
    end

  fun parse_file unit raw_options get_source lthy =
    let
      val options = collect_unit_options raw_options
      val _ =
        if explicit_selection options andalso is_some (#manifest options)
        then error
          "c_file: inline types/functions selection and manifest are mutually exclusive"
        else ()
      val thy = Proof_Context.theory_of lthy
      val {src_path, lines, digest, pos}: Token.file =
        get_source thy
      val source = Input.source true (cat_lines lines) (pos, pos)
      val (manifest, dependencies) =
        (case #manifest options of
           NONE =>
             (inline_manifest options, [(src_path, digest)])
         | SOME get_manifest =>
             let
               val {src_path = manifest_path, lines = manifest_lines,
                    digest = manifest_digest, ...}: Token.file =
                 get_manifest thy
             in
               (parse_manifest_text (cat_lines manifest_lines),
                [(src_path, digest),
                 (manifest_path, manifest_digest)])
             end)
      val configured =
        configure_unit "c_file" unit options manifest lthy
      val tu = parse_translation_unit_ast source thy
    in
      preflight_and_install
        "c_file" configured dependencies tu lthy
    end

  val optional_semi = Scan.option \<^keyword>\<open>;\<close>
in

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>c_source\<close>
    "translate an inline C translation unit into a mandatory Isabelle namespace"
    (Parse.name -- parse_unit_options -- Parse.embedded_input --| optional_semi
      >> (fn ((unit, options), source) => parse_source unit options source))

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>c_file\<close>
    "translate a C source file into a mandatory Isabelle namespace"
    (Parse.name -- parse_unit_options -- Resources.parse_file --| optional_semi
      >> (fn ((unit, options), source) => parse_file unit options source))

end
\<close>

end
