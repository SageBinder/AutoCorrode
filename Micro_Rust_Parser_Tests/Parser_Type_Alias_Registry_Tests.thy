theory Parser_Type_Alias_Registry_Tests
  imports Micro_Rust_Parser_Impl.Parser_Impl_Type_Mappings_Builtins
begin

urust_type "RegistryOrdered<'value>" = \<open> 'value::linorder list \<close>
urust_type "RegistryMappedWord" = \<open> 16 word \<close>

ML\<open>
structure Registry_Alias_Probe =
struct
  open URust_AST
  val pos = Position.line_file 1 "registry-alias-probes"
  val layout = make_source_layout pos []
  fun primitive typ = Primitive_Type (typ, pos)
  fun path name types =
    Path_Type
      ([Rust_Type_Path_Segment
        (name, pos,
         if null types then NONE else SOME (map Rust_Type_Argument types),
         layout)], layout)
  fun pointer mutability typ = Raw_Pointer_Type (mutability, typ, layout)
  fun alias name parameters rhs lthy =
    #1 (Micro_Rust_Semantic_Navigation.capture (fn () =>
      URust_Type_Mappings.declare_alias
        {registration = NONE, item_name = (name, pos),
         parameters = map (fn name => (name, pos)) parameters, rhs = rhs} lthy))
  fun require description condition =
    if condition then () else error ("registry alias probe: " ^ description)
  fun captured action =
    #1 (Micro_Rust_Semantic_Navigation.capture action)
  fun rejected needle action =
    (case Exn.result (fn () => captured action) () of
       Exn.Res _ => error ("registry alias probe unexpectedly accepted: " ^ needle)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else require ("missing diagnostic " ^ needle)
           (String.isSubstring needle (Runtime.exn_message exn)))
end
\<close>

local_setup\<open>
  Registry_Alias_Probe.alias "RegistryWidth" [] (Registry_Alias_Probe.primitive URust_AST.DPT_U16) #>
  Registry_Alias_Probe.alias "RegistryChain" [] (Registry_Alias_Probe.path "RegistryWidth" []) #>
  Registry_Alias_Probe.alias "RegistryIdentity" ["T"] (Registry_Alias_Probe.path "T" []) #>
  Registry_Alias_Probe.alias "RegistryPair" ["T", "U"]
    (URust_AST.Tuple_Type
      ([Registry_Alias_Probe.path "T" [], Registry_Alias_Probe.path "U" []],
       Registry_Alias_Probe.layout)) #>
  Registry_Alias_Probe.alias "RegistrySorted" ["T"]
    (Registry_Alias_Probe.path "RegistryOrdered" [Registry_Alias_Probe.path "T" []]) #>
  Registry_Alias_Probe.alias "RegistryPtr" ["T"]
    (Registry_Alias_Probe.pointer URust_AST.RPM_Const (Registry_Alias_Probe.path "T" [])) #>
  Registry_Alias_Probe.alias "RegistryMutPtr" ["T"]
    (Registry_Alias_Probe.pointer URust_AST.RPM_Mut (Registry_Alias_Probe.path "T" [])) #>
  Registry_Alias_Probe.alias "RegistrySigned" [] (Registry_Alias_Probe.primitive URust_AST.DPT_I32) #>
  Registry_Alias_Probe.alias "RegistryUnsigned" [] (Registry_Alias_Probe.primitive URust_AST.DPT_U32) #>
  Registry_Alias_Probe.alias "RegistryMappedAlias" [] (Registry_Alias_Probe.path "RegistryMappedWord" [])
\<close>

ML_val\<open>
  local
    open Registry_Alias_Probe
    val ctxt = \<^context>
    fun resolve typ = captured (fn () => URust_Type_Mappings.resolve ctxt typ)
    fun signature_types types = captured (fn () => URust_Type_Mappings.resolve_signature ctxt types)
    fun cast typ = captured (fn () =>
      URust_Type_Mappings.resolve_cast ctxt (SCT_Type typ))
    val _ = require "alias chain changed HOL meaning"
      (resolve (path "RegistryChain" []) = \<^typ>\<open>16 word\<close>)
    val _ = require "generic identity instantiations collapsed"
      (signature_types
        [path "RegistryIdentity" [primitive DPT_U8],
         path "RegistryIdentity" [primitive DPT_U16]] =
        [\<^typ>\<open>8 word\<close>, \<^typ>\<open>16 word\<close>])
    val _ = require "positional generic tuple parameters collapsed"
      (resolve (path "RegistryPair" [primitive DPT_U8, primitive DPT_U16]) =
        \<^typ>\<open>8 word \<times> 16 word \<times> tnil\<close>)
    val SOME sorted = URust_Type_Mappings.lookup ctxt "RegistrySorted"
    val _ = require "generic sort requirement was not captured"
      (URust_Type_Mappings.entry_parameter_sorts sorted = [\<^sort>\<open>linorder\<close>])
    val _ = require "signed alias selected unsigned cast"
      (cast (path "RegistrySigned" []) = CT_Signed ST_I32)
    val _ = require "unsigned alias selected signed cast"
      (cast (path "RegistryUnsigned" []) = CT_Unsigned UT_U32)
    val _ = require "generic identity cast lost primitive metadata"
      (cast (path "RegistryIdentity" [primitive DPT_U16]) = CT_Unsigned UT_U16)
    val _ = require "const pointer alias lost mutability"
      (cast (path "RegistryPtr" [primitive DPT_U16]) =
        CT_RawPointer (RPM_Const, UT_U16))
    val _ = require "mut pointer alias lost mutability"
      (cast (path "RegistryMutPtr" [primitive DPT_U16]) =
        CT_RawPointer (RPM_Mut, UT_U16))
    val _ = rejected "no supported cast operation" (fn () =>
      cast (path "RegistryMappedAlias" []))
    val [pointer_left, pointer_right, nested] =
      signature_types
        [path "RegistryPtr" [primitive DPT_U8],
         pointer RPM_Mut (primitive DPT_U16),
         pointer RPM_Const (path "RegistryPtr" [primitive DPT_U8])]
    val expected_right =
      \<^typ>\<open>('address, 'global, 16 word) Global_Store.ref\<close>
    val expected_nested =
      \<^typ>\<open>('address, 'global, ('address, 'global, 8 word) Global_Store.ref) Global_Store.ref\<close>
    val [address, global] = Term.add_tvarsT pointer_left [] |> map TVar
    val _ = require "backend address/global slots collapsed" (address <> global)
    (* Match structurally because Term.add_tvarsT does not promise address/global order. *)
    val _ = require "signature pointers did not share their backend"
      (Type.raw_instance (pointer_right, Logic.varifyT_global expected_right) andalso
       eq_set (op =) (Term.add_tvarsT pointer_left [], Term.add_tvarsT pointer_right []) andalso
       Type.raw_instance (nested, Logic.varifyT_global expected_nested) andalso
       eq_set (op =) (Term.add_tvarsT pointer_left [], Term.add_tvarsT nested []))
    val [fresh_pointer] = signature_types [path "RegistryPtr" [primitive DPT_U8]]
    val _ = require "separate signatures reused flexible backend slots"
      (null (inter (op =) (Term.add_tvarsT pointer_left []) (Term.add_tvarsT fresh_pointer [])))
    val fields =
      captured (fn () => URust_Type_Mappings.resolve_fields ctxt
        [path "RegistryPtr" [primitive DPT_U8], pointer RPM_Mut (primitive DPT_U16)])
    val _ = require "field batch did not expose exactly one backend pair"
      (length (#backend_parameters fields) = 2 andalso
        forall (fn typ => eq_set (op =)
          (Term.add_tfreesT typ [], #backend_parameters fields)) (#types fields))
    val lthy = Named_Target.theory_init \<^theory>
    val SOME identity = URust_Type_Mappings.lookup lthy "RegistryIdentity"
    val replay = alias "RegistryIdentity" ["Value"] (path "Value" []) lthy
    val SOME identical = URust_Type_Mappings.lookup replay "RegistryIdentity"
    val _ = require "alpha-identical aliases lost navigation identity"
      (URust_Type_Mappings.entry_identity identity =
        URust_Type_Mappings.entry_identity identical)
    val _ = rejected "alias and direct/generated mapping collide" (fn () =>
      alias "RegistryMappedWord" [] (primitive DPT_U16) lthy)
    val _ = rejected "conflicting active mappings" (fn () =>
      alias "RegistryWidth" [] (primitive DPT_U8) lthy)
    val _ = rejected "duplicate type parameter" (fn () =>
      alias "RegistryDuplicate" ["T", "T"] (path "T" []) lthy)
    val _ = rejected "unused type parameters" (fn () =>
      alias "RegistryUnused" ["T"] (primitive DPT_U16) lthy)
    val _ = rejected "recursive alias dependency" (fn () =>
      alias "RegistryRecursive" [] (path "RegistryRecursive" []) lthy)
    val recursive_chain =
      lthy
      |> alias "RegistryCycleLeft" [] (primitive DPT_U16)
      |> alias "RegistryCycleRight" [] (path "RegistryCycleLeft" [])
    val _ = rejected "recursive alias dependency" (fn () =>
      alias "RegistryCycleLeft" [] (path "RegistryCycleRight" []) recursive_chain)
    val _ = rejected "unknown Rust type" (fn () =>
      alias "RegistryUnknown" [] (path "RegistryMissing" []) lthy)
    val _ = rejected "generic arities" (fn () =>
      alias "RegistryArity" [] (path "RegistryIdentity" []) lthy)
    val _ = rejected "does not satisfy sort" (fn () =>
      resolve (path "RegistrySorted"
        [HOL_Type_Source (Input.string "nat \<Rightarrow> nat")]))
    val _ = rejected "type variables are not supported" (fn () =>
      resolve (HOL_Type_Source (Input.string "'unrelated")))
    val _ = rejected "unrelated HOL type variables" (fn () =>
      alias "RegistryFreeEscape" [] (HOL_Type_Source (Input.string "'unrelated")) lthy)
    val fixed = TFree ("'fixed", \<^sort>\<open>type\<close>)
    val fixed_ctxt = Variable.declare_typ fixed ctxt
    val [fixed_alias] = captured (fn () =>
      URust_Type_Mappings.resolve_signature fixed_ctxt
        [path "RegistryIdentity" [HOL_Type_Source (Input.string "'fixed")]])
    val _ = require "ambient signature type was made flexible" (fixed_alias = fixed)
    val _ = rejected "does not satisfy sort" (fn () =>
      URust_Type_Mappings.resolve_signature fixed_ctxt
        [path "RegistrySorted" [HOL_Type_Source (Input.string "'fixed")]])
    val generated_parameters =
      [("'generated_address", \<^sort>\<open>type\<close>),
       ("'generated_global", \<^sort>\<open>type\<close>)]
    val generated_template =
      Type (\<^type_name>\<open>prod\<close>, map TFree generated_parameters)
    val generated = captured (fn () =>
      URust_Type_Mappings.register_generated_scheme
        {rust_name = "RegistryGeneratedPair", rust_pos = pos,
         hol_type_name = \<^type_name>\<open>prod\<close>,
         hol_type = generated_template, backend_parameters = generated_parameters}
        lthy)
    val generated_alias = alias "RegistryGeneratedAlias" []
      (path "RegistryGeneratedPair" []) generated
    val generated_fields = captured (fn () =>
      URust_Type_Mappings.resolve_fields generated_alias
        [path "RegistryGeneratedPair" [], path "RegistryGeneratedAlias" [],
         pointer RPM_Const (primitive DPT_U8)])
    val SOME generated_entry =
      URust_Type_Mappings.lookup generated_alias "RegistryGeneratedPair"
    val _ = require "generated scheme exposed Rust generic arguments"
      (URust_Type_Mappings.entry_arities generated_entry = [0] andalso
        null (URust_Type_Mappings.entry_parameter_sorts generated_entry))
    val [generated_direct, generated_synonym, generated_pointer] = #types generated_fields
    val _ = require "generated alias did not share the field batch backend pair"
      (generated_direct = generated_synonym andalso
       eq_set (op =)
         (Term.add_tfreesT generated_direct [], Term.add_tfreesT generated_pointer []))
    val _ = rejected "alias and direct/generated mapping collide" (fn () =>
      alias "RegistryGeneratedPair" [] (primitive DPT_U16) generated)
    val registration_pos =
      Position.make0 7 101 118 "" "registry-quoted-path" "registry-path-probe"
    val item_pos =
      Position.make0 9 205 216 "" "registry-quoted-path" "registry-path-probe"
    val malformed_path_message =
      (case Exn.result (fn () => captured (fn () =>
          URust_Type_Mappings.declare_alias
            {registration = SOME ("wire::::InvalidPath", registration_pos),
             item_name = ("InvalidPath", item_pos), parameters = [],
             rhs = primitive DPT_U16} lthy)) () of
         Exn.Res _ => error "malformed registration path unexpectedly accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    fun diagnostic_range (XML.Text _) ranges = ranges
      | diagnostic_range (XML.Elem ((_, properties), children)) ranges =
          let
            val ranges' =
              (case
                (Properties.get properties Markup.offsetN,
                 Properties.get properties Markup.end_offsetN) of
                 (SOME offset, SOME end_offset) => (offset, end_offset) :: ranges
               | _ => ranges)
          in fold diagnostic_range children ranges' end
    val _ = require "malformed quoted path reported a duplicate or item-name range"
      (fold diagnostic_range (YXML.parse_body malformed_path_message) [] =
        [("101", "118")])
  in val _ = writeln "registry alias probes passed" end
\<close>

end
