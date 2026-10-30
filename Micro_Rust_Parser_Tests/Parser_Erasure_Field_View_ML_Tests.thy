(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Erasure_Field_View_ML_Tests
  imports Parser_Erasure_Field_View_Examples Parser_Field_View_ML_Tests
begin

section\<open> Complete source schemes and checked field policies \<close>

text\<open>
These audits run serially because resolution can report entities into the same
native output sink temporarily owned by the rollback checks below.
\<close>

ML\<open>
local
  open Parser_Field_View_Test
  val ctxt = \<^context>
  fun sparse name arity =
    let
      val entry = the (M.lookup ctxt name)
      val _ = require (name ^ ": source slots were dropped or reordered")
        (M.entry_arities entry = [arity] andalso
         M.entry_parameter_kinds entry = replicate arity URust_AST.Const_Parameter andalso
         M.entry_erased_parameters entry = (0 upto (arity - 1)))
      val _ = require (name ^ ": a HOL phantom or sort survived")
        (null (Term.add_tvarsT (M.entry_template entry) []) andalso
         null (Term.add_tfreesT (M.entry_template entry) []))
    in () end
  val _ = List.app (fn (name, arity) => sparse name arity)
    [("CompositionBlock", 1), ("CompositionStorage", 2), ("CompositionAliasStorage", 1)]
  val expected = [\<^typ>\<open>composition_block list\<close>, \<^typ>\<open>64 word list\<close>]
  val _ = require "composed native constructor lost its selected list carriers"
    (native_fields ctxt \<^type_name>\<open>composition_storage\<close> = expected)
  val _ = require "selected outer alias imposed its default capacity sort"
    (native_fields ctxt \<^type_name>\<open>composition_alias_storage\<close> =
      [\<^typ>\<open>composition_block list\<close>])
  val policies = URust_Datatype.field_representations_of ctxt
    \<^type_name>\<open>composition_storage\<close>
  val _ = require "composed declaration lost its authored field identities"
    (map #field policies = ["blocks", "available"])
  val _ = List.app (fn (row, typ) =>
    let
      val {field, hol_type, policy} = row
      val head = if field = "blocks" then "composition::Buffer" else "composition::Chain"
      val view = the (M.lookup_representation ctxt head "list")
    in
      require (field ^ ": selected carrier was not persisted") (hol_type = typ);
      require (field ^ ": canonical source identity was lost")
        (#source_head policy = head andalso #representation policy = "list" andalso
         #declaration_identity policy = M.entry_identity view)
    end) (policies ~~ expected)
  val _ = require "ordinary bounded containers changed after field selection"
    (resolved ctxt "composition::Buffer<CompositionBlock<0>,4>" =
      \<^typ>\<open>(composition_block, 4) vector\<close> andalso
     resolved ctxt "CompositionBlocks<CompositionBlock<7>,4>" =
      \<^typ>\<open>(composition_block, 4) vector\<close> andalso
     resolved ctxt "composition::Chain<4>" = \<^typ>\<open>4 composition_chain\<close>)
  val (zero_type, zero) = M.resolve_type_identity ctxt (parsed ctxt "CompositionStorage<0,0>")
  val (seven_type, seven) = M.resolve_type_identity ctxt (parsed ctxt "CompositionStorage<7,4>")
  val (_, alias) = M.resolve_type_identity ctxt (parsed ctxt "CompositionStorageZero")
  val _ = require "erased source specializations collapsed to one identity"
    (zero_type = seven_type andalso
     M.source_identity_name (the zero) <> M.source_identity_name (the seven))
  val _ = require "source alias failed to forward its erased arguments"
    (M.source_identity_name (the zero) = M.source_identity_name (the alias))
in end
\<close>

lemma composition_checked_selectors:
  shows \<open> composition_storage_blocks (make_composition_storage blocks available) = blocks \<close>
    and \<open> composition_storage_available (make_composition_storage blocks available) = available \<close>
  by simp_all

ML\<open>
local
  open Parser_Field_View_Test
  val ctxt = \<^context>
  val linked = the (M.lookup ctxt "CompositionLinked")
  val _ = require "partial erasure lost source indexes or shared backend roles"
    (M.entry_arities linked = [2] andalso
     M.entry_parameter_kinds linked =
       [URust_AST.Type_Parameter, URust_AST.Const_Parameter] andalso
     M.entry_erased_parameters linked = [1] andalso
     M.entry_parameter_sorts linked = [\<^sort>\<open>type\<close>, []] andalso
     M.entry_backend_roles linked = [M.Address, M.Global] andalso
     length (M.entry_backend_parameter_sorts linked) = 2 andalso
     length (Term.add_tvarsT (M.entry_template linked) []) = 3)
  val variables = Term.add_tvarsT (M.entry_template linked) []
  val _ = require "retained source witness was renumbered or an erased witness reappeared"
    (filter (fn ((name, _), _) => name = "_urust_type") variables =
      [(("_urust_type", 0), \<^sort>\<open>type\<close>)] andalso
     null (Term.add_tfreesT (M.entry_template linked) []))
  val _ = List.app (fn (role, sort) =>
    require "partial erasure lost a canonical backend role index or sort"
      (AList.lookup (op =) variables (URust_Model_Parameters.canonical role) = SOME sort))
    (M.entry_backend_roles linked ~~ M.entry_backend_parameter_sorts linked)
  val [blocks, pointer] = native_fields ctxt \<^type_name>\<open>composition_linked\<close>
  val _ = require "partial erasure split the selected and ordinary pointer carriers"
    (blocks = HOLogic.listT pointer andalso
     length (Term.add_tvarsT pointer []) = 3)
  val native_constructor =
    the_single (#ctrs (the (Ctr_Sugar.ctr_sugar_of ctxt
      \<^type_name>\<open>composition_linked\<close>)))
  val (_, native_parameters) = Term.dest_Type (body_type (fastype_of native_constructor))
  val _ = require "native fields do not follow retained-source then backend parameter order"
    (pointer = Term.typ_subst_atomic
       [(\<^typ>\<open>'address\<close>, nth native_parameters 1),
        (\<^typ>\<open>'global\<close>, nth native_parameters 2),
        (\<^typ>\<open>'element\<close>, hd native_parameters)]
       \<^typ>\<open>('address, 'global, 'element) Global_Store.ref\<close>)
  val policy = URust_Datatype.field_representations_of ctxt
    \<^type_name>\<open>composition_linked\<close> |> the_single
  val constructor = the (URust_Item_Scope.lookup_constructor ctxt "CompositionLinked")
  val fields = URust_Item_Scope.constructor_field_entries constructor
  val view = the (M.lookup_representation ctxt "composition::Buffer" "list")
  val _ = require "partial erasure misaligned persisted field variables with native selectors"
    (#field policy = "blocks" andalso #hol_type policy = blocks andalso
     map (range_type o fastype_of o URust_Item_Scope.field_scheme) fields = [blocks, pointer] andalso
     #source_head (#policy policy) = "composition::Buffer" andalso
     #representation (#policy policy) = "list" andalso
     #declaration_identity (#policy policy) = M.entry_identity view)
in end
\<close>

section\<open> Composition boundaries and rollback \<close>

(* Report capture owns a global native output hook and must execute serially. *)
ML\<open>
local
  open Parser_Field_View_Test
  val thy = \<^theory>
  fun declaration erased policies item =
    "urust_datatype [erase_parameters = [" ^ commas (map quote erased) ^
      "], field_representations = [" ^ commas policies ^ "]] " ^ cartouche item
  fun reject label message leaf erased policies item =
    rejection thy label message (SOME leaf) (declaration erased policies item)
  fun rejected_function label expected item =
    let
      val (result, reports) = Parser_Test_Reports.markup (fn () =>
        Exn.capture (fn () => run thy label ("urust " ^ cartouche item)) ())
      fun positions (XML.Text _) = []
        | positions (XML.Elem ((name, properties), body)) =
            (if name = Markup.positionN then [Position.of_properties properties] else []) @
              maps positions body
      val _ = case result of
          Exn.Res _ => error (label ^ ": inferred an erased source specialization")
        | Exn.Exn exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else
              let val body = YXML.parse_body (Runtime.exn_message exn)
              in require (label ^ ": wrong or unpositioned source selection error")
                (String.isSubstring expected (XML.content_of body) andalso
                 not (null (maps positions body)))
              end
      val _ = require (label ^ ": failed function emitted a generated definition")
        (not (exists (fn (name, properties) =>
          name = Markup.entityN andalso is_some (Properties.get properties Markup.defN) andalso
          Properties.get properties Markup.kindN <> SOME "urust_var") reports))
      val _ = require (label ^ ": failed function emitted semantic navigation")
        (not (exists (fn (name, properties) =>
          name = Markup.entityN andalso
          is_some (Position.offset_of (Position.of_properties properties)) andalso
          (case Properties.get properties Markup.kindN of
            SOME kind =>
              member (op =) ["urust_item", "urust_constructor", "urust_field",
                "micro_rust_notation", Micro_Rust_Names.notationN,
                "micro_rust_type_mapping"] kind orelse
              (member (op =) [Markup.constantN, Markup.type_nameN] kind andalso
                is_some (Properties.get properties Markup.refN))
          | NONE => false)) reports))
    in () end
  val _ = reject "composition-required-capacity" "still required by a datatype field" "\"N\""
    ["N"] []
    "struct CompositionRejected<const N:usize>{blocks:composition::Buffer<u8,N>}"
  val _ = reject "composition-required-element" "still required by a datatype field" "\"T\""
    ["T", "N"] [policy "blocks" "list"]
    "struct CompositionRejected<T,const N:usize>{blocks:composition::Buffer<T,N>}"
  val _ = reject "composition-unknown-view" "unknown representation" " missing "
    ["N"] [policy "blocks" "missing"]
    "struct CompositionRejected<const N:usize>{blocks:composition::Buffer<u8,N>}"
  val _ = reject "composition-wrong-const-kind" "const" "u8"
    ["N"] [policy "blocks" "list"]
    "struct CompositionRejected<const N:usize>{blocks:composition::Buffer<u8,u8>}"
  val _ = reject "composition-nested-default" "sort" "0"
    ["N"] [policy "blocks" "list"]
    "struct CompositionRejected<const N:usize>{blocks:composition::Buffer<composition::Buffer<u8,0>,N>}"
  val _ = rejected_function "composition-erased-receiver"
    "receiver has no source identity"
    "fn CompositionRejected(value:CompositionStorageZero)->u8{value.kind()}"
  val _ = rejected_function "composition-erased-owner"
    "explicit type arguments"
    "fn CompositionRejected(value:CompositionStorageZero)->u8{CompositionStorage::kind(value)}"
  val _ = require "a failed composed declaration installed a mapping"
    (is_none (M.lookup \<^context> "CompositionRejected"))
in end
\<close>

context composition_field_transport
begin
ML\<open>
local
  open Parser_Field_View_Test
  val entry = the (URust_Item_Scope.lookup_type \<^context> "CompositionTransport")
  val policy = URust_Datatype.field_representations_of \<^context>
    (URust_Item_Scope.type_hol_name entry) |> the_single
in
  val _ = require "locale reopening lost the selected field's checked type or source provenance"
    (#hol_type policy = \<^typ>\<open>composition_block list\<close> andalso
     #source_head (#policy policy) = "composition::Buffer")
end
\<close>
end

end
