(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Field_View_ML_Tests
  imports Parser_Field_View_Examples
begin

ML\<open>
structure Parser_Field_View_Test =
struct
  structure M = URust_Type_Mappings
  fun require message condition =
    if condition then () else error ("field representation regression: " ^ message)
  fun start label = Position.make0 1 1 0 "" label ""
    |> Position.copy_id (Position.thread_data ())
  fun source label text = Parser_Lex_Util.positioned_content_source text (start label)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun run thy label text =
    fold (Toplevel.command_exception true)
      (Outer_Syntax.parse_text thy (K thy) (start label) text)
      (Toplevel.make_state (SOME thy))
  fun succeeded thy label text = Toplevel.context_of (run thy label text)
  fun parsed ctxt text = URust_Parser.parse_type_source ctxt (source "field-view-type" text)
  fun resolved ctxt text = M.resolve ctxt (parsed ctxt text)
  fun find text needle offset =
    if offset + size needle > size text then error ("missing token " ^ quote needle)
    else if String.substring (text, offset, size needle) = needle then offset
    else find text needle (offset + 1)
  fun range label text needle =
    let
      fun last offset =
        (case try (find text needle) (offset + size needle) of
           SOME next => last next | NONE => offset)
      val offset = last (find text needle 0)
      val quoted = String.isPrefix "\"" needle andalso String.isSuffix "\"" needle
      val content = if quoted then String.substring (needle, 1, size needle - 2) else needle
      val offset = offset + (if quoted then 1 else 0)
      val first = Position.symbol_explode (String.substring (text, 0, offset)) (start label)
    in Position.range_position (Position.range (first, Position.symbol_explode content first)) end
  fun positioned pos message =
    let
      fun collect (XML.Text _) result = result
        | collect (XML.Elem ((_, props), body)) result = fold collect body (props :: result)
      val properties = fold collect (YXML.parse_body message) []
      fun same props =
        Properties.get props Markup.offsetN = Option.map Value.print_int (Position.offset_of pos)
        andalso Properties.get props Markup.end_offsetN =
          Option.map Value.print_int (Position.end_offset_of pos)
        andalso Properties.get props Markup.fileN = Position.file_of pos
    in exists same properties end
  fun rejection thy label expected leaf text =
    let
      val (result, reports) = Parser_Test_Reports.markup
        (fn () => Exn.capture (fn () => run thy label text) ())
      val message = case result of Exn.Res _ => error (label ^ ": accepted invalid source")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val _ = require (label ^ ": wrong diagnostic " ^ XML.content_of (YXML.parse_body message))
        (String.isSubstring expected message)
      val _ = Option.app (fn needle =>
        require (label ^ ": wrong source leaf") (positioned (range label text needle) message)) leaf
      val _ = require (label ^ ": failed command leaked semantic reports")
        (not (exists (fn (name, _) => name = Markup.entityN) reports))
    in () end
  fun policy field representation = quote field ^ " " ^ "\<rightarrow>" ^
    " " ^ cartouche representation
  fun datatype_command selections item =
    "urust_datatype [field_representations = [" ^ commas selections ^ "]] " ^ cartouche item
  fun mapping options key template =
    "urust_type " ^ options ^ " " ^ quote key ^ " = " ^ cartouche template
  fun alternative name erased key template =
    mapping ("[representation = " ^ quote name ^
      (if erased = "" then "" else ", erase = " ^ cartouche erased) ^ "]") key template
  fun native_fields ctxt type_name =
    binder_types (fastype_of (the_single (#ctrs (the (Ctr_Sugar.ctr_sugar_of ctxt type_name)))))
  fun selected ctxt representation text =
    M.resolve_declaration_roles_with_representations ctxt [] []
      [(SOME (representation, Position.none), parsed ctxt text)]
  fun imported_alias key text thy =
    let
      val layout = URust_AST.make_source_layout Position.none []
      val use = URust_AST.mk_use_item
        (URust_AST.mk_use_path
          (map (fn name => (name, Position.none)) ["view_demo", "Buffer"],
           SOME ("CapturedBuffer", Position.none), layout), layout)
      val batch = URust_Imports.validate_batch [use]
      val lthy = Local_Theory.map_contexts (fn _ => fn ctxt =>
        URust_Imports.prepare_batch_unreported URust_Imports.Require_Targets ctxt batch)
        (Named_Target.theory_init thy)
      val item = the (URust_Parser.parse_type_alias_source lthy (source key text))
    in
      lthy
      |> M.declare_generic_alias
        {registration = SOME (key, Position.none), item_name = URust_AST.type_alias_name item,
         parameters = URust_AST.type_alias_parameter_descriptors item,
         rhs = URust_AST.type_alias_rhs item}
      |> Local_Theory.exit_global
    end
end
\<close>

section\<open> Checked carriers and policy provenance \<close>

ML_val\<open>
local
  open Parser_Field_View_Test
  val ctxt = \<^context>
  val expected =
    [\<^typ>\<open>8 word list\<close>, \<^typ>\<open>64 word list\<close>,
     \<^typ>\<open>8 field_view_chain\<close>, \<^typ>\<open>(8 word, 3) vector list\<close>,
     \<^typ>\<open>bool option\<close>, \<^typ>\<open>(8 word, 4) vector\<close>,
     \<^typ>\<open>16 word list\<close>]
  val _ = require "native constructor lost a checked field carrier"
    (native_fields ctxt \<^type_name>\<open>field_view_packet\<close> = expected)
  val constructor = the (URust_Item_Scope.lookup_constructor ctxt "FieldViewPacket")
  val selectors = URust_Item_Scope.constructor_field_entries constructor
  val _ = require "selectors disagree with constructor field types"
    (map (range_type o fastype_of o URust_Item_Scope.field_scheme) selectors = expected)
  val metadata = URust_Datatype.field_representations_of ctxt \<^type_name>\<open>field_view_packet\<close>
  val _ = require "policies were lost after declaration completion"
    (map #field metadata = ["blocks", "available", "nested", "optional", "displayValue"])
  val _ = List.app (fn {field, hol_type, policy} =>
    let
      val view = the (M.lookup_representation ctxt (#source_head policy) (#representation policy))
      val index = find_index (fn entry => URust_Item_Scope.field_rust_name entry = field) selectors
    in
      require ("policy's stored type disagrees with the selector: " ^ field)
        (hol_type = nth expected index);
      require ("policy lost its mapping identity: " ^ field)
        (#declaration_identity policy = M.entry_identity view);
      require ("policy lost its canonical source head: " ^ field)
        (#source_head policy = (if field = "available" then "view_demo::Chain"
          else "view_demo::Buffer"))
    end) metadata
  val _ = List.app (fn (text, typ) =>
    require ("default carrier changed: " ^ text) (resolved ctxt text = typ))
    [("view_demo::Buffer<u8,4>", \<^typ>\<open>(8 word, 4) vector\<close>),
     ("FieldViewAliasAgain<u8,4>", \<^typ>\<open>(8 word, 4) vector\<close>),
     ("view_demo::Chain<8>", \<^typ>\<open>8 field_view_chain\<close>)]
  val imported = URust_Datatype.field_representations_of ctxt
    \<^type_name>\<open>field_view_imported\<close> |> the_single
  val _ = require "imported selection lost the canonical nominal head"
    (#source_head (#policy imported) = "view_demo::Buffer" andalso
     #hol_type imported = \<^typ>\<open>8 word list\<close>)
  val _ = require "chunk import escaped its command scope"
    (is_none (URust_Import_Scope.lookup ctxt URust_Import_Scope.Type_Namespace "SelectedBuffer"))
  val types = native_fields ctxt \<^type_name>\<open>field_view_sharing\<close>
  val [selected_type, direct_type, nested_type] = types
  val _ = require "selected/nested/default fields did not share backend role variables"
    (selected_type = HOLogic.listT direct_type andalso
     nested_type = Type (\<^type_name>\<open>vector\<close>, [direct_type, \<^typ>\<open>4\<close>]))
  val [alias_selected, alias_direct] = native_fields ctxt
    \<^type_name>\<open>field_view_alias_sharing\<close>
  val _ = require "retained references through a forwarded outer alias lost ordinary role sharing"
    (alias_selected = HOLogic.listT alias_direct)
  val (_, sorts) = Term.dest_Type (resolved ctxt "FieldViewCapacity<u8,0>")
  val _ = require "selected alias copied the default capacity's len sort"
    (length sorts = 2 andalso nth sorts 1 = \<^typ>\<open>0\<close>)
  val capacity = the (M.lookup ctxt "FieldViewCapacity")
  val _ = require "ordinary datatype source witnesses were erased implicitly"
    (M.entry_arities capacity = [2] andalso null (M.entry_erased_parameters capacity))
  val default_before = the (M.lookup ctxt "view_demo::Buffer")
  val view_before = the (M.lookup_representation ctxt "view_demo::Buffer" "list")
  val repeated = succeeded \<^theory> "field-view-alpha-repetition"
    (alternative "list" "'limit" "view_demo::Buffer<'value,const 'limit>" "'value list")
  val _ = require "alternative repetition changed the default schema or navigation identity"
    (M.entry_identity (the (M.lookup repeated "view_demo::Buffer")) = M.entry_identity default_before
     andalso M.entry_template (the (M.lookup repeated "view_demo::Buffer")) =
       M.entry_template default_before andalso
     M.entry_identity (the (M.lookup_representation repeated "view_demo::Buffer" "list")) =
       M.entry_identity view_before)
  val reordered = succeeded \<^theory> "field-view-policy-order"
    (datatype_command [policy "right" "optional", policy "left" "list"]
      "struct FieldViewPolicyOrder { left: view_demo::Buffer<u8,4>, right: view_demo::Buffer<bool,4> }")
  val order_type = URust_Item_Scope.type_hol_name
    (the (URust_Item_Scope.lookup_type reordered "FieldViewPolicyOrder"))
  val _ = require "policy order changed source-field association"
    (map (fn {field, policy, ...} => (field, #representation policy))
      (URust_Datatype.field_representations_of reordered order_type) =
      [("left", "list"), ("right", "optional")])
  val unused = succeeded \<^theory> "field-view-unused-alternative"
    (mapping ("[representation = \"epoch\", model = " ^ cartouche "epoch = 'epoch" ^
      ", erase = " ^ cartouche "'capacity" ^ "]")
      "view_demo::Buffer<'element,const 'capacity>" "'element list * 'epoch::len word" ^
      " declare [[urust_model_parameters = " ^
        cartouche ("[\"epoch\" \<rightarrow> " ^ cartouche "0" ^ "]") ^ "]]")
  val ordinary = M.resolve_declaration_roles unused [] []
    [parsed unused "view_demo::Buffer<u8,4>", parsed unused "*mut u8"]
  val _ = require "an unused alternative constrained ordinary field sorts or backend roles"
    (#types ordinary =
       [\<^typ>\<open>(8 word, 4) vector\<close>, \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>]
      andalso null (#backend_parameters ordinary))
in end
\<close>

context field_view_local_nat
begin
ML_val\<open>
local
  open Parser_Field_View_Test
  val entry = the (URust_Item_Scope.lookup_type \<^context> "FieldViewLocalHolder")
  val metadata = URust_Datatype.field_representations_of \<^context>
    (URust_Item_Scope.type_hol_name entry) |> the_single
  val _ = require "reopened locale lost its local alternative"
    (resolved \<^context> "FieldViewLocal" = \<^typ>\<open>nat\<close> andalso
     #hol_type metadata = \<^typ>\<open>nat list\<close>)
in end
\<close>
end

context field_view_local_bool
begin
ML_val\<open>
local
  open Parser_Field_View_Test
  val entry = the (URust_Item_Scope.lookup_type \<^context> "FieldViewLocalHolder")
  val metadata = URust_Datatype.field_representations_of \<^context>
    (URust_Item_Scope.type_hol_name entry) |> the_single
  val _ = require "duplicate local source names selected another locale's alternative"
    (resolved \<^context> "FieldViewLocal" = \<^typ>\<open>bool\<close> andalso
     #hol_type metadata = \<^typ>\<open>bool list\<close>)
in end
\<close>
end

ML_val\<open>
local
  open Parser_Field_View_Test
  val entry = the (URust_Item_Scope.lookup_type \<^context> "FieldViewTransport")
  val metadata = URust_Datatype.field_representations_of \<^context>
    (URust_Item_Scope.type_hol_name entry)
  val _ = require "interpreted declaration lost checked field types or canonical source identity"
    (exists (fn {hol_type, policy, ...} =>
      hol_type = \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref list\<close> andalso
      #source_head policy = "view_demo::ReferenceBuffer" andalso
      #representation policy = "transport") metadata)
  val _ = require "interpreted concrete backend roles were not shared with the direct field"
    (native_fields \<^context> (URust_Item_Scope.type_hol_name entry) =
      [\<^typ>\<open>(nat, bool, 8 word) Global_Store.ref list\<close>,
       \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>])
in end
\<close>

section\<open> Imported alias recipes and theory merges \<close>

ML_val\<open>
local
  open Parser_Field_View_Test
  val thy = \<^theory>
  val imported_thy = imported_alias "FieldViewCapturedAlias"
    "type FieldViewCapturedAlias<T, const N: usize> = CapturedBuffer<T,N>;" thy
  val imported = Proof_Context.init_global imported_thy
  val selected_result = selected imported "list" "FieldViewCapturedAlias<u16,0>"
  val _ = require "a captured import was reread in the selection context"
    (#types selected_result = [\<^typ>\<open>16 word list\<close>] andalso
     #source_head (the (the_single (#representations selected_result))) = "view_demo::Buffer")
  val _ = require "imported alias changed its ordinary carrier"
    (resolved imported "FieldViewCapturedAlias<u16,4>" = \<^typ>\<open>(16 word, 4) vector\<close>)
  val _ = require "forwarding an outer nominal copied its old carrier sorts"
    (#types (selected imported "list" "FieldViewForward<view_demo::Buffer<u8,0>>") =
      [\<^typ>\<open>8 word list\<close>])
  val _ = List.app (fn (text, typ) =>
    require ("retained alias argument bypassed ordinary field resolution: " ^ text)
      (#types (selected imported "list" text) = [typ]))
    [("FieldViewAlias<[u8;3],0>", \<^typ>\<open>(8 word, 3) array list\<close>),
     ("FieldViewAlias<(u8,bool),0>", \<^typ>\<open>(8 word \<times> bool \<times> tnil) list\<close>)]
  val _ = require "alias declaration's import scope became global"
    (is_none (URust_Import_Scope.lookup imported
      URust_Import_Scope.Type_Namespace "CapturedBuffer"))
  val closed = succeeded imported_thy "field-view-closed-escape"
    ("urust_type_alias " ^ cartouche ("type FieldViewClosedEscape = view_demo::Buffer<" ^
      "\<tau>" ^ cartouche "bool" ^ ",3>;"))
  val _ = require "a checked closed alias escape was lost during selection"
    (#types (selected closed "list" "FieldViewClosedEscape") = [\<^typ>\<open>bool list\<close>])
  val ended = Theory.end_theory thy
  fun branch label view_template =
    let
      val branch = Theory.begin_theory (label, Position.none) [ended]
      val ctxt = succeeded branch (label ^ "-view")
        (alternative "merge" "'count" "view_demo::Buffer<'value,const 'count>" view_template)
    in
      imported_alias "FieldViewMergedAlias"
        "type FieldViewMergedAlias<T, const N: usize> = CapturedBuffer<T,N>;"
        (Proof_Context.theory_of ctxt) |> Theory.end_theory
    end
  val left = branch "FieldViewMergeLeft" "'value list"
  val right = branch "FieldViewMergeRight" "'value list"
  fun merged label parents = Theory.begin_theory (label, Position.none) parents
    |> Proof_Context.init_global
  val forward = merged "FieldViewMergeForward" [left, right]
  val reverse = merged "FieldViewMergeReverse" [right, left]
  val result_forward = selected forward "merge" "FieldViewMergedAlias<u8,0>"
  val result_reverse = selected reverse "merge" "FieldViewMergedAlias<u8,0>"
  val _ = require "theory merge order changed checked alias selection"
    (#types result_forward = [\<^typ>\<open>8 word list\<close>] andalso
     #types result_forward = #types result_reverse andalso
     #representations result_forward = #representations result_reverse)
  val conflict = branch "FieldViewMergeConflict" "'value option"
  val _ = List.app (fn parents =>
    (case Exn.capture (fn () => merged "FieldViewMergeRejected" parents) () of
       Exn.Exn exn => require "alternative merge conflict lost its diagnostic"
         (String.isSubstring "conflicting active mappings" (Runtime.exn_message exn))
     | _ => error "field representation regression: conflicting alternatives merged"))
    [[left, conflict], [conflict, left]]
in end
\<close>

section\<open> Positioned policy and field navigation \<close>

ML_val\<open>
local
  open Parser_Field_View_Test
  val text = datatype_command [policy "authoredValue" "list"]
    "struct FieldViewNavigation { authoredValue: view_demo::Buffer<u8,4> }"
  val (_, markup) = Parser_Test_Reports.markup
    (fn () => succeeded \<^theory> "field-view-navigation" text)
  fun reference kind name = exists (fn (tag, props) =>
    tag = Markup.entityN andalso Properties.get props Markup.kindN = SOME kind andalso
    Properties.get props Markup.nameN = SOME name andalso
    is_some (Properties.get props Markup.refN)) markup
  val _ = require "representation option did not navigate to its declaration"
    (reference "micro_rust_type_mapping_representation" "view_demo::Buffer::list")
  val _ = require "authored field option did not navigate to the checked source field"
    (reference "urust_field" "FieldViewNavigation.authoredValue")
  fun checked_head label head source_type command =
    let
      val (_, reports) = Parser_Test_Reports.markup
        (fn () => succeeded \<^theory> label command)
      val expected = range label command head
      val authored = range label command source_type
      val canonical = the (M.lookup \<^context> "view_demo::Buffer")
      val definition = Position.def_properties_of (M.entry_declaration_position canonical)
      fun in_field props =
        (case (Properties.get props Markup.offsetN, Position.offset_of authored,
            Position.end_offset_of authored) of
           (SOME raw, SOME first, SOME last) =>
             first <= Value.parse_int raw andalso Value.parse_int raw < last
         | _ => false)
      val references = filter (fn (tag, props) =>
        tag = Markup.entityN andalso
        Properties.get props Markup.kindN = SOME "micro_rust_type_mapping" andalso
        Properties.get props Markup.nameN = SOME "view_demo::Buffer" andalso
        is_some (Properties.get props Markup.refN) andalso in_field props) reports
      fun exact (_, props) =
        Properties.get props Markup.offsetN = Option.map Value.print_int (Position.offset_of expected)
        andalso Properties.get props Markup.end_offsetN =
          Option.map Value.print_int (Position.end_offset_of expected)
        andalso Properties.get props Markup.refN = SOME (Value.print_int (M.entry_identity canonical))
        andalso forall (fn (name, value) => Properties.get props name = SOME value) definition
      val _ = require (source_type ^ ": selected head navigation lost its authored token span")
        (not (null references) andalso forall exact references)
    in () end
  val _ = checked_head "field-view-qualified-head" "Buffer" "view_demo::Buffer<u8,4>"
    (datatype_command [policy "payload" "list"]
      "struct FieldViewQualifiedNavigation { payload: view_demo::Buffer<u8,4> }")
  val _ = checked_head "field-view-imported-head" "SelectedBuffer" "SelectedBuffer<u8,4>"
    ("urust " ^ cartouche ("use view_demo::Buffer as SelectedBuffer; " ^
      "\<omega>" ^ cartouche ("field_representations = [" ^ policy "payload" "list" ^ "]") ^
      " struct FieldViewImportedNavigation { payload: SelectedBuffer<u8,4> }"))
  val _ = checked_head "field-view-aliased-head" "FieldViewAliasAgain" "FieldViewAliasAgain<u8,4>"
    (datatype_command [policy "payload" "list"]
      "struct FieldViewAliasNavigation { payload: FieldViewAliasAgain<u8,4> }")
  val _ = checked_head "field-view-forwarded-head" "Buffer"
    "FieldViewForward<view_demo::Buffer<u8,4>>"
    (datatype_command [policy "payload" "list"]
      "struct FieldViewForwardNavigation { payload: FieldViewForward<view_demo::Buffer<u8,4>> }")
in end
\<close>

section\<open> Explicit rejection boundaries and transaction rollback \<close>

ML_val\<open>
local
  open Parser_Field_View_Test
  val thy = \<^theory>
  fun selected_item policy_text item = datatype_command [policy_text] item
  val _ = rejection thy "field-view-unknown" "unknown representation" (SOME " missing ")
    (selected_item (policy "payload" "missing")
      "struct FieldViewRejected { payload: view_demo::Buffer<u8,4> }")
  val shadow_alias = succeeded thy "field-view-shadow-alias"
    ("urust_type_alias " ^ cartouche "type T = view_demo::Buffer<u8,4>;")
  val _ = rejection (Proof_Context.theory_of shadow_alias) "field-view-formal-before-alias"
    "not a source parameter" NONE
    (selected_item (policy "payload" "list") "struct FieldViewRejected<T> { payload: T }")
  val _ = rejection thy "field-view-formal-before-import" "not a source parameter" NONE
    ("urust " ^ cartouche ("use view_demo::Buffer as T; " ^
      "\<omega>" ^ cartouche ("field_representations = [" ^ policy "payload" "list" ^ "]") ^
      " struct FieldViewRejected<T> { payload: T }"))
  val _ = rejection thy "field-view-unknown-field" "unknown field representation key"
    (SOME "\"absent\"")
    (selected_item (policy "absent" "list")
      "struct FieldViewRejected { payload: view_demo::Buffer<u8,4> }")
  val _ = rejection thy "field-view-duplicate-field" "duplicate field representation key"
    (SOME "\"payload\"")
    (datatype_command [policy "payload" "list", policy "payload" "optional"]
      "struct FieldViewRejected { payload: view_demo::Buffer<u8,4> }")
  val _ = rejection thy "field-view-tuple" "only to named struct fields" (SOME "\"payload\"")
    (selected_item (policy "payload" "list") "struct FieldViewRejected(view_demo::Buffer<u8,4>);")
  val _ = rejection thy "field-view-enum" "only to named struct fields" (SOME "\"payload\"")
    (selected_item (policy "payload" "list")
      "enum FieldViewRejected { Value { payload: view_demo::Buffer<u8,4> } }")
  val _ = List.app (fn (label, typ) =>
    rejection thy ("field-view-structural-" ^ label) "require an outer nominal type" NONE
      (selected_item (policy "payload" "list") ("struct FieldViewRejected { payload: " ^ typ ^ " }")))
    [("slice", "[u8]"), ("array", "[u8;4]"), ("reference", "&view_demo::Buffer<u8,4>"),
     ("tuple", "(view_demo::Buffer<u8,4>,bool)"), ("primitive", "u8")]
  val _ = rejection thy "field-view-wrong-const-kind" "type parameters used as const arguments"
    (SOME "bool")
    (selected_item (policy "payload" "list")
      "struct FieldViewRejected { payload: view_demo::Buffer<u8,bool> }")
  val _ = rejection thy "field-view-wrong-type-kind" "numeric generic arguments for type parameters"
    (SOME "3")
    (selected_item (policy "payload" "list")
      "struct FieldViewRejected { payload: view_demo::Buffer<3,4> }")
  val _ = rejection thy "field-view-arity" "generic arities" NONE
    (selected_item (policy "payload" "list")
      "struct FieldViewRejected { payload: view_demo::Buffer<u8> }")
  val _ = rejection thy "field-view-out-of-scope" "const arguments" (SOME "N")
    (selected_item (policy "payload" "list")
      "struct FieldViewRejected { payload: view_demo::Buffer<u8,N> }")
  val _ = rejection thy "field-view-schema" "different source schema" NONE
    (alternative "invalid" "" "view_demo::Buffer<'element>" "'element list")
  val _ = rejection thy "field-view-schema-kind" "different source schema" NONE
    (alternative "invalid" "'capacity" "view_demo::Buffer<'element,'capacity>" "'element list")
  val _ = rejection thy "field-view-no-default" "requires an existing default mapping" NONE
    (alternative "list" "" "FieldViewMissing" "nat list")
  val _ = rejection thy "field-view-invalid-name" "representation names must be identifiers" NONE
    (alternative "two names" "" "FieldViewPacket" "nat")
  val _ = rejection thy "field-view-generated-default-replacement" "conflicting active mappings" NONE
    (mapping "" "FieldViewPacket" "nat")
  val _ = rejection thy "field-view-default-replacement" "conflicting active mappings" NONE
    (mapping ("[erase = " ^ cartouche "'capacity" ^ "]")
      "view_demo::Buffer<'element,const 'capacity>" "'element list")
  val _ = rejection thy "field-view-alias-registration" "canonical nominal head, not an alias" NONE
    (alternative "list" "'n" "FieldViewAlias<'t,const 'n>" "'t list")
  val _ = rejection thy "field-view-invalid-template" "correspond exactly" NONE
    (alternative "invalid" "'capacity" "view_demo::Buffer<'element,const 'capacity>" "nat list")
  val _ = rejection thy "field-view-retained-erased" "erased placeholder" NONE
    (alternative "invalid" "'capacity" "view_demo::Buffer<'element,const 'capacity>"
      "('element,'capacity::len) vector")
  val _ = rejection thy "field-view-conflict" "conflicting active mappings" NONE
    (alternative "list" "'capacity" "view_demo::Buffer<'element,const 'capacity>" "'element option")
  val _ = rejection thy "field-view-malformed-option" "quoted representation name" NONE
    (mapping "[representation]" "FieldViewMissing" "nat")
  val _ = rejection thy "field-view-duplicate-option" "duplicate" NONE
    (mapping "[representation = \"list\", representation = \"optional\"]" "FieldViewMissing" "nat")
  val _ = rejection thy "field-view-formal-escape" "unrelated HOL type variables" NONE
    ("urust_type_alias " ^ cartouche
      ("type FieldViewFormalEscape<T> = view_demo::Buffer<" ^
        "\<tau>" ^ cartouche "'T option" ^ ",3>;"))
  val rollback_text = "urust " ^ cartouche
    ("\<omega>" ^ cartouche
       ("field_representations = [" ^ policy "payload" "list" ^ "]") ^
     " struct FieldViewRollback { payload: view_demo::Buffer<u8,4> } " ^
     "\<omega>" ^ cartouche
       ("field_representations = [" ^ policy "payload" "missing" ^ "]") ^
     " struct FieldViewRollbackLater { payload: view_demo::Buffer<u8,4> }")
  val _ = rejection thy "field-view-chunk-rollback" "unknown representation" NONE rollback_text
  val clean = succeeded thy "field-view-retry-after-rollback"
    (selected_item (policy "payload" "list")
      "struct FieldViewRollback { payload: view_demo::Buffer<u8,4> }")
  val _ = require "a failed chunk leaked a later native datatype"
    (is_none (M.lookup clean "FieldViewRollbackLater"))
  val _ = require "the retry did not install one checked field policy"
    (length (URust_Datatype.field_representations_of clean
      (URust_Item_Scope.type_hol_name (the (URust_Item_Scope.lookup_type clean "FieldViewRollback")))) = 1)
in end
\<close>

end
