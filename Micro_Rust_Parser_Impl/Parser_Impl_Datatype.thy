theory Parser_Impl_Datatype
  imports
    Parser_Impl_Grammar
    Parser_Impl_Printer_Output
    Parser_Impl_Translate
begin

section\<open> Rust datatype declarations \<close>

text\<open>
This theory owns the complete implementation behind \<open>urust_datatype\<close>: source validation,
Isabelle datatype generation, Rust item-scope installation, declaration markup, and deterministic
verbosity output. Its serialized printer check runs before generation. Human output replays the
synthetic declaration only to validate and report against the already generated artifacts; it does
not generate or register anything. The outer command supplies only its already-validated options
and source through the sealed \<open>URust_Datatype.define\<close> operation.
\<close>

ML\<open>
signature URUST_DATATYPE =
sig
  val define:
    {source: Input.source,
     explicit_binding: binding option,
     interactive: bool,
     verbosity: int,
     pp_test: bool,
     pretty: bool} ->
    local_theory -> local_theory
end

structure URust_Datatype :> URUST_DATATYPE =
struct

structure I = URust_Item_Scope

fun verbosity_output_enabled interactive lthy =
  interactive orelse Config.get lthy Proof_Display.show_results

fun pretty_generated_result kind name lthy thms =
  Pretty.block1
    [Pretty.block
       [Pretty.mark_position (Position.thread_data ())
          (Pretty.keyword1 kind),
        Pretty.brk 1,
        Pretty.str (Long_Name.base_name name),
        Pretty.str ":"],
     Pretty.fbrk,
     Proof_Context.pretty_fact lthy ("", thms)]

type generated_datatype =
  {rust_name: string,
   hol_type_name: string,
   constructors: (string * string) list,
   selectors: (string * string) list,
   lenses: (string * string) list,
   item: URust_AST.urust_datatype}

val snake_case = URust_AST.rust_snake_case

fun positioned_datatype_error message pos =
  error ("urust_datatype: " ^ message ^ Position.here pos)

fun first_differing_token_index left right =
  let
    fun first index [] [] = index
      | first index [] (_ :: _) = index
      | first index (_ :: _) [] = index
      | first index (left_token :: left_tokens)
          (right_token :: right_tokens) =
          if left_token = right_token
          then first (index + 1) left_tokens right_tokens
          else index
  in first 0 left right end

fun datatype_roundtrip ctxt source item =
  let
    val original_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options item
    val generated =
      URust_Printer.string_of_datatype
        URust_Printer.serialized_options item
    fun mismatch index detail =
      error
        ("uRust datatype pretty-printer roundtrip mismatch" ^
          Position.here (Input.pos_of source) ^ "\n" ^
          "generated source:\n" ^ generated ^ "\n" ^
          "first differing token index: " ^ string_of_int index ^
          (if detail = "" then "" else "\n" ^ detail))
    val reparsed =
      (case Exn.capture
          (URust_Parser.parse_datatype_source ctxt)
          (Parser_Lex_Util.text_source generated) of
         Exn.Res (SOME reparsed) => reparsed
       | Exn.Res NONE =>
           mismatch 0 "generated source reparsed as empty input"
       | Exn.Exn exn =>
           mismatch 0
             ("generated source failed to parse: " ^
               Runtime.exn_message exn))
    val reparsed_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options reparsed
  in
    if original_tokens = reparsed_tokens then ()
    else
      mismatch
        (first_differing_token_index original_tokens reparsed_tokens) ""
  end

fun validate_rust_item_name what (name, pos) =
  if name = "_"
  then
    positioned_datatype_error
      (what ^ " name `_` is not supported") pos
  else ()

fun duplicate_names what entries =
  let
    fun check _ [] = ()
      | check seen ((name, pos) :: rest) =
          if Symtab.defined seen name
          then positioned_datatype_error
            ("duplicate " ^ what ^ " " ^ quote name) pos
          else check (Symtab.update (name, ()) seen) rest
  in check Symtab.empty entries end

fun check_constructor_arity name pos arity =
  if arity <= 14 then ()
  else
    positioned_datatype_error
      ("constructor " ^ quote name ^ " has " ^
        string_of_int arity ^
        " fields; at most 14 are supported") pos

fun primitive_type_source URust_AST.DPT_U8 = "8 word"
  | primitive_type_source URust_AST.DPT_U16 = "16 word"
  | primitive_type_source URust_AST.DPT_U32 = "32 word"
  | primitive_type_source URust_AST.DPT_U64 = "64 word"
  | primitive_type_source URust_AST.DPT_U128 = "128 word"
  | primitive_type_source URust_AST.DPT_Usize = "64 word"
  | primitive_type_source URust_AST.DPT_I8 = "8 word"
  | primitive_type_source URust_AST.DPT_I16 = "16 word"
  | primitive_type_source URust_AST.DPT_I32 = "32 word"
  | primitive_type_source URust_AST.DPT_I64 = "64 word"
  | primitive_type_source URust_AST.DPT_I128 = "128 word"
  | primitive_type_source URust_AST.DPT_Isize = "64 word"
  | primitive_type_source URust_AST.DPT_Bool = "bool"
  | primitive_type_source URust_AST.DPT_Char = "char"
  | primitive_type_source URust_AST.DPT_Str =
      error "urust_datatype: Rust str is not a supported datatype field type"
  | primitive_type_source URust_AST.DPT_Never =
      error "urust_datatype: Rust ! is not a supported datatype field type"
  | primitive_type_source URust_AST.DPT_Unit = "unit"

fun read_datatype_type lthy datatype_type =
  let
    val (source, pos) =
      (case datatype_type of
         URust_AST.Primitive_Type (primitive, pos) =>
           (primitive_type_source primitive, pos)
       | URust_AST.HOL_Type_Source input =>
           (Syntax.implode_input input, Input.pos_of input))
  in
    (case Exn.result (fn () => Syntax.read_typ lthy source) () of
       Exn.Res typ =>
         if null (Term.add_tfreesT typ []) andalso
             null (Term.add_tvarsT typ [])
         then typ
         else
           positioned_datatype_error
             "type variables are not supported in datatype fields"
             pos
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           error
             (Runtime.exn_message exn ^
               Position.here pos))
  end

fun datatype_field_name
    (URust_AST.Datatype_Field (name, _, _)) = name

fun datatype_field_position
    (URust_AST.Datatype_Field (_, pos, _)) = pos

fun datatype_field_type
    (URust_AST.Datatype_Field (_, _, datatype_type)) =
      datatype_type

fun shape_fields URust_AST.Unit_Shape = []
  | shape_fields (URust_AST.Tuple_Shape types) =
      map (pair Binding.empty) types
  | shape_fields (URust_AST.Named_Shape fields) =
      map
        (fn field =>
          (Binding.name (datatype_field_name field),
           datatype_field_type field))
        fields

fun validate_shape constructor_name constructor_pos shape =
  let
    val arity =
      (case shape of
         URust_AST.Unit_Shape => 0
       | URust_AST.Tuple_Shape types => length types
       | URust_AST.Named_Shape fields =>
           let
             val _ =
               List.app
                 (validate_rust_item_name "field" o
                   (fn field =>
                     (datatype_field_name field,
                      datatype_field_position field)))
                 fields
             val _ =
               duplicate_names "field"
                 (map
                   (fn field =>
                     (datatype_field_name field,
                      datatype_field_position field))
                   fields)
           in length fields end)
  in check_constructor_arity constructor_name constructor_pos arity end

fun bnf_constructor lthy binding fields =
  (((Binding.empty, binding),
    map (apsnd (read_datatype_type lthy)) fields), NoSyn)

fun define_bnf_datatype binding constructors lthy =
  let
    val datatype_spec = (([], binding), NoSyn)
    val dtspec =
      (Ctr_Sugar.default_ctr_options,
       [(((datatype_spec, constructors),
          (Binding.empty, Binding.empty, Binding.empty)), [])])
  in
    BNF_FP_Def_Sugar.co_datatypes
      BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec lthy
  end

fun completed_datatype_info item rust_name type_binding lthy =
  let
    val expected_name = Local_Theory.full_name lthy type_binding
    val sugar =
      (case Ctr_Sugar.ctr_sugar_of lthy expected_name of
         SOME sugar => sugar
       | NONE =>
           error
             ("urust_datatype: generated datatype metadata is unavailable for " ^
               quote expected_name))
    val hol_type_name = dest_Type_name (#T sugar)
    val constructor_names =
      map (dest_Const_name o Term.head_of) (#ctrs sugar)
    val selector_names =
      map (dest_Const_name o Term.head_of) (flat (#selss sugar))
  in
    {rust_name = rust_name,
     hol_type_name = hol_type_name,
     constructors = map (pair "") constructor_names,
     selectors = map (pair "") selector_names,
     lenses = [],
     item = item}: generated_datatype
  end

fun scope_constructor_shape URust_AST.Unit_Shape =
      URust_Item_Scope.Unit_Constructor
  | scope_constructor_shape (URust_AST.Tuple_Shape _) =
      URust_Item_Scope.Tuple_Constructor
  | scope_constructor_shape (URust_AST.Named_Shape _) =
      URust_Item_Scope.Named_Constructor

fun item_constructor_descriptors item =
  (case item of
     URust_AST.Struct_Item (name, pos, shape, _) =>
       [(name, pos, URust_Item_Scope.Struct_Constructor, shape)]
   | URust_AST.Enum_Item (enum_name, _, variants, _) =>
       map
         (fn URust_AST.Datatype_Variant
             (variant_name, variant_pos, shape) =>
           (enum_name ^ "::" ^ variant_name,
            variant_pos, URust_Item_Scope.Enum_Variant, shape))
         variants)

fun source_field_entries shape selectors =
  (case shape of
     URust_AST.Named_Shape fields =>
       if length fields = length selectors
       then
         map2
           (fn field => fn selector =>
             {rust_name = datatype_field_name field,
              rust_pos = datatype_field_position field,
              selector =
                Const (dest_Const_name selector, dummyT)})
           fields selectors
       else
         error
           "urust_datatype: generated selector metadata does not match the source fields"
   | _ => [])

fun reject_item_notation_conflict lthy rust_path rust_pos =
  let
    val registrations =
      maps
        (fn kind =>
          Micro_Rust_Names.lookups lthy kind rust_path)
        [Micro_Rust_Names.NLiteral,
         Micro_Rust_Names.NFunction]
  in
    if is_some (URust_Item_Scope.lookup_function lthy rust_path)
    then
      positioned_datatype_error
        ("Rust item path " ^ quote rust_path ^
          " conflicts with an existing Rust function item")
        rust_pos
    else if null registrations then ()
    else
      positioned_datatype_error
        ("Rust item path " ^ quote rust_path ^
          " conflicts with an existing micro_rust_notation declaration")
        rust_pos
  end

fun register_generated_datatype
    ({rust_name, hol_type_name, item, ...}: generated_datatype) lthy =
  let
    val rust_pos =
      (case item of
         URust_AST.Struct_Item (_, pos, _, _) => pos
       | URust_AST.Enum_Item (_, pos, _, _) => pos)
    val sugar =
      (case Ctr_Sugar.ctr_sugar_of lthy hol_type_name of
         SOME sugar => sugar
       | NONE =>
           error
             ("urust_datatype: generated datatype metadata is unavailable for " ^
               quote hol_type_name))
    val descriptors = item_constructor_descriptors item
    val constructors = #ctrs sugar
    val selector_rows =
      if null (#selss sugar)
      then replicate (length constructors) []
      else #selss sugar
    val _ =
      if length descriptors = length constructors andalso
          length constructors = length selector_rows
      then ()
      else
        error
          "urust_datatype: generated constructor metadata does not match the source item"
    val conflict_paths =
      (rust_name, rust_pos) ::
        map
          (fn (rust_path, pos, _, _) =>
            (rust_path, pos))
          descriptors
      |> distinct (fn ((left, _), (right, _)) => left = right)
    val _ =
      List.app
        (fn (rust_path, pos) =>
          reject_item_notation_conflict lthy rust_path pos)
        conflict_paths
    val lthy' =
      URust_Item_Scope.register_type
        {rust_name = rust_name,
         rust_pos = rust_pos,
         hol_type_name = hol_type_name}
        lthy
    fun register
        ((rust_path, position, origin, shape),
         (constructor, selectors)) =
      URust_Item_Scope.register_constructor
        {rust_type = rust_name,
         rust_path = rust_path,
         rust_pos = position,
         hol_type_name = hol_type_name,
         constructor =
           Const (dest_Const_name constructor, dummyT),
         origin = origin,
         shape = scope_constructor_shape shape,
         fields = source_field_entries shape selectors}
  in
    fold register
      (descriptors ~~ (constructors ~~ selector_rows)) lthy'
  end

fun make_named_struct rust_name rust_pos type_binding fields item lthy =
  let
    val hol_base = Binding.name_of type_binding
    val _ = validate_shape rust_name rust_pos (URust_AST.Named_Shape fields)
    val _ =
      duplicate_names "generated HOL field"
        (map
          (fn field =>
            (snake_case (datatype_field_name field),
             datatype_field_position field))
          fields)
    val record_fields =
      map
        (fn field =>
          (Binding.name
             (hol_base ^ "_" ^ snake_case (datatype_field_name field)),
           read_datatype_type lthy (datatype_field_type field)))
        fields
    val lthy' =
      Datatype_Records.record type_binding
        Datatype_Records.default_ctr_options [] record_fields lthy
    val overrides =
      map2
        (fn (selector, _) => fn field =>
          (Binding.name_of selector,
           (datatype_field_name field, datatype_field_position field)))
        record_fields fields
    val lthy'' =
      Micro_Rust_Record.make
        {with_fields = true,
         record_name = hol_base,
         overrides = overrides,
         report = false}
        lthy'
  in
    (completed_datatype_info item rust_name type_binding lthy'', lthy'')
  end

fun make_positional_struct rust_name rust_pos type_binding shape item lthy =
  let
    val _ = validate_shape rust_name rust_pos shape
    val constructor_binding =
      Binding.name ("make_" ^ Binding.name_of type_binding)
    val fields = shape_fields shape
    val constructor = bnf_constructor lthy constructor_binding fields
    val lthy' = define_bnf_datatype type_binding [constructor] lthy
  in
    (completed_datatype_info item rust_name type_binding lthy', lthy')
  end

fun enum_variant_spec lthy hol_base
    (URust_AST.Datatype_Variant (name, pos, shape)) =
  let
    val _ = validate_rust_item_name "variant" (name, pos)
    val _ = validate_shape name pos shape
    val fields =
      (case shape of
         URust_AST.Named_Shape named_fields =>
           map
             (fn field =>
               (Binding.name
                  (hol_base ^ "_" ^ snake_case name ^ "_" ^
                    snake_case (datatype_field_name field)),
                datatype_field_type field))
             named_fields
       | _ => shape_fields shape)
  in
    bnf_constructor lthy (Binding.name name) fields
  end

fun make_enum rust_name variants type_binding item lthy =
  let
    val _ =
      duplicate_names "variant"
        (map
          (fn URust_AST.Datatype_Variant (name, pos, _) =>
            (name, pos))
          variants)
    val _ =
      List.app
        (fn URust_AST.Datatype_Variant
            (name, pos, shape) =>
          (validate_rust_item_name "variant" (name, pos);
           validate_shape name pos shape))
        variants
    val hol_base = Binding.name_of type_binding
    val _ =
      duplicate_names "generated HOL selector"
        (maps
          (fn URust_AST.Datatype_Variant
              (variant_name, _, shape) =>
            (case shape of
               URust_AST.Named_Shape fields =>
                 map
                   (fn field =>
                     (snake_case variant_name ^ "_" ^
                        snake_case (datatype_field_name field),
                      datatype_field_position field))
                   fields
             | _ => []))
          variants)
    val constructors =
      map (enum_variant_spec lthy hol_base) variants
    val lthy' = define_bnf_datatype type_binding constructors lthy
  in
    (completed_datatype_info item rust_name type_binding lthy', lthy')
  end

fun infer_datatype_binding rust_name pos =
  Binding.make (snake_case rust_name, pos)

fun generate_urust_datatype type_binding item lthy =
  (case item of
     URust_AST.Struct_Item
       (rust_name, rust_pos, shape, _) =>
       (validate_rust_item_name "item" (rust_name, rust_pos);
        case shape of
          URust_AST.Named_Shape fields =>
            make_named_struct rust_name rust_pos type_binding fields item lthy
        | _ =>
            make_positional_struct rust_name rust_pos type_binding shape item lthy)
   | URust_AST.Enum_Item
       (rust_name, rust_pos, variants, _) =>
       (validate_rust_item_name "item" (rust_name, rust_pos);
        make_enum rust_name variants type_binding item lthy))

type generated_artifacts =
  {rust_name: string,
   hol_type_name: string,
   constructors:
     (string * URust_Item_Scope.constructor_entry) list,
   selectors: (string * string) list,
   lenses: (string * string) list,
   selector_definitions: thm list,
   lens_definitions: (string * thm) list,
   item: URust_AST.urust_datatype}

fun const_name_of term =
  (case Term.head_of term of
     Const (name, _) => name
   | _ =>
       error "urust_datatype: generated public artifact has no constant identity")

fun lookup_generated_constructor lthy (rust_path, _, _, _) =
  (case URust_Item_Scope.lookup_constructor lthy rust_path of
     SOME entry => (rust_path, entry)
   | NONE =>
       error
         ("urust_datatype: generated Rust item mapping is unavailable for " ^
           quote rust_path))

fun selector_label rust_path source_field =
  if String.isSubstring "::" rust_path
  then rust_path ^ "." ^ source_field
  else source_field

fun generated_lens lthy hol_type_name (source_field, selector) =
  let
    val candidate =
      lens_name (Long_Name.base_name hol_type_name)
        (Long_Name.base_name (const_name_of selector))
    val full_candidate =
      Local_Theory.full_name lthy (Binding.name candidate)
    val lens =
      (case try
          (Proof_Context.read_const
            {proper = true, strict = false} lthy)
          full_candidate of
         SOME term => term
       | NONE =>
           error
             ("urust_datatype: generated lens is unavailable for field " ^
               quote source_field))
  in (source_field, const_name_of lens) end

fun theorem_for_definition lthy constant_name =
  Option.map
    (pair constant_name)
    (try (Proof_Context.get_thm lthy)
      (Thm.def_name constant_name))

fun completed_generated_artifacts
    ({rust_name, hol_type_name, item, ...}: generated_datatype) lthy =
  let
    val descriptors = item_constructor_descriptors item
    val constructors =
      map (lookup_generated_constructor lthy) descriptors
    val selectors =
      maps
        (fn (rust_path, entry) =>
          map
            (fn (source_field, selector) =>
              (selector_label rust_path source_field,
               const_name_of selector))
            (URust_Item_Scope.constructor_fields entry))
        constructors
    val lenses =
      (case item of
         URust_AST.Struct_Item
           (_, _, URust_AST.Named_Shape _, _) =>
             (case constructors of
                [(_, entry)] =>
                  map (generated_lens lthy hol_type_name)
                    (URust_Item_Scope.constructor_fields entry)
              | _ =>
                  error
                    "urust_datatype: named struct has unexpected constructor metadata")
       | _ => [])
    val sugar =
      (case Ctr_Sugar.ctr_sugar_of lthy hol_type_name of
         SOME sugar => sugar
       | NONE =>
           error
             ("urust_datatype: generated datatype metadata is unavailable for " ^
               quote hol_type_name))
    val lens_definitions =
      map_filter
        (theorem_for_definition lthy o snd)
        lenses
  in
    {rust_name = rust_name,
     hol_type_name = hol_type_name,
     constructors = constructors,
     selectors = selectors,
     lenses = lenses,
     selector_definitions = #sel_defs sugar,
     lens_definitions = lens_definitions,
     item = item}: generated_artifacts
  end

fun report_generated_field_declarations lthy
    ({constructors, item, ...}: generated_artifacts) =
  let
    fun report_shape shape (_, entry) =
      (case shape of
         URust_AST.Named_Shape fields =>
           let
             val aliases =
               URust_Item_Scope.constructor_field_entries entry
             val _ =
               if map datatype_field_name fields =
                   map URust_Item_Scope.field_rust_name aliases
               then ()
               else
                 error
                   "urust_datatype: source field aliases changed before markup"
           in
             ignore
               (map2
                 (fn field => fn source_field =>
                   (case URust_Item_Scope.field_selector source_field of
                      Const (name, _) =>
                        (Position.report
                           (datatype_field_position field)
                           (Name_Space.markup
                             (Consts.space_of
                               (Proof_Context.consts_of lthy))
                             name);
                         URust_Item_Scope.report_field_definition
                           source_field)
                    | _ =>
                        URust_Item_Scope.report_field_definition
                          source_field))
                 fields aliases)
           end
       | _ => ())
    val shapes =
      (case item of
         URust_AST.Struct_Item (_, _, shape, _) => [shape]
       | URust_AST.Enum_Item (_, _, variants, _) =>
           map
             (fn URust_AST.Datatype_Variant (_, _, shape) =>
               shape)
             variants)
    val _ =
      if length shapes = length constructors then ()
      else
        error
          "urust_datatype: constructor shapes changed before field markup"
  in
    List.app
      (fn (shape, constructor) =>
        report_shape shape constructor)
      (shapes ~~ constructors)
  end

fun report_generated_datatype_replay lthy
    ({rust_name, hol_type_name, constructors, item = original_item, ...}:
      generated_artifacts)
    source =
  let
    val replayed_item =
      (case URust_Parser.parse_datatype_source lthy source of
         SOME item => item
       | NONE =>
           positioned_datatype_error
             "pretty output reparsed as empty input"
             (Input.pos_of source))
    val original_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options original_item
    val replayed_tokens =
      URust_Printer.tokens_of_datatype
        URust_Printer.serialized_options replayed_item
    val _ =
      if original_tokens = replayed_tokens then ()
      else
        positioned_datatype_error
          "pretty output changed the generated datatype AST"
          (Input.pos_of source)

    val type_entry =
      (case I.lookup_type lthy rust_name of
         SOME entry =>
           if I.type_hol_name entry = hol_type_name
           then entry
           else
             error
               "urust_datatype: pretty replay found a mismatched generated type identity"
       | NONE =>
           error
             "urust_datatype: pretty replay could not find the generated type identity")

    fun constructor_for rust_path =
      (case AList.lookup (op =) constructors rust_path of
         SOME entry =>
           (case I.lookup_constructor lthy rust_path of
              SOME current =>
                if Term.aconv_untyped
                    (I.constructor_term entry,
                     I.constructor_term current)
                then current
                else
                  error
                    "urust_datatype: pretty replay found a mismatched generated constructor identity"
            | NONE =>
                error
                  "urust_datatype: pretty replay could not find a generated constructor identity")
       | NONE =>
           error
             ("urust_datatype: pretty replay found an unexpected constructor path " ^
               quote rust_path))

    fun report_type_backend pos =
      (Context_Position.report lthy pos
         (Name_Space.markup
           (Proof_Context.type_space lthy)
           (I.type_hol_name type_entry));
       Context_Position.report lthy pos Markup.keyword3)

    fun report_constructor_backend pos entry =
      (case I.constructor_term entry of
         Const (name, _) =>
           Context_Position.report lthy pos
             (Name_Space.markup
               (Consts.space_of
                 (Proof_Context.consts_of lthy)) name)
       | _ =>
           error
             "urust_datatype: pretty replay constructor has no constant identity")

    fun report_field_backend pos entry =
      (case I.field_selector entry of
         Const (name, _) =>
           Context_Position.report lthy pos
             (Name_Space.markup
               (Consts.space_of
                 (Proof_Context.consts_of lthy)) name)
       | _ =>
           error
             "urust_datatype: pretty replay field has no selector identity")

    fun validate_type datatype_type =
      ignore (read_datatype_type lthy datatype_type)

    fun report_shape shape entry =
      (case shape of
         URust_AST.Unit_Shape =>
           if I.constructor_shape entry = I.Unit_Constructor
           then ()
           else
             error
               "urust_datatype: pretty replay changed a unit constructor shape"
       | URust_AST.Tuple_Shape types =>
           (if I.constructor_shape entry = I.Tuple_Constructor
            then ()
            else
              error
                "urust_datatype: pretty replay changed a tuple constructor shape";
            List.app validate_type types)
       | URust_AST.Named_Shape fields =>
           let
             val field_entries =
               I.constructor_field_entries entry
             val source_names =
               map datatype_field_name fields
             val stored_names =
               map I.field_rust_name field_entries
             val _ =
               if I.constructor_shape entry = I.Named_Constructor andalso
                   source_names = stored_names
               then ()
               else
                 error
                   "urust_datatype: pretty replay changed generated field identities"
             val _ =
               ignore
                 (map2
                   (fn field => fn field_entry =>
                     let
                       val field_pos = datatype_field_position field
                       val _ =
                         validate_type (datatype_field_type field)
                       val _ =
                         report_field_backend field_pos field_entry
                       val _ =
                         I.report_field_reference
                           lthy field_pos field_entry
                     in () end)
                   fields field_entries)
           in () end)

    fun report_constructor rust_path pos shape =
      let
        val entry = constructor_for rust_path
        val _ = report_constructor_backend pos entry
        val _ = Context_Position.report lthy pos Markup.keyword3
        val _ = I.report_constructor_reference lthy pos entry
        val _ = report_shape shape entry
      in () end

    val _ =
      (case replayed_item of
         URust_AST.Struct_Item (name, pos, shape, _) =>
           let
             val entry = constructor_for name
             val _ = report_type_backend pos
             val _ = report_constructor_backend pos entry
             val _ = Context_Position.report lthy pos Markup.keyword3
             val _ = I.report_type_reference lthy pos type_entry
             val _ = I.report_constructor_reference lthy pos entry
             val _ = report_shape shape entry
           in () end
       | URust_AST.Enum_Item (name, pos, variants, _) =>
           let
             val _ = report_type_backend pos
             val _ = I.report_type_reference lthy pos type_entry
             val _ =
               List.app
                 (fn URust_AST.Datatype_Variant
                     (variant_name, variant_pos, shape) =>
                   report_constructor
                     (name ^ "::" ^ variant_name)
                     variant_pos shape)
                 variants
           in () end)
  in () end

fun pretty_type_identity lthy name =
  Pretty.mark
    (Name_Space.markup
      (Proof_Context.type_space lthy) name)
    (Pretty.str name)

fun pretty_const_identity lthy name =
  Pretty.mark
    (Name_Space.markup
      (Consts.space_of (Proof_Context.consts_of lthy))
      name)
    (Pretty.str name)

fun pretty_manifest_mapping lthy (source, target) =
  Pretty.block
    [Pretty.str "    ",
     Pretty.str source,
     Pretty.str " -> ",
     pretty_const_identity lthy target]

fun pretty_manifest_section _ [] = []
  | pretty_manifest_section title rows =
      Pretty.str ("  " ^ title ^ ":") :: rows

fun pretty_datatype_manifest lthy
    ({rust_name, hol_type_name, constructors, selectors, lenses, ...}:
      generated_artifacts) =
  let
    val constructor_rows =
      map
        (fn (source, entry) =>
          pretty_manifest_mapping lthy
            (source,
             const_name_of
               (URust_Item_Scope.constructor_term entry)))
        constructors
    val selector_rows =
      map (pretty_manifest_mapping lthy) selectors
    val lens_rows =
      map (pretty_manifest_mapping lthy) lenses
    val mapping_rows =
      Pretty.block
        [Pretty.str "    ",
         Pretty.str rust_name,
         Pretty.str " -> ",
         pretty_type_identity lthy hol_type_name] ::
      constructor_rows @ lens_rows
    val item_row =
      Pretty.block
        [Pretty.str "  item: ",
         Pretty.str rust_name,
         Pretty.str " -> ",
         pretty_type_identity lthy hol_type_name]
  in
    Pretty.chunks
      (Pretty.keyword1 "urust_datatype generated artifacts" ::
       item_row ::
       pretty_manifest_section "constructors" constructor_rows @
       pretty_manifest_section "selectors" selector_rows @
       pretty_manifest_section "lenses" lens_rows @
       pretty_manifest_section "installed Rust mappings"
         mapping_rows)
  end

fun constructor_argument_types lthy entry =
  (case URust_Item_Scope.constructor_term entry of
     Const (name, _) =>
       binder_types
         (Consts.the_constraint
           (Proof_Context.consts_of lthy) name)
   | _ => [])

fun pretty_constructor_declaration lthy
    (rust_path, entry) =
  let
    val constructor_name =
      const_name_of
        (URust_Item_Scope.constructor_term entry)
    val arguments = constructor_argument_types lthy entry
    val fields = URust_Item_Scope.constructor_fields entry
    val argument_pretties =
      if null fields
      then map (Syntax.pretty_typ lthy) arguments
      else
        map2
          (fn (_, selector) => fn typ =>
            Pretty.block
              [Pretty.str "(",
               pretty_const_identity lthy
                 (const_name_of selector),
               Pretty.str ": ",
               Syntax.pretty_typ lthy typ,
               Pretty.str ")"])
          fields arguments
  in
    Pretty.block
      ([Pretty.str "  | ",
        pretty_const_identity lthy constructor_name] @
       maps (fn argument =>
         [Pretty.brk 1, argument]) argument_pretties @
       [Pretty.str ("    (* " ^ rust_path ^ " *)")])
  end

fun pretty_record_declaration lthy hol_type_name constructors =
  let
    val (_, entry) = the_single constructors
    val fields = URust_Item_Scope.constructor_fields entry
    val arguments = constructor_argument_types lthy entry
    val field_rows =
      map2
        (fn (_, selector) => fn typ =>
          Pretty.block
            [Pretty.str "  ",
             pretty_const_identity lthy
               (const_name_of selector),
             Pretty.str " :: ",
             Syntax.pretty_typ lthy typ])
        fields arguments
  in
    Pretty.chunks
      (Pretty.block
         [Pretty.keyword1 "datatype_record",
          Pretty.brk 1,
          pretty_type_identity lthy hol_type_name,
          Pretty.str " ="] ::
       field_rows)
  end

fun pretty_standard_datatype_declaration lthy hol_type_name constructors =
  Pretty.chunks
    (Pretty.block
       [Pretty.keyword1 "datatype",
        Pretty.brk 1,
        pretty_type_identity lthy hol_type_name,
        Pretty.str " ="] ::
     map (pretty_constructor_declaration lthy) constructors)

fun pretty_normalized_declaration lthy
    ({hol_type_name, constructors, item, ...}: generated_artifacts) =
  (case item of
     URust_AST.Struct_Item
       (_, _, URust_AST.Named_Shape _, _) =>
       pretty_record_declaration lthy hol_type_name constructors
   | _ =>
       pretty_standard_datatype_declaration
         lthy hol_type_name constructors)

fun pretty_public_definition lthy (name, theorem) =
  pretty_generated_result "definition" name lthy
    [theorem]

fun print_generated_datatype
    interactive verbosity pretty lthy artifacts =
  if verbosity = 0 orelse
      not (verbosity_output_enabled interactive lthy)
  then ()
  else
    let
      val manifest = pretty_datatype_manifest lthy artifacts
      val human =
        (case pretty of
           NONE => []
         | SOME declaration =>
             [Pretty.str "",
              Pretty.keyword1 "normalized uRust declaration",
              declaration])
      val details =
        if verbosity < 2
        then []
        else
          [Pretty.str "",
           Pretty.keyword1 "normalized generated declaration",
           pretty_normalized_declaration lthy artifacts] @
          map
            (pretty_public_definition lthy)
            (#selector_definitions artifacts
              |> map (fn theorem =>
                  (Thm_Name.short
                    (Thm.get_name_hint theorem), theorem))) @
          map
            (pretty_public_definition lthy)
            (#lens_definitions artifacts)
    in
      Pretty.writeln
        (Pretty.chunks (manifest :: human @ details))
    end

fun define
    {source, explicit_binding, interactive, verbosity,
     pp_test, pretty} lthy =
  let
    val item =
      (case URust_Parser.parse_datatype_source lthy source of
         SOME item => item
       | NONE =>
           positioned_datatype_error
             "empty datatype item" (Input.pos_of source))
    val (rust_name, rust_pos) =
      (case item of
         URust_AST.Struct_Item (name, pos, _, _) => (name, pos)
       | URust_AST.Enum_Item (name, pos, _, _) => (name, pos))
    val _ =
      if pp_test
      then datatype_roundtrip lthy source item
      else ()
    val type_binding =
      the_default (infer_datatype_binding rust_name rust_pos)
        explicit_binding
    val (generated, lthy'') =
      let
        val (generated, lthy') =
          generate_urust_datatype type_binding item
            (Config.put Proof_Display.show_results false lthy)
        val lthy'' =
          register_generated_datatype generated lthy'
      in (generated, lthy'') end
    val final_lthy =
      Config.put Proof_Display.show_results
        (Config.get lthy Proof_Display.show_results) lthy''
    val artifacts =
      completed_generated_artifacts generated final_lthy
    val _ =
      report_generated_field_declarations final_lthy artifacts
    val pretty_declaration =
      if pretty andalso verbosity > 0 andalso
          verbosity_output_enabled interactive final_lthy
      then
        SOME
          (URust_Printer_Output.pretty_human_datatype_with_reparse
            (report_generated_datatype_replay
              final_lthy artifacts)
            item)
      else NONE
    val _ =
      print_generated_datatype interactive verbosity
        pretty_declaration
        final_lthy artifacts
  in
    final_lthy
  end

end
\<close>

end
