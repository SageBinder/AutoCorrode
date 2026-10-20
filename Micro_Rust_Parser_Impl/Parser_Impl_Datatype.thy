theory Parser_Impl_Datatype
  imports
    Parser_Impl_Grammar
    Parser_Impl_Printer_Output
    Parser_Impl_Translate
    Parser_Impl_Type_Mappings_Builtins
    Enum_Theory.Enum_Theory
    Shallow_Micro_Rust.Simple_Word_Enum_uRust
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
  type rename = (string * Position.T) * (string * Position.T)
  type declaration =
    {source: Input.source,
     explicit_binding: binding option,
     interactive: bool,
     verbosity: int,
     pp_test: bool,
     pretty: bool,
     register_notation: bool,
     renames: rename list,
     unprefixed_selectors: Position.T option,
     backend: string,
     word_width: int option,
     parameters: rename list,
     plugins: Proof.context -> Plugin_Name.filter}
  type prepared
  val prepare: declaration -> URust_AST.urust_datatype -> local_theory -> prepared
  val prepared_registrations: Proof.context -> prepared -> URust_Imports.registrations
  val declare_prepared: prepared -> local_theory -> (unit -> unit) * local_theory
  val declare:
    declaration -> URust_AST.urust_datatype -> local_theory -> (unit -> unit) * local_theory
  val define: declaration -> local_theory -> local_theory
end

structure URust_Datatype :> URUST_DATATYPE =
struct

structure I = URust_Item_Scope
structure Navigation = Micro_Rust_Semantic_Navigation

type rename = (string * Position.T) * (string * Position.T)
type declaration =
  {source: Input.source,
   explicit_binding: binding option,
   interactive: bool,
   verbosity: int,
   pp_test: bool,
   pretty: bool,
   register_notation: bool,
   renames: rename list,
   unprefixed_selectors: Position.T option,
   backend: string,
   word_width: int option,
   parameters: rename list,
   plugins: Proof.context -> Plugin_Name.filter}

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
   hol_type: typ,
   backend_parameters: (string * sort) list,
   backend: string,
   source_parameters: (string * sort) list,
   native_constructors: term list,
   native_selectors: term list list,
   selector_definitions: thm list,
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

fun payload_key variant member = variant ^ "." ^ member

(* Rust tuple indices are decimal literals without leading zeros. *)
fun tuple_index text =
  if text = "0" orelse
      (text <> "" andalso String.sub (text, 0) <> #"0" andalso
        forall_string Symbol.is_ascii_digit text)
  then SOME (Value.parse_int text)
  else NONE

(* The reason a rename key names nothing in this source item. A struct key is a named field. An
   enum key is a variant, which renames its constructor, or a payload key "Variant.field" or
   "Variant.N" with the source variant name and a named field or 0-based tuple index. *)
fun rename_key_error item key =
  let
    fun unknown reason = SOME ("unknown rename key " ^ quote key ^ ": " ^ reason)
    fun field_names fields = map (fn URust_AST.Datatype_Field (name, _, _) => name) fields
    fun variant_key enum_name variants =
      let
        val (variant, rest) = Substring.position "." (Substring.full key) |> apply2 Substring.string
        val member_name = if rest = "" then NONE else SOME (unprefix "." rest)
        val shape =
          get_first
            (fn URust_AST.Datatype_Variant (name, _, shape) =>
              if name = variant then SOME shape else NONE)
            variants
      in
        (case (shape, member_name) of
           (NONE, _) => unknown ("enum " ^ quote enum_name ^ " has no variant " ^ quote variant)
         | (SOME _, NONE) => NONE
         | (SOME (URust_AST.Named_Shape (fields as _ :: _)), SOME field) =>
             if member (op =) (field_names fields) field then NONE
             else unknown ("variant " ^ quote variant ^ " has no field " ^ quote field)
         | (SOME (URust_AST.Tuple_Shape (types as _ :: _)), SOME index) =>
             (case tuple_index index of
                NONE =>
                  SOME
                    ("invalid rename key " ^ quote key ^ ": tuple variant fields are named by " ^
                      "0-based decimal indices without leading zeros")
              | SOME n =>
                  if n < length types then NONE
                  else
                    unknown
                      ("variant " ^ quote variant ^ " has " ^ string_of_int (length types) ^
                        " positional " ^ (if length types = 1 then "field" else "fields")))
         | (SOME _, SOME _) => unknown ("variant " ^ quote variant ^ " has no payload fields"))
      end
  in
    (case item of
       URust_AST.Struct_Item (name, _, URust_AST.Named_Shape (fields as _ :: _), _) =>
         if member (op =) (field_names fields) key then NONE
         else unknown ("struct " ^ quote name ^ " has no field " ^ quote key)
     | URust_AST.Struct_Item (name, _, URust_AST.Tuple_Shape (_ :: _), _) =>
         unknown
           ("struct " ^ quote name ^ " has only positional fields, " ^
             "and tuple struct fields have no rename keys")
     | URust_AST.Struct_Item (name, _, _, _) =>
         unknown ("struct " ^ quote name ^ " has no fields")
     | URust_AST.Enum_Item (name, _, variants, _) => variant_key name variants)
  end

fun checked_binding lthy what (name, pos) =
  let
    val binding = Binding.make (name, pos)
    val _ =
      if name <> "" andalso Symbol_Pos.is_identifier name then ()
      else positioned_datatype_error ("invalid HOL name binding " ^ quote name ^ what) pos
    val _ =
      Local_Theory.full_name lthy binding
      handle ERROR message =>
        positioned_datatype_error message pos
  in binding end

(* Keys belong to this source declaration; targets are native HOL basenames. *)
fun resolve_renames lthy item (renames: rename list) =
  let
    val _ = duplicate_names "rename key" (map fst renames)
    fun resolve ((source, source_pos), target) =
      (case rename_key_error item source of
         SOME message => positioned_datatype_error message source_pos
       | NONE => (source, checked_binding lthy "" target))
  in Symtab.make (map resolve renames) end

fun renamed_binding renames key default =
  the_default default (Symtab.lookup renames key)

fun chosen_binding renames source default pos =
  renamed_binding renames source (Binding.make (default, pos))

(* Under unprefixed_selectors, a named struct field or named enum payload field without its own
   key takes its snake-case source name, positioned at the field like every automatic struct
   selector. *)
fun add_unprefixed_selectors lthy item renames =
  let
    fun add key (URust_AST.Datatype_Field (name, pos, _)) table =
      if Symtab.defined table (key name) then table
      else
        Symtab.update
          (key name,
           checked_binding lthy (" for the unprefixed selector of field " ^ quote name)
             (snake_case name, pos))
          table
  in
    (case item of
       URust_AST.Struct_Item (_, _, URust_AST.Named_Shape fields, _) => fold (add I) fields renames
     | URust_AST.Struct_Item _ => renames
     | URust_AST.Enum_Item (_, _, variants, _) =>
         fold
           (fn URust_AST.Datatype_Variant (variant, _, URust_AST.Named_Shape fields) =>
                 fold (add (payload_key variant)) fields
             | _ => I)
           variants renames)
  end

fun check_effective_names what bindings =
  duplicate_names what (map (fn b => (Binding.name_of b, Binding.pos_of b)) bindings)

fun check_constructor_arity name pos arity =
  if arity <= 14 then ()
  else
    positioned_datatype_error
      ("constructor " ^ quote name ^ " has " ^
        string_of_int arity ^
        " fields; at most 14 are supported") pos

fun datatype_field_name
    (URust_AST.Datatype_Field (name, _, _)) = name

fun datatype_field_position
    (URust_AST.Datatype_Field (_, pos, _)) = pos

fun datatype_field_type
    (URust_AST.Datatype_Field (_, _, datatype_type)) =
      datatype_type

fun recursive_type_position rust_name datatype_type =
  let
    fun argument
        (URust_AST.Rust_Type_Argument typ) = typ_position typ
      | argument (URust_AST.Rust_Numeric_Argument _) = NONE
    and typ_position
        (URust_AST.Primitive_Type _) = NONE
      | typ_position (URust_AST.Path_Type (segments, layout)) =
          let
            fun segment
                (URust_AST.Rust_Type_Path_Segment
                  (name, _, arguments, _)) =
              (name, the_default [] arguments)
            val rows = map segment segments
            val path = space_implode "::" (map fst rows)
          in
            if path = rust_name
            then SOME (URust_AST.source_span layout)
            else get_first argument (maps snd rows)
          end
      | typ_position (URust_AST.Tuple_Type (types, _)) =
          get_first typ_position types
      | typ_position (URust_AST.Group_Type (typ, _)) =
          typ_position typ
      | typ_position (URust_AST.Reference_Type (_, _, typ, _)) =
          typ_position typ
      | typ_position (URust_AST.Raw_Pointer_Type (_, typ, _)) =
          typ_position typ
      | typ_position (URust_AST.Slice_Type (typ, _)) =
          typ_position typ
      | typ_position (URust_AST.Array_Type (typ, _, _)) =
          typ_position typ
      | typ_position (URust_AST.Const_Array_Type (typ, _, _)) = typ_position typ
      | typ_position (URust_AST.HOL_Type_Source _) = NONE
  in typ_position datatype_type end

fun reject_recursive_shape rust_name shape =
  let
    val types =
      (case shape of
         URust_AST.Unit_Shape => []
       | URust_AST.Tuple_Shape types => types
       | URust_AST.Named_Shape fields =>
           map datatype_field_type fields)
  in
    (case get_first (recursive_type_position rust_name) types of
       NONE => ()
     | SOME pos =>
         positioned_datatype_error
           ("recursive Rust datatype reference " ^
             quote rust_name ^ " is not supported")
           pos)
  end

fun reject_recursive_item rust_name item =
  (case item of
     URust_AST.Struct_Item (_, _, shape, _) =>
       reject_recursive_shape rust_name shape
   | URust_AST.Enum_Item (_, _, variants, _) =>
       List.app
         (fn URust_AST.Datatype_Variant (_, _, shape) =>
           reject_recursive_shape rust_name shape)
         variants)

fun shape_fields URust_AST.Unit_Shape = []
  | shape_fields (URust_AST.Tuple_Shape types) =
      map (pair Binding.empty) types
  | shape_fields (URust_AST.Named_Shape fields) =
      map
        (fn field =>
          (Binding.name (datatype_field_name field),
           datatype_field_type field))
        fields

fun item_field_types item =
  (case item of
     URust_AST.Struct_Item (_, _, shape, _) =>
       map snd (shape_fields shape)
   | URust_AST.Enum_Item (_, _, variants, _) =>
       maps
         (fn URust_AST.Datatype_Variant (_, _, shape) =>
           map snd (shape_fields shape))
         variants)

fun datatype_parameters parameters =
  map (fn parameter as (_, sort) => (NONE, (TFree parameter, sort)))
    parameters

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

fun bnf_constructor binding fields =
  (((Binding.empty, binding), fields), NoSyn)

fun define_bnf_datatype plugins backend_parameters binding constructors lthy =
  let
    val datatype_spec =
      ((datatype_parameters backend_parameters, binding), NoSyn)
    val dtspec =
      ((Plugin_Name.make_filter lthy plugins, false),
       [(((datatype_spec, constructors),
          (Binding.empty, Binding.empty, Binding.empty)), [])])
  in
    BNF_FP_Def_Sugar.co_datatypes
      BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec lthy
  end

fun completed_datatype_info backend_parameters item rust_name type_binding lthy =
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
    (* Ctr_Sugar exports native schemes with index-zero schematic variables.
       Registry schemes name their implicit parameters with free variables. *)
    val hol_type = Type.legacy_freeze_type (#T sugar)
    val generated_parameters =
      map dest_TFree (snd (dest_Type hol_type))
    val _ =
      if length generated_parameters = length backend_parameters then ()
      else
        error
          "urust_datatype: generated implicit backend parameters changed"
    val constructor_names =
      map (dest_Const_name o Term.head_of) (#ctrs sugar)
    val selector_names =
      map (dest_Const_name o Term.head_of) (flat (#selss sugar))
  in
    {rust_name = rust_name,
     hol_type_name = hol_type_name,
     hol_type = hol_type,
     backend_parameters = generated_parameters,
     backend = "hol",
     source_parameters = [],
     native_constructors = #ctrs sugar,
     native_selectors = #selss sugar,
     selector_definitions = #sel_defs sugar,
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
              selector = selector})
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
    if null registrations then ()
    else
      positioned_datatype_error
        ("Rust item path " ^ quote rust_path ^
          " conflicts with an existing micro_rust_notation declaration")
        rust_pos
  end

fun register_generated_datatype
    ({rust_name, hol_type_name, item, native_constructors, native_selectors, ...}: generated_datatype) lthy =
  let
    val rust_pos =
      (case item of
         URust_AST.Struct_Item (_, pos, _, _) => pos
       | URust_AST.Enum_Item (_, pos, _, _) => pos)
    val descriptors = item_constructor_descriptors item
    val constructors = native_constructors
    val selector_rows =
      if null native_selectors then replicate (length constructors) []
      else native_selectors
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
         constructor = constructor,
         origin = origin,
         shape = scope_constructor_shape shape,
         fields = source_field_entries shape selectors}
  in
    fold register
      (descriptors ~~ (constructors ~~ selector_rows)) lthy'
  end

fun make_named_struct plugins register_notation renames backend_parameters resolved_types
    rust_name rust_pos type_binding fields item lthy =
  let
    val hol_base = Binding.name_of type_binding
    val _ = validate_shape rust_name rust_pos (URust_AST.Named_Shape fields)
    val record_fields =
      map2
        (fn field => fn typ =>
          (chosen_binding renames (datatype_field_name field)
             (hol_base ^ "_" ^ snake_case (datatype_field_name field))
             (datatype_field_position field),
           typ))
        fields resolved_types
    val _ = check_effective_names "generated HOL field" (map fst record_fields)
    val lthy' =
      Datatype_Records.record type_binding
        (Plugin_Name.make_filter lthy plugins)
        (datatype_parameters backend_parameters) record_fields lthy
    val overrides =
      if register_notation
      then
        map2
          (fn (selector, _) => fn field =>
            (Binding.name_of selector,
             (datatype_field_name field, datatype_field_position field)))
          record_fields fields
      (* The record generator rejects source-name overrides when field registration is disabled. *)
      else []
    val lthy'' =
      Micro_Rust_Record.make
        {with_fields = register_notation,
         record_name = hol_base,
         overrides = overrides,
         report = false}
        lthy'
  in
    (completed_datatype_info backend_parameters item rust_name type_binding lthy'', lthy'')
  end

fun make_positional_struct plugins backend_parameters resolved_types
    rust_name rust_pos type_binding shape item lthy =
  let
    val _ = validate_shape rust_name rust_pos shape
    val constructor_binding =
      Binding.name ("make_" ^ Binding.name_of type_binding)
    val fields = map fst (shape_fields shape) ~~ resolved_types
    val constructor = bnf_constructor constructor_binding fields
    val lthy' =
      define_bnf_datatype plugins backend_parameters type_binding [constructor] lthy
  in
    (completed_datatype_info backend_parameters item rust_name type_binding lthy', lthy')
  end

fun enum_variant_spec renames hol_base
    (URust_AST.Datatype_Variant (name, pos, shape)) resolved_types =
  let
    val _ = validate_rust_item_name "variant" (name, pos)
    val _ = validate_shape name pos shape
    (* Payload keys use the source variant name, independently of a constructor rename. An
       unrenamed positional field keeps the empty binding and therefore no custom selector. *)
    val fields =
      (case shape of
         URust_AST.Named_Shape named_fields =>
           map
             (fn field =>
               (renamed_binding renames (payload_key name (datatype_field_name field))
                  (Binding.name
                    (hol_base ^ "_" ^ snake_case name ^ "_" ^
                      snake_case (datatype_field_name field))),
                datatype_field_type field))
             named_fields
       | _ =>
           map_index
             (fn (index, (_, typ)) =>
               (renamed_binding renames (payload_key name (string_of_int index)) Binding.empty,
                typ))
             (shape_fields shape))
  in
    bnf_constructor (chosen_binding renames name name pos)
      (map fst fields ~~ resolved_types)
  end

(* The custom selectors of a variant specification, each at the position that explains it: a
   rename target, or the source field of an automatic name. *)
fun payload_selector_names
    (URust_AST.Datatype_Variant (_, _, shape), (((_, _), fields), _)) =
  let
    val source_positions =
      (case shape of
         URust_AST.Named_Shape named_fields => map datatype_field_position named_fields
       | _ => map (K Position.none) fields)
    fun explained (binding, _) source_pos =
      (Binding.name_of binding,
       if Binding.pos_of binding = Position.none then source_pos else Binding.pos_of binding)
  in
    map2 explained fields source_positions
    |> filter_out (fn (name, _) => name = "")
  end

fun make_enum plugins renames backend_parameters resolved_types
    rust_name variants type_binding item lthy =
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
      check_effective_names "generated HOL constructor"
        (map (fn URust_AST.Datatype_Variant (name, pos, _) =>
          chosen_binding renames name name pos) variants)
    fun variant_types (variant as URust_AST.Datatype_Variant (_, _, shape))
        remaining =
      let
        val count = length (shape_fields shape)
        val (types, rest) = chop count remaining
      in (enum_variant_spec renames hol_base variant types, rest) end
    val (constructors, remaining_types) =
      fold_map variant_types variants resolved_types
    val _ =
      duplicate_names "generated HOL selector"
        (maps payload_selector_names (variants ~~ constructors))
    val _ =
      if null remaining_types then ()
      else error "urust_datatype: field batch does not match the enum variants"
    val lthy' =
      define_bnf_datatype plugins backend_parameters type_binding constructors lthy
  in
    (completed_datatype_info backend_parameters item rust_name type_binding lthy', lthy')
  end

fun native_datatype_info backend backend_parameters rust_name type_binding item
    hol_type constructors selectors selector_definitions ctxt : generated_datatype =
  let
    val hol_type = Type.legacy_freeze_type hol_type
    fun specialize family term =
      let
        val scheme = term |> Term.map_types (Type.legacy_freeze_type #> Logic.varifyT_global)
        val substitution = Sign.typ_match (Proof_Context.theory_of ctxt)
          (family (fastype_of scheme), hol_type) Vartab.empty
      in Term.map_types (Envir.subst_type substitution) scheme end
    val constructors = map (specialize body_type) constructors
    val selectors = map (map (specialize domain_type)) selectors
  in
  {rust_name = rust_name, hol_type_name = dest_Type_name hol_type,
   hol_type = hol_type, backend_parameters = backend_parameters,
   backend = backend, source_parameters = [], native_constructors = constructors,
   native_selectors = selectors,
   selector_definitions = selector_definitions,
   constructors = map (pair "" o dest_Const_name) constructors,
   selectors = map (pair "" o dest_Const_name) (flat selectors), lenses = [], item = item}
  end

fun custom_enum_selectors type_binding constructors case_const case_thms specifications lthy =
  let
    val argument_types = map (binder_types o fastype_of) constructors
    val result_type = body_type (fastype_of (hd constructors))
    fun selector variant_index field_index binding typ lthy =
      let
        fun branch (index, types) =
          let val variables = map_index (fn (i, T) => Free ("x" ^ string_of_int i, T)) types
              val result = if index = variant_index then nth variables field_index
                else Const (\<^const_name>\<open>undefined\<close>, typ)
          in fold_rev lambda variables result end
        val case_type = map (fn Ts => Ts ---> typ) argument_types ---> result_type --> typ
        val body = list_comb (Const (dest_Const_name case_const, case_type),
          map_index branch argument_types)
        val ((term, (_, definition)), lthy') = Local_Theory.define
          ((binding, NoSyn), ((Thm.def_binding binding, []), body)) lthy
        val phi = Local_Theory.target_morphism lthy'
        val term = Morphism.term phi term |> Term.map_types Type.legacy_freeze_type
        val definition = Morphism.thm phi definition
        val variables = map_index (fn (i, T) => Free ("x" ^ string_of_int i, T))
          (nth argument_types variant_index)
        val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
          (term $ list_comb (nth constructors variant_index, variables), nth variables field_index))
        val theorem = Goal.prove lthy' (map (fst o dest_Free) variables) [] goal
          (fn {context, ...} => simp_tac (context addsimps (definition :: case_thms)) 1)
        val (_, lthy'') = Local_Theory.note
          ((Binding.suffix_name "_simps" binding, @{attributes [simp]}), [theorem]) lthy'
      in ((term, definition), lthy'') end
    fun variant (index, (((_, _), fields), _)) lthy =
      fold_map (fn (i, (binding, typ)) => fn ctxt =>
        if Binding.is_empty binding then ((NONE, NONE), ctxt)
        else let val ((term, definition), ctxt') = selector index i binding typ ctxt
          in ((SOME term, SOME definition), ctxt') end)
        (map_index I fields) lthy
    val (rows, lthy') = fold_map variant (map_index I specifications) lthy
  in ((map (map_filter fst) rows, maps (map_filter snd) rows), lthy') end

(* The plugins of the native simple_word_enum backend. The common registry owns source constructor
   names, so the urust_notation plugin never runs; conversion plugins use the original Rust type
   name, independently of HOL constructor renames. *)
fun native_plugins plugins ctxt name =
  plugins ctxt name andalso name <> \<^plugin>\<open>urust_notation\<close>

fun make_native_enum backend plugins width values renames backend_parameters resolved_types
    rust_name variants type_binding item lthy =
  let
    val _ = duplicate_names "variant"
      (map (fn URust_AST.Datatype_Variant (name, pos, _) => (name, pos)) variants)
    fun specification (variant as URust_AST.Datatype_Variant (name, pos, shape)) remaining =
      let val (types, rest) = chop (length (shape_fields shape)) remaining
      in (enum_variant_spec renames (Binding.name_of type_binding) variant types, rest) end
    val (specifications, _) = fold_map specification variants resolved_types
    val _ = check_effective_names "generated HOL constructor"
      (map (fn (((_, binding), _), _) => binding) specifications)
    val _ = duplicate_names "generated HOL selector"
      (maps payload_selector_names (variants ~~ specifications))
  in
    if backend = "enum" then
      let
        val typed = map (fn (((_, binding), fields), _) => (binding, map snd fields)) specifications
        val (result, lthy') = Enum_Cmd.enum_core backend_parameters type_binding typed lthy
        val ((selectors, definitions), lthy'') = custom_enum_selectors type_binding
          (#constructors result) (#case_const result) (#case_thms result) specifications lthy'
      in (native_datatype_info backend backend_parameters rust_name type_binding item
        (#T result) (#constructors result) selectors definitions lthy'', lthy'') end
    else
      let
        val variant_specs = map2 (fn (((_, binding), _), _) => fn value =>
          (binding, string_of_int value)) specifications values
        val (info, lthy') = Simple_Word_Enum.simple_word_enum_core_parameters backend_parameters
          {timer = Simple_Word_Enum.new_timer false, report = false}
          (native_plugins plugins, the width, type_binding, SOME rust_name, variant_specs) lthy
      in (native_datatype_info backend backend_parameters rust_name type_binding item
        (#absT info) (#variant_consts info) (replicate (length variants) []) [] lthy', lthy') end
  end

fun infer_datatype_binding rust_name pos =
  Binding.make (snake_case rust_name, pos)

fun generate_urust_datatype backend plugins width values register_notation renames backend_parameters
    resolved_types type_binding item lthy =
  (case item of
     URust_AST.Struct_Item
       (rust_name, rust_pos, shape, _) =>
       (validate_rust_item_name "item" (rust_name, rust_pos);
        case shape of
          URust_AST.Named_Shape [] =>
            make_positional_struct plugins backend_parameters []
              rust_name rust_pos type_binding URust_AST.Unit_Shape item lthy
        | URust_AST.Named_Shape fields =>
            make_named_struct plugins register_notation renames backend_parameters
              resolved_types rust_name rust_pos type_binding fields item lthy
        | _ =>
            make_positional_struct plugins backend_parameters resolved_types
              rust_name rust_pos type_binding shape item lthy)
   | URust_AST.Enum_Item
       (rust_name, rust_pos, variants, _) =>
       (validate_rust_item_name "item" (rust_name, rust_pos);
        if backend = "hol" then make_enum plugins renames backend_parameters resolved_types
          rust_name variants type_binding item lthy
        else make_native_enum backend plugins width values renames backend_parameters resolved_types
          rust_name variants type_binding item lthy))

type generated_artifacts =
  {rust_name: string,
   hol_type_name: string,
   hol_type: typ,
   backend_parameters: (string * sort) list,
   backend: string,
   source_parameters: (string * sort) list,
   constructors:
     (string * URust_Item_Scope.constructor_entry) list,
   selectors: (string * string) list,
   lenses: (string * string) list,
   register_notation: bool,
   source_item: URust_AST.urust_datatype,
   source_descriptors: URust_AST.generic_parameter list,
   parameter_overrides: rename list,
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

fun completed_generated_artifacts source_item source_descriptors parameter_overrides register_notation
    ({rust_name, hol_type_name, hol_type, backend_parameters, backend, source_parameters,
      selector_definitions, item, ...}: generated_datatype) lthy =
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
    val lens_definitions =
      map_filter
        (theorem_for_definition lthy o snd)
        lenses
  in
    {rust_name = rust_name,
     hol_type_name = hol_type_name,
     hol_type = hol_type,
     backend_parameters = backend_parameters,
     backend = backend,
     source_parameters = source_parameters,
     constructors = constructors,
     selectors = selectors,
     lenses = lenses,
     register_notation = register_notation,
     source_item = source_item, source_descriptors = source_descriptors,
     parameter_overrides = parameter_overrides,
     selector_definitions = selector_definitions,
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
                        (Navigation.defer_report lthy
                           (datatype_field_position field)
                           (Name_Space.markup
                             (Consts.space_of
                               (Proof_Context.consts_of lthy))
                             name);
                         URust_Item_Scope.defer_field_definition lthy
                           source_field)
                    | _ =>
                        URust_Item_Scope.defer_field_definition lthy
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
    ({rust_name, hol_type_name, source_parameters, backend_parameters,
      source_descriptors, parameter_overrides,
      constructors, source_item = original_item, ...}:
      generated_artifacts)
    source =
  let
    val replayed_source =
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
        URust_Printer.serialized_options replayed_source
    val replayed_item = case replayed_source of URust_AST.Datatype_Header (_, _, _, item) => item
      | item => item
    val _ =
      if original_tokens = replayed_tokens then ()
      else
        positioned_datatype_error
          "pretty output changed the generated datatype AST"
          (Input.pos_of source)
    (* Resolve every replayed field together, exactly as for generation.  The
       batch's fresh names may differ from the native datatype parameters. *)
    val replayed_fields =
      URust_Type_Mappings.resolve_declaration lthy source_descriptors parameter_overrides (item_field_types replayed_item)
    val replayed_parameters = #source_parameters replayed_fields @ #backend_parameters replayed_fields
    val complete_parameters = source_parameters @ backend_parameters
    val _ =
      if map snd replayed_parameters = map snd complete_parameters then ()
      else
        error
          "urust_datatype: pretty replay changed implicit backend parameters"
    val replayed_substitutions =
      map2
        (fn source => fn target => (TFree source, TFree target))
        replayed_parameters complete_parameters
    val replayed_types =
      map (Term.typ_subst_atomic replayed_substitutions) (#types replayed_fields)
    val stored_types =
      maps
        (binder_types o Type.legacy_freeze_type o fastype_of o
          I.constructor_scheme o snd)
        constructors
    val _ =
      if replayed_types = stored_types then ()
      else
        error
          "urust_datatype: pretty replay changed generated field type schemes"

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
       | _ => error "urust_datatype: pretty replay field has no selector identity")

    fun report_shape shape entry =
      (case shape of
         URust_AST.Unit_Shape =>
           if I.constructor_shape entry = I.Unit_Constructor
           then ()
           else
             error
               "urust_datatype: pretty replay changed a unit constructor shape"
       | URust_AST.Tuple_Shape _ =>
           if I.constructor_shape entry = I.Tuple_Constructor
           then ()
           else
             error
               "urust_datatype: pretty replay changed a tuple constructor shape"
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
    ({rust_name, hol_type_name, constructors, selectors, lenses, register_notation,
      backend, source_descriptors, source_parameters, backend_parameters, ...}:
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
      constructor_rows @ (if register_notation then lens_rows else [])
    val item_row =
      Pretty.block
        [Pretty.str "  item: ",
         Pretty.str rust_name,
         Pretty.str " -> ",
         pretty_type_identity lthy hol_type_name]
    val parameter_ctxt = Config.put show_sorts true lthy
    val parameter_rows = map2
      (fn URust_AST.Generic_Parameter (name, _, kind) => fn parameter =>
        Pretty.block
          [Pretty.str ((case kind of URust_AST.Type_Parameter => ""
             | URust_AST.Const_Parameter => "const ") ^ name ^ " -> "),
           Syntax.pretty_typ parameter_ctxt (TFree parameter)])
      source_descriptors source_parameters
    val implicit_rows = map (fn parameter => Pretty.block
      [Pretty.str "implicit ", Syntax.pretty_typ parameter_ctxt (TFree parameter)])
      backend_parameters
  in
    Pretty.chunks
      (Pretty.keyword1 "urust_datatype generated artifacts" ::
       item_row ::
       Pretty.block [Pretty.str "  backend: ", Pretty.str backend] ::
       Pretty.block [Pretty.str "  parameters: ", Pretty.enum ", " "(" ")"
         (parameter_rows @ implicit_rows)] ::
       pretty_manifest_section "constructors" constructor_rows @
       pretty_manifest_section "selectors" selector_rows @
       pretty_manifest_section "lenses" lens_rows @
       pretty_manifest_section "installed Rust mappings"
         mapping_rows)
  end

fun constructor_argument_types entry =
  (case URust_Item_Scope.constructor_scheme entry of
     Const (_, typ) => binder_types (Type.legacy_freeze_type typ)
   | _ => [])

fun pretty_constructor_declaration lthy
    (rust_path, entry) =
  let
    val constructor_name =
      const_name_of
        (URust_Item_Scope.constructor_term entry)
    val arguments = constructor_argument_types entry
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

fun pretty_parameterized_type_identity lthy hol_type_name backend_parameters =
  if null backend_parameters then pretty_type_identity lthy hol_type_name
  else
    Pretty.block
      [Pretty.enclose "(" ")"
         (Pretty.commas
           (map (Syntax.pretty_typ lthy o TFree) backend_parameters)),
       Pretty.brk 1,
       pretty_type_identity lthy hol_type_name]

fun pretty_record_declaration lthy hol_type_name backend_parameters constructors =
  let
    val (_, entry) = the_single constructors
    val fields = URust_Item_Scope.constructor_fields entry
    val arguments = constructor_argument_types entry
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
          pretty_parameterized_type_identity lthy hol_type_name backend_parameters,
          Pretty.str " ="] ::
       field_rows)
  end

fun pretty_standard_datatype_declaration lthy backend hol_type_name parameters constructors =
  Pretty.chunks
    (Pretty.block
       [Pretty.keyword1 (if backend = "hol" then "datatype" else backend),
        Pretty.brk 1,
        pretty_parameterized_type_identity lthy hol_type_name parameters,
        Pretty.str " ="] ::
     map (pretty_constructor_declaration lthy) constructors)

fun pretty_normalized_declaration lthy
    ({hol_type_name, source_parameters, backend_parameters, backend, constructors, item, ...}:
      generated_artifacts) =
  let
    val parameters = source_parameters @ backend_parameters
  in
    (case item of
       URust_AST.Struct_Item (_, _, URust_AST.Named_Shape (_ :: _), _) =>
         pretty_record_declaration lthy hol_type_name parameters constructors
     | _ =>
         pretty_standard_datatype_declaration
           lthy backend hol_type_name parameters constructors)
  end

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

fun literal_discriminant integer =
  let
    val raw = URust_AST.integer_literal_lexeme integer
    val pos = URust_AST.integer_literal_position integer
    val _ = if is_none (URust_AST.integer_literal_suffix_position integer) then ()
      else positioned_datatype_error "discriminants must be unsuffixed literal integers" pos
    val value = Parser_Utils.read_unsigned_integer raw
  in case value of SOME value => value | NONE =>
    positioned_datatype_error "unsupported literal discriminant" pos end

fun select_backend requested explicit_width repr discriminants item =
  let
    val width = case repr of NONE => explicit_width | SOME (name, pos) =>
      let
        val repr_width = case AList.lookup (op =)
          [("u8", 8), ("u16", 16), ("u32", 32), ("u64", 64), ("u128", 128)] name of
            SOME width => width
          | NONE => positioned_datatype_error ("unsupported repr " ^ quote name) pos
        val _ = case explicit_width of NONE => () | SOME width =>
          if width = repr_width then () else
            positioned_datatype_error "word_width conflicts with Rust repr" pos
      in SOME repr_width end
    val (variants, is_enum) = case item of URust_AST.Enum_Item (_, _, variants, _) => (variants, true)
      | _ => ([], false)
    val nullary = forall (fn URust_AST.Datatype_Variant (_, _, shape) =>
      null (shape_fields shape)) variants
    val selected = if requested = "auto" then
        if is_enum then if is_some width andalso nullary then "simple_word_enum" else "enum"
        else "hol"
      else requested
    val pos = URust_AST.datatype_item_position item
    val _ = if not is_enum andalso selected <> "hol" then
      positioned_datatype_error "enum backends require an enum declaration" pos else ()
    val _ = if selected = "simple_word_enum" andalso (is_none width orelse not nullary) then
      positioned_datatype_error "simple_word_enum requires an explicit width and no payload" pos else ()
    val _ = if is_some explicit_width andalso selected <> "simple_word_enum" then
      positioned_datatype_error "word_width requires the simple_word_enum backend" pos else ()
    fun value (URust_AST.Datatype_Variant (name, pos, _)) previous =
      let val current = case AList.lookup (op =) discriminants name of
            NONE => previous + 1 | SOME integer => literal_discriminant integer
          val _ = if selected <> "simple_word_enum" then () else
            if current >= 0 andalso current < Integer.pow (the width) 2 then ()
            else positioned_datatype_error ("discriminant out of range for " ^
              string_of_int (the width) ^ " bits") pos
      in (current, current) end
    val (values, _) = fold_map value variants (~1)
    val _ = if selected = "simple_word_enum" andalso not (null (duplicates (op =) values)) then
      positioned_datatype_error "duplicate discriminant" pos else ()
  in (selected, width, values) end

fun finish_metadata selected source_parameters backend_parameters
    ({rust_name, hol_type_name, hol_type, native_constructors, native_selectors,
      selector_definitions, constructors, selectors, lenses, item, ...}: generated_datatype) =
  {rust_name = rust_name, hol_type_name = hol_type_name,
   hol_type = hol_type, backend_parameters = backend_parameters,
   source_parameters = source_parameters, backend = selected,
   native_constructors = native_constructors, native_selectors = native_selectors,
   selector_definitions = selector_definitions,
   constructors = constructors, selectors = selectors, lenses = lenses, item = item}: generated_datatype

(* Validation that depends only on the parsed item, its options and the enclosing naming. A
   multi-item command prepares every member before its first declaration. Field types and the
   backend chosen for them depend on earlier declarations and are resolved when declaring. *)
type prepared =
  {declaration: declaration,
   source_item: URust_AST.urust_datatype,
   descriptors: URust_AST.generic_parameter list,
   item: URust_AST.urust_datatype,
   rust_name: string,
   rust_pos: Position.T,
   type_binding: binding,
   resolved_renames: binding Symtab.table,
   repr: (string * Position.T) option,
   discriminants: (string * URust_AST.integer_literal) list}

fun prepare
    (declaration as {source, explicit_binding, pp_test, renames, unprefixed_selectors, backend,
      word_width, ...} : declaration) source_item lthy : prepared =
  let
    val (descriptors, repr, discriminants, item) = case source_item of
      URust_AST.Datatype_Header (descriptors, repr, values, item) => (descriptors, repr, values, item)
    | item => ([], NONE, [], item)
    val (rust_name, rust_pos) =
      (case item of
         URust_AST.Struct_Item (name, pos, _, _) => (name, pos)
       | URust_AST.Enum_Item (name, pos, _, _) => (name, pos))
    val _ = reject_recursive_item rust_name item
    val _ = List.app (fn (name, pos, _, shape) => validate_shape name pos shape)
      (item_constructor_descriptors item)
    val _ =
      if pp_test
      then datatype_roundtrip lthy source source_item
      else ()
    val type_binding =
      the_default (infer_datatype_binding rust_name rust_pos)
        explicit_binding
    val explicit_renames = resolve_renames lthy item renames
    val resolved_renames =
      (case unprefixed_selectors of
         NONE => explicit_renames
       | SOME pos =>
           (case try (select_backend backend word_width repr discriminants) item of
              SOME ("simple_word_enum", _, _) =>
                positioned_datatype_error
                  ("unprefixed_selectors does not apply to the simple_word_enum backend, " ^
                    "which generates no selectors")
                  pos
            | _ => add_unprefixed_selectors lthy item explicit_renames))
  in
    {declaration = declaration, source_item = source_item, descriptors = descriptors,
     item = item, rust_name = rust_name, rust_pos = rust_pos, type_binding = type_binding,
     resolved_renames = resolved_renames, repr = repr, discriminants = discriminants}
  end

(* Authored definition entities of the completed artifacts, regenerated after the invisible
   backend run. *)
fun artifact_definitions lthy
    ({hol_type_name, constructors, selectors, lenses, selector_definitions,
      lens_definitions, ...}: generated_artifacts) =
  let
    val consts = Consts.space_of (Proof_Context.consts_of lthy)
    val facts = Facts.space_of (Proof_Context.facts_of lthy)
    val constructor_names =
      map_filter
        (fn (_, entry) =>
          (case URust_Item_Scope.constructor_term entry of
             Const (name, _) => SOME name
           | _ => NONE))
        constructors
  in
    [(Proof_Context.type_space lthy, hol_type_name)] @
    map (pair consts) (constructor_names @ map #2 selectors @ map #2 lenses) @
    map (pair facts)
      (map (Thm_Name.short o Thm.get_name_hint) selector_definitions @
        map #1 lens_definitions)
  end

(* The shared declaration operation for an already prepared item. Generation and registration
   run in invisible backend contexts within one report transaction, which joins an enclosing
   command transaction; authored definition entities are regenerated afterwards. Successful
   result output is returned for the caller to emit after its transaction. *)
(* The registrations that declaring a prepared item makes, from the same constructor descriptors,
   backend selection and plugin filter as declaration: the item type and its declaration mapping,
   every constructor, and, for the native simple_word_enum backend with the urust_conversion plugin,
   the conversion call notations that plugin registers. A backend selection that the declaration
   will reject contributes no conversions; the declaration reports the error in its own order. *)
fun prepared_registrations ctxt
    ({declaration = {backend, word_width, plugins, ...}, item, rust_name, repr, discriminants,
      ...}: prepared) : URust_Imports.registrations =
  let
    val conversions =
      (case try (select_backend backend word_width repr discriminants) item of
         SOME ("simple_word_enum", SOME width, _) =>
           if native_plugins plugins ctxt \<^plugin>\<open>urust_conversion\<close>
           then Simple_Word_Enum_uRust.conversion_rust_names rust_name width
           else []
       | _ => [])
    val generated_struct = (case item of URust_AST.Struct_Item _ => true | _ => false)
  in
    {item_types = [(rust_name, generated_struct)],
     type_mappings = [rust_name],
     constructors =
       map (fn (rust_path, _, origin, shape) => (rust_path, origin, scope_constructor_shape shape))
         (item_constructor_descriptors item),
     literal_notations = [],
     call_notations = conversions}
  end

fun declare_prepared
    ({declaration =
        {interactive, verbosity, pretty, register_notation, parameters, plugins, backend,
         word_width, ...},
      source_item, descriptors, item, rust_name, rust_pos, type_binding, resolved_renames,
      repr, discriminants}: prepared) lthy =
  let
    val expected_hol_type_name =
      Local_Theory.full_name lthy type_binding
    val ((final_lthy, artifacts, pretty_declaration), type_reports) =
      URust_Report_Transaction.capture (fn () =>
        let
          val {types, source_parameters, backend_parameters} =
            URust_Type_Mappings.resolve_declaration lthy descriptors parameters (item_field_types item)
          val all_parameters = source_parameters @ backend_parameters
          (* Backend selection follows field resolution, so item diagnostics keep their order. *)
          val (selected, width, values) = select_backend backend word_width repr discriminants item
          val _ =
            URust_Type_Mappings.preflight_declaration_scheme
              {rust_name = rust_name,
               rust_pos = rust_pos,
               hol_type_name = expected_hol_type_name,
               hol_type =
                 Type (expected_hol_type_name, map TFree all_parameters),
               source_parameters = source_parameters,
               parameter_kinds = map (fn URust_AST.Generic_Parameter (_, _, kind) => kind) descriptors,
               backend_parameters = backend_parameters}
              lthy
          fun generate backend_lthy =
            let
              (* Datatype generation opens nested targets from the enclosing target contexts.
                 Configure every existing target and restore its own setting after generation. *)
              val overloaded_settings = Unsynchronized.ref ([]: (int * bool) list)
              val generation_lthy = backend_lthy
                |> Local_Theory.map_contexts (fn depth => fn ctxt =>
                    (overloaded_settings := (depth, Config.get ctxt Typedef.overloaded) ::
                        !overloaded_settings;
                     Config.put Typedef.overloaded true ctxt))
                |> Local_Theory.background_theory (Config.put_global Typedef.overloaded true)
                |> Config.put Proof_Display.show_results false
              val (generated, generated_lthy) =
                generate_urust_datatype selected plugins width values register_notation
                  resolved_renames all_parameters types type_binding item generation_lthy
              val native_parameters = #backend_parameters generated
              val (native_source, native_backend) = chop (length source_parameters) native_parameters
              val generated = finish_metadata selected native_source native_backend generated
              val registered_lthy =
                generated_lthy
                |> register_generated_datatype generated
                |> URust_Type_Mappings.register_declaration_scheme
                    {rust_name = rust_name,
                     rust_pos = rust_pos,
                     hol_type_name = #hol_type_name generated,
                     hol_type = #hol_type generated,
                     source_parameters = #source_parameters generated,
                     parameter_kinds =
                       map (fn URust_AST.Generic_Parameter (_, _, kind) => kind) descriptors,
                     backend_parameters = #backend_parameters generated}
              val restored_lthy =
                registered_lthy
                |> Config.put Proof_Display.show_results
                    (Config.get backend_lthy Proof_Display.show_results)
                |> Local_Theory.background_theory (Config.put_global Typedef.overloaded
                    (Config.get_global (Proof_Context.theory_of backend_lthy) Typedef.overloaded))
                |> Local_Theory.map_contexts (fn depth =>
                    Config.put Typedef.overloaded
                      (the (AList.lookup (op =) (!overloaded_settings) depth)))
            in (generated, restored_lthy) end
          val (generated, final_lthy) =
            URust_Report_Transaction.invisible_declarations (K I) generate lthy
          val artifacts =
            completed_generated_artifacts source_item descriptors parameters register_notation
              generated final_lthy
          val _ =
            URust_Report_Transaction.defer_definitions final_lthy
              (artifact_definitions final_lthy artifacts)
          val _ =
            report_generated_field_declarations final_lthy artifacts
          val pretty_declaration =
            if pretty andalso verbosity > 0 andalso
                verbosity_output_enabled interactive final_lthy
            then
              SOME
                (URust_Printer_Output.pretty_human_datatype_with_reparse
                  (report_generated_datatype_replay
                    (URust_Import_Scope.transfer_frames lthy final_lthy) artifacts)
                  source_item)
            else NONE
        in
          (final_lthy, artifacts, pretty_declaration)
        end)
    val _ = URust_Report_Transaction.replay final_lthy type_reports
  in
    (fn () =>
      print_generated_datatype interactive verbosity
        pretty_declaration
        final_lthy artifacts,
     final_lthy)
  end

fun declare declaration source_item lthy =
  declare_prepared (prepare declaration source_item lthy) lthy

fun define (declaration as {source, ...}: declaration) lthy =
  let
    val source_item =
      (case URust_Parser.parse_datatype_source lthy source of
         SOME item => item
       | NONE =>
           positioned_datatype_error
             "empty datatype item" (Input.pos_of source))
    val (output, lthy') = declare declaration source_item lthy
    val _ = output ()
  in lthy' end

end
\<close>

end
