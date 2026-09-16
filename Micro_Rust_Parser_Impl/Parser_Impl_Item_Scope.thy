theory Parser_Impl_Item_Scope
  imports Parser_Impl_AST
begin

section\<open> Generated Rust item scope \<close>

ML\<open>
signature URUST_ITEM_SCOPE =
sig
  datatype constructor_shape =
      Unit_Constructor
    | Tuple_Constructor
    | Named_Constructor
  datatype constructor_origin =
      Struct_Constructor
    | Enum_Variant

  type type_entry
  type field_entry
  type field_report
  type constructor_entry

  val register_type:
    {rust_name: string,
     rust_pos: Position.T,
     hol_type_name: string} ->
    local_theory -> local_theory

  val register_constructor:
    {rust_type: string,
     rust_path: string,
     rust_pos: Position.T,
     hol_type_name: string,
     constructor: term,
     origin: constructor_origin,
     shape: constructor_shape,
     fields:
       {rust_name: string,
        rust_pos: Position.T,
        selector: term} list} ->
    local_theory -> local_theory

  val lookup_type: Proof.context -> string -> type_entry option
  val lookup_constructor:
    Proof.context -> string -> constructor_entry option

  val type_rust_name: type_entry -> string
  val type_position: type_entry -> Position.T
  val type_hol_name: type_entry -> string
  val constructor_rust_type: constructor_entry -> string
  val constructor_rust_path: constructor_entry -> string
  val constructor_position: constructor_entry -> Position.T
  val constructor_hol_type: constructor_entry -> string
  val constructor_term: constructor_entry -> term
  val constructor_origin: constructor_entry -> constructor_origin
  val constructor_shape: constructor_entry -> constructor_shape
  val constructor_fields: constructor_entry -> (string * term) list
  val constructor_field_entries: constructor_entry -> field_entry list
  val field_rust_path: field_entry -> string
  val field_rust_name: field_entry -> string
  val field_position: field_entry -> Position.T
  val field_selector: field_entry -> term

  val report_type_reference:
    Proof.context -> Position.T -> type_entry -> unit
  val report_constructor_reference:
    Proof.context -> Position.T -> constructor_entry -> unit
  val report_type_definition: type_entry -> unit
  val report_constructor_definition: constructor_entry -> unit
  val report_field_definition: field_entry -> unit
  val report_field_reference:
    Proof.context -> Position.T -> field_entry -> unit
  val defer_field_reference:
    Proof.context -> Position.T -> field_entry -> unit
  val capture_field_reports:
    (unit -> 'a) -> 'a * field_report list
  val replay_field_reports:
    Proof.context -> field_report list -> unit

  val dump_types: Proof.context -> type_entry list
  val dump_constructors: Proof.context -> constructor_entry list
end

structure URust_Item_Scope :> URUST_ITEM_SCOPE =
struct
  datatype constructor_shape =
      Unit_Constructor
    | Tuple_Constructor
    | Named_Constructor
  datatype constructor_origin =
      Struct_Constructor
    | Enum_Variant

  type type_entry =
    {rust_name: string,
     rust_pos: Position.T,
     hol_type_name: string,
     serial: serial}

  type field_entry =
    {rust_path: string,
     rust_name: string,
     rust_pos: Position.T,
     selector: term,
     serial: serial}

  type field_report = Position.T * field_entry

  type constructor_entry =
    {rust_type: string,
     rust_path: string,
     rust_pos: Position.T,
     hol_type_name: string,
     constructor: term,
     origin: constructor_origin,
     shape: constructor_shape,
     fields: field_entry list,
     serial: serial}

  type data =
    {types: type_entry Symtab.table,
     constructors: constructor_entry Symtab.table}

  val empty_data: data =
    {types = Symtab.empty, constructors = Symtab.empty}

  fun same_shape (Unit_Constructor, Unit_Constructor) = true
    | same_shape (Tuple_Constructor, Tuple_Constructor) = true
    | same_shape (Named_Constructor, Named_Constructor) = true
    | same_shape _ = false

  fun same_origin (Struct_Constructor, Struct_Constructor) = true
    | same_origin (Enum_Variant, Enum_Variant) = true
    | same_origin _ = false

  fun same_field
      (left: field_entry, right: field_entry) =
    #rust_path left = #rust_path right andalso
      #rust_name left = #rust_name right andalso
      Term.aconv_untyped (#selector left, #selector right)

  fun same_fields (left, right) =
    eq_list same_field (left, right)

  fun same_type_entry
      (left: type_entry, right: type_entry) =
    #rust_name left = #rust_name right andalso
      #hol_type_name left = #hol_type_name right

  fun same_constructor_entry
      (left: constructor_entry, right: constructor_entry) =
    #rust_type left = #rust_type right andalso
      #rust_path left = #rust_path right andalso
      #hol_type_name left = #hol_type_name right andalso
      Term.aconv_untyped (#constructor left, #constructor right) andalso
      same_origin (#origin left, #origin right) andalso
      same_shape (#shape left, #shape right) andalso
      same_fields (#fields left, #fields right)

  fun merge_entry kind same (left, right) =
    if same (left, right) then left
    else
      error
        ("urust_datatype: conflicting generated Rust " ^ kind ^
          " mapping")

  fun merge_data
      ({types = left_types, constructors = left_constructors},
       {types = right_types, constructors = right_constructors}) =
    {types =
       Symtab.join
         (K (merge_entry "item" same_type_entry))
         (left_types, right_types),
     constructors =
       Symtab.join
         (K (merge_entry "constructor" same_constructor_entry))
         (left_constructors, right_constructors)}

  structure Data = Generic_Data
  (
    type T = data
    val empty = empty_data
    val merge = merge_data
  )

  val type_entity = "urust_item"
  val constructor_entity = "urust_constructor"
  val field_entity = "urust_field"

  fun lookup_type ctxt rust_name =
    Symtab.lookup (#types (Data.get (Context.Proof ctxt))) rust_name

  fun lookup_constructor ctxt rust_path =
    Symtab.lookup
      (#constructors (Data.get (Context.Proof ctxt))) rust_path

  fun type_rust_name ({rust_name, ...}: type_entry) = rust_name
  fun type_position ({rust_pos, ...}: type_entry) = rust_pos
  fun type_hol_name ({hol_type_name, ...}: type_entry) = hol_type_name
  fun constructor_rust_type
      ({rust_type, ...}: constructor_entry) = rust_type
  fun constructor_rust_path
      ({rust_path, ...}: constructor_entry) = rust_path
  fun constructor_position
      ({rust_pos, ...}: constructor_entry) = rust_pos
  fun constructor_hol_type
      ({hol_type_name, ...}: constructor_entry) = hol_type_name
  fun constructor_term
      ({constructor, ...}: constructor_entry) = constructor
  fun constructor_origin
      ({origin, ...}: constructor_entry) = origin
  fun constructor_shape
      ({shape, ...}: constructor_entry) = shape
  fun constructor_fields
      ({fields, ...}: constructor_entry) =
    map
      (fn ({rust_name, selector, ...}: field_entry) =>
        (rust_name, selector))
      fields
  fun constructor_field_entries
      ({fields, ...}: constructor_entry) = fields
  fun field_rust_path
      ({rust_path, ...}: field_entry) = rust_path
  fun field_rust_name
      ({rust_name, ...}: field_entry) = rust_name
  fun field_position
      ({rust_pos, ...}: field_entry) = rust_pos
  fun field_selector
      ({selector, ...}: field_entry) = selector

  fun field_entity_name
      ({rust_path, rust_name, ...}: field_entry) =
    rust_path ^ "." ^ rust_name

  fun report_type_reference ctxt use_pos
      ({rust_name, rust_pos, serial, ...}: type_entry) =
    Context_Position.report ctxt use_pos
      (Position.make_entity_markup
        {def = false} serial type_entity (rust_name, rust_pos))

  fun report_constructor_reference ctxt use_pos
      ({rust_path, rust_pos, serial, ...}: constructor_entry) =
    Context_Position.report ctxt use_pos
      (Position.make_entity_markup
        {def = false} serial constructor_entity
        (rust_path, rust_pos))

  fun report_type_definition
      ({rust_name, rust_pos, serial, ...}: type_entry) =
    Position.report rust_pos
      (Position.make_entity_markup
        {def = true} serial type_entity (rust_name, rust_pos))

  fun report_constructor_definition
      ({rust_path, rust_pos, serial, ...}: constructor_entry) =
    Position.report rust_pos
      (Position.make_entity_markup
        {def = true} serial constructor_entity
        (rust_path, rust_pos))

  fun report_field_definition
      (entry as {rust_pos, serial, ...}: field_entry) =
    Position.report rust_pos
      (Position.make_entity_markup
        {def = true} serial field_entity
        (field_entity_name entry, rust_pos))

  fun report_field_reference ctxt use_pos
      (entry as {rust_pos, serial, ...}: field_entry) =
    Context_Position.report ctxt use_pos
      (Position.make_entity_markup
        {def = false} serial field_entity
        (field_entity_name entry, rust_pos))

  val field_reports:
    field_report list Unsynchronized.ref Thread_Data.var =
      Thread_Data.var ()

  fun defer_field_reference ctxt use_pos entry =
    (case Thread_Data.get field_reports of
       SOME reports =>
         reports := (use_pos, entry) :: !reports
     | NONE =>
         report_field_reference ctxt use_pos entry)

  fun capture_field_reports action =
    let
      val reports =
        Unsynchronized.ref ([]: field_report list)
      val result =
        Thread_Data.setmp field_reports (SOME reports)
          action ()
    in (result, rev (!reports)) end

  fun replay_field_reports ctxt reports =
    List.app
      (fn (use_pos, entry) =>
        report_field_reference ctxt use_pos entry)
      reports

  fun insert_type entry ({types, constructors}: data) =
    {types =
       (case Symtab.lookup types (#rust_name entry) of
          NONE => Symtab.update (#rust_name entry, entry) types
        | SOME existing =>
            if same_type_entry (existing, entry)
            then types
            else
              error
                ("urust_datatype: Rust item path " ^
                  quote (#rust_name entry) ^
                  " is already mapped to HOL type " ^
                  quote (#hol_type_name existing) ^
                  Position.here (#rust_pos entry))),
     constructors = constructors}

  fun insert_constructor entry ({types, constructors}: data) =
    {types = types,
     constructors =
       (case Symtab.lookup constructors (#rust_path entry) of
          NONE =>
            Symtab.update (#rust_path entry, entry) constructors
        | SOME existing =>
            if same_constructor_entry (existing, entry)
            then constructors
            else
              error
                ("urust_datatype: Rust constructor path " ^
                  quote (#rust_path entry) ^
                  " is already mapped to a different HOL constructor" ^
                  Position.here (#rust_pos entry)))}

  fun register_type {rust_name, rust_pos, hol_type_name} lthy =
    let
      val serial = serial ()
      val entry: type_entry =
        {rust_name = rust_name,
         rust_pos = rust_pos,
         hol_type_name = hol_type_name,
         serial = serial}
      val _ =
        (case lookup_type lthy rust_name of
           NONE => ()
         | SOME existing =>
             if same_type_entry (existing, entry)
             then ()
             else
               error
                 ("urust_datatype: Rust item path " ^
                   quote rust_name ^ " is already mapped to HOL type " ^
                   quote (#hol_type_name existing) ^
                   Position.here rust_pos))
      val _ =
        Position.report rust_pos
          (Name_Space.markup
            (Proof_Context.type_space lthy) hol_type_name)
      val _ = Position.report rust_pos Markup.keyword3
      val _ =
        report_type_definition entry
    in
      lthy
      |> Local_Theory.declaration
          {pervasive = false, syntax = false, pos = rust_pos}
          (fn _ => Data.map (insert_type entry))
    end

  fun register_constructor
      {rust_type, rust_path, rust_pos, hol_type_name,
       constructor, origin, shape, fields}
      lthy =
    let
      val constructor_serial = serial ()
      val field_entries: field_entry list =
        map
          (fn {rust_name, rust_pos, selector} =>
            {rust_path = rust_path,
             rust_name = rust_name,
             rust_pos = rust_pos,
             selector = selector,
             serial = serial ()})
          fields
      val entry: constructor_entry =
        {rust_type = rust_type,
         rust_path = rust_path,
         rust_pos = rust_pos,
         hol_type_name = hol_type_name,
         constructor = constructor,
         origin = origin,
         shape = shape,
         fields = field_entries,
         serial = constructor_serial}
      val _ =
        (case lookup_constructor lthy rust_path of
           NONE => ()
         | SOME existing =>
             if same_constructor_entry (existing, entry)
             then ()
             else
               error
                 ("urust_datatype: Rust constructor path " ^
                   quote rust_path ^
                   " is already mapped to a different HOL constructor" ^
                   Position.here rust_pos))
      val _ = Position.report rust_pos Markup.keyword3
      val _ =
        (case constructor of
           Const (name, _) =>
             Position.report rust_pos
               (Name_Space.markup
                 (Consts.space_of
                   (Proof_Context.consts_of lthy)) name)
         | _ => ())
      val _ =
        report_constructor_definition entry
    in
      lthy
      |> Local_Theory.declaration
          {pervasive = false, syntax = false, pos = rust_pos}
          (fn phi =>
            let
              val mapped: constructor_entry =
                {rust_type = rust_type,
                 rust_path = rust_path,
                 rust_pos = rust_pos,
                 hol_type_name = hol_type_name,
                 constructor = Morphism.term phi constructor,
                 origin = origin,
                 shape = shape,
                 fields =
                   map
                     (fn
                       ({rust_path, rust_name, rust_pos,
                         selector, serial}: field_entry) =>
                       {rust_path = rust_path,
                        rust_name = rust_name,
                        rust_pos = rust_pos,
                        selector = Morphism.term phi selector,
                        serial = serial})
                     field_entries,
                 serial = constructor_serial}
            in Data.map (insert_constructor mapped) end)
    end

  fun dump_types ctxt =
    #types (Data.get (Context.Proof ctxt))
    |> Symtab.dest
    |> map snd

  fun dump_constructors ctxt =
    #constructors (Data.get (Context.Proof ctxt))
    |> Symtab.dest
    |> map snd
end
\<close>

end
