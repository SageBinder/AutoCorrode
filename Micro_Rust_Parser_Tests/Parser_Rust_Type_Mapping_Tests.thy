theory Parser_Rust_Type_Mapping_Tests
  imports Parser_Test_Utils
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = false]]
declare [[urust_verbosity = 0]]

section\<open> Extensible Rust-to-HOL type mappings \<close>

urust_type "PacketId" = \<open>64 word\<close>
urust_type "transport::PacketFlag" = \<open>bool\<close>
urust_type "ResultMap<'ok, 'err>" = \<open>('ok, 'err) result\<close>
urust_type "Wrap<'value>" = \<open>'value option\<close>
urust_type "Ordered<'value>" = \<open>'value::linorder list\<close>
urust_type "wire::Envelope<'header>::Body<'payload>" =
  \<open>('header, 'payload) result\<close>
urust_type "FunctionType" = \<open>nat \<Rightarrow> nat\<close>
urust_type "u128" = \<open>128 word\<close>

urust_type "AlphaMap<'left, 'right>" =
  \<open>('left, 'right) result\<close>

urust_type "AlphaMap<'x, 'y>" =
  \<open>('x, 'y) result\<close>

urust_datatype \<open>
  struct MappedTypes {
    identifier: PacketId,
    flag: transport::PacketFlag,
    outcome: ResultMap<PacketId, bool>,
    nested: Wrap<Wrap<Wrap<u8>>>,
    commented: ResultMap<
      /* first */ Wrap<u16>,
      // second
      Wrap<bool>,
    >,
    segmented: wire::Envelope<u8>::Body<PacketId>,
    wide: u128,
    unit: (),
    grouped: (PacketId),
    pair: (u8, bool),
  }
\<close>

urust_datatype \<open>
  struct MappedTupleTypes {
    flat: (u8, bool, PacketId),
    flat_four: (u8, bool, PacketId, Wrap<u16>),
    nested_tuple: (u8, (bool, PacketId)),
    generic_tuple: (Wrap<u8>, PacketId),
    escaped_tuple: (PacketId, \<tau>\<open>nat\<close>),
    escaped: \<tau>\<open>nat option\<close>,
  }
\<close>

urust_datatype \<open>
  struct TupleArity16((
    u8, u8, u8, u8, u8, u8, u8, u8,
    u8, u8, u8, u8, u8, u8, u8, u8,
  ));
\<close>

urust_datatype \<open>
  struct TupleArity17((
    u8, u8, u8, u8, u8, u8, u8, u8,
    u8, u8, u8, u8, u8, u8, u8, u8, u8,
  ));
\<close>

urust_datatype explicit_mapped_hol \<open>
  enum MappedChoice {
    Empty,
    Payload(PacketId),
  }
\<close>

urust_datatype \<open>
  struct UsesGenerated(MappedTypes, MappedTupleTypes, MappedChoice);
\<close>

datatype ordinary_type_registry_control =
  Ordinary_Type_Registry_Control

bundle scoped_type_mapping
begin

urust_type "ScopedType" = \<open>nat\<close>

end

bundle conflicting_type_mapping_left
begin

urust_type "BundleConflict" = \<open>nat\<close>

end

bundle conflicting_type_mapping_right
begin

urust_type "BundleConflict" = \<open>bool\<close>

end

context includes scoped_type_mapping
begin

urust_datatype \<open>
  struct ScopedTypeHolder(ScopedType);
\<close>

end

locale type_mapping_left
begin

urust_type "LocaleType" = \<open>nat\<close>

urust_datatype \<open>
  struct LocaleTypeHolder(LocaleType);
\<close>

end

locale type_mapping_right
begin

urust_type "LocaleType" = \<open>bool\<close>

urust_datatype \<open>
  struct LocaleTypeHolder(LocaleType);
\<close>

end

section\<open> Registry and generated-type audits \<close>

ML_val \<open>
  local
    val expected =
      [("u8", \<^typ>\<open>8 word\<close>),
       ("u16", \<^typ>\<open>16 word\<close>),
       ("u32", \<^typ>\<open>32 word\<close>),
       ("u64", \<^typ>\<open>64 word\<close>),
       ("usize", \<^typ>\<open>64 word\<close>),
       ("i32", \<^typ>\<open>32 word\<close>),
       ("i64", \<^typ>\<open>64 word\<close>),
       ("bool", \<^typ>\<open>bool\<close>),
       ("()", \<^typ>\<open>unit\<close>)]

    fun check (name, typ) =
      (case URust_Type_Mappings.lookup \<^context> name of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry = typ andalso
               URust_Type_Mappings.entry_arities entry = [0] andalso
               null
                 (URust_Type_Mappings.entry_parameter_sorts entry) andalso
               URust_Type_Mappings.entry_origin entry =
                 "urust_type declaration"
           then ()
           else
             error
               ("unexpected built-in uRust type mapping for " ^
                 quote name)
       | NONE =>
           error
             ("missing built-in uRust type mapping for " ^
               quote name))

    val _ = List.app check expected
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  local
    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun run source_name command_text () =
      let
        val thy = \<^theory>\<open>Parser_Test_Utils\<close>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    val command_text =
      "urust_datatype before_u128 " ^
        cartouche " struct BeforeU128(u128); "
    val _ =
      (case Exn.result (run "before-u128" command_text) () of
         Exn.Res _ =>
           error "u128 unexpectedly resolved before registration"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring
               "unknown Rust type \"u128\"" (Runtime.exn_message exn)
           then ()
           else
             error
               ("unexpected pre-registration u128 diagnostic: " ^
                 Runtime.exn_message exn))
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  val SOME alpha =
    URust_Type_Mappings.lookup \<^context> "AlphaMap"
  val _ =
    if URust_Type_Mappings.entry_arities alpha = [2] andalso
        length
          (URust_Type_Mappings.entry_parameter_sorts alpha) = 2
    then ()
    else error "alpha-normalized mapping metadata changed"
\<close>

ML_val \<open>
  local
    fun require_sugar name =
      (case Ctr_Sugar.ctr_sugar_of \<^context> name of
         SOME sugar => sugar
       | NONE => error ("missing generated datatype " ^ quote name))

    fun argument_types name =
      let
        val sugar = require_sugar name
      in
        (case #ctrs sugar of
           [Const (constructor, _)] =>
             binder_types
               (Consts.the_constraint
                 (Proof_Context.consts_of \<^context>) constructor)
         | _ => error "expected one generated constructor")
      end

    fun tuple_elements typ =
      if typ = \<^typ>\<open>tnil\<close> then []
      else
        (case try HOLogic.dest_prodT typ of
           SOME (head, tail) => head :: tuple_elements tail
         | NONE => error "expected a tnil-terminated tuple type")

    val mapped = argument_types \<^type_name>\<open>mapped_types\<close>
    val _ =
      if mapped =
          [\<^typ>\<open>64 word\<close>,
           \<^typ>\<open>bool\<close>,
           \<^typ>\<open>(64 word, bool) result\<close>,
           \<^typ>\<open>8 word option option option\<close>,
           \<^typ>\<open>(16 word option, bool option) result\<close>,
           \<^typ>\<open>(8 word, 64 word) result\<close>,
           \<^typ>\<open>128 word\<close>,
           \<^typ>\<open>unit\<close>,
           \<^typ>\<open>64 word\<close>,
           \<^typ>\<open>8 word \<times> bool \<times> tnil\<close>]
      then ()
      else error "registry-backed datatype field resolution changed"

    val mapped_tuples =
      argument_types \<^type_name>\<open>mapped_tuple_types\<close>
    val _ =
      if mapped_tuples =
          [\<^typ>\<open>8 word \<times> bool \<times> 64 word \<times> tnil\<close>,
           \<^typ>\<open>8 word \<times> bool \<times> 64 word \<times> 16 word option \<times> tnil\<close>,
           \<^typ>\<open>8 word \<times> (bool \<times> 64 word \<times> tnil) \<times> tnil\<close>,
           \<^typ>\<open>8 word option \<times> 64 word \<times> tnil\<close>,
           \<^typ>\<open>64 word \<times> nat \<times> tnil\<close>,
           \<^typ>\<open>nat option\<close>]
      then ()
      else error "registry-backed tuple field resolution changed"

    val [tuple16] =
      argument_types \<^type_name>\<open>tuple_arity16\<close>
    val [tuple17] =
      argument_types \<^type_name>\<open>tuple_arity17\<close>
    val _ =
      if length (tuple_elements tuple16) = 16 andalso
          length (tuple_elements tuple17) = 17
      then ()
      else error "large Rust tuple encoding changed"
    val _ =
      if tuple16 = tuple17
      then error "tuple arities 16 and 17 collapsed"
      else ()

    val _ =
      (case URust_Type_Mappings.lookup \<^context> "MappedTypes" of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry =
               \<^typ>\<open>mapped_types\<close>
           then ()
           else error "generated struct mapping has the wrong HOL type"
       | NONE => error "generated struct did not register a type mapping")
    val _ =
      (case URust_Type_Mappings.lookup \<^context> "MappedChoice" of
         SOME entry =>
           if URust_Type_Mappings.entry_template entry =
               \<^typ>\<open>explicit_mapped_hol\<close>
           then ()
           else error "generated enum mapping has the wrong HOL type"
       | NONE => error "generated enum did not register a type mapping")
    val _ =
      if argument_types \<^type_name>\<open>uses_generated\<close> =
          [\<^typ>\<open>mapped_types\<close>,
           \<^typ>\<open>mapped_tuple_types\<close>,
           \<^typ>\<open>explicit_mapped_hol\<close>]
      then ()
      else error "later generated-type references changed"
  in
    val _ = ()
  end
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup
      \<^context> "ordinary_type_registry_control"
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup \<^context> "ScopedType"
  val SOME _ =
    URust_Type_Mappings.lookup \<^context> "ScopedTypeHolder"
\<close>

ML_val \<open>
  val NONE =
    URust_Type_Mappings.lookup \<^context> "LocaleType"
  val NONE =
    URust_Type_Mappings.lookup \<^context> "LocaleTypeHolder"
\<close>

section\<open> Source positions and registry markup \<close>

ML_val \<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation
    val mapping_kind = "micro_rust_type_mapping"

    fun audit message condition =
      if condition then ()
      else error ("uRust type mapping markup audit: " ^ message)

    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun command_start source_name =
      Position.make0 1 1 0 "" source_name source_name

    fun run source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (command_start source_name)
            command_text
      in
        fold (Toplevel.command_exception true) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun mapping_ids property rust_name position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN =
                  SOME mapping_kind andalso
                Properties.get properties Markup.nameN =
                  SOME rust_name andalso
                has_position properties position
            then Properties.get properties property
            else NONE)
      |> distinct (op =)

    fun mapping_entities markup =
      filter
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN =
              SOME mapping_kind)
        markup

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing source token " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (Position.range
            (token_start,
             Position.symbol_explode needle token_start))
      end

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect
              (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun range_of position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    val declaration_file = "urust-type-mapping-definition"
    val declaration_text =
      "urust_type \"MarkupId\" = " ^ cartouche "nat"
    val (declaration_state, declaration_markup) =
      Parser_Test_Reports.markup
        (run declaration_file declaration_text)
    val declaration_ctxt =
      Toplevel.context_of declaration_state
      |> Context_Position.set_visible true
    val SOME mapping =
      URust_Type_Mappings.lookup declaration_ctxt "MarkupId"
    val identity =
      Value.print_int
        (URust_Type_Mappings.entry_identity mapping)
    val declaration_position =
      URust_Type_Mappings.entry_declaration_position mapping
    val _ =
      audit "declaration position lost its source file"
        (Position.file_of declaration_position =
          SOME declaration_file)
    val declaration_ids =
      mapping_ids Markup.defN "MarkupId"
        declaration_position declaration_markup
    val _ =
      audit
        ("declaration entity identity or exact range changed: " ^
          commas_quote declaration_ids ^ " from " ^
          commas_quote
            (map
              (fn (_, properties) =>
                commas
                  (map
                    (fn (name, value) => name ^ "=" ^ value)
                    properties))
              (mapping_entities declaration_markup)))
        (declaration_ids = [identity])

    val parameter_file = "urust-type-mapping-parameters"
    val parameter_text =
      "urust_type \"MarkupPair<'left, 'right>\" = " ^
        cartouche "('left, 'right) result"
    val (_, parameter_markup) =
      Parser_Test_Reports.markup
        (run parameter_file parameter_text)
    val parameter_start = command_start parameter_file
    val left_position =
      token_position parameter_text parameter_start "'left" 0
    val right_position =
      token_position parameter_text parameter_start "'right" 0
    val _ =
      audit "first mapping placeholder lost native type-variable markup"
        (count_markup Markup.tfreeN
          left_position parameter_markup = 1)
    val _ =
      audit "second mapping placeholder lost native type-variable markup"
        (count_markup Markup.tfreeN
          right_position parameter_markup = 1)

    val use_text = " struct MarkupHolder(MarkupId); "
    val use_start =
      Position.make0 41 5000 0 "" ""
        "urust-type-mapping-reference"
    val use_source =
      Parser_Lex_Util.positioned_content_source
        use_text use_start
    val SOME parsed_use =
      URust_Parser.parse_datatype_source
        declaration_ctxt use_source
    val mapped_type =
      (case parsed_use of
         URust_AST.Struct_Item
           (_, _, URust_AST.Tuple_Shape [typ], _) => typ
       | _ => error "unexpected mapping markup test AST")
    val use_position =
      URust_AST.rust_type_position mapped_type
    val expected_use_position =
      token_position use_text use_start "MarkupId" 0
    val _ =
      audit "parsed mapping-use source range changed"
        (Position.offset_of use_position =
          Position.offset_of expected_use_position andalso
         Position.end_offset_of use_position =
          Position.end_offset_of expected_use_position)
    val (resolved_type, deferred_reports) =
      Navigation.capture
        (fn () =>
          URust_Type_Mappings.resolve
            declaration_ctxt mapped_type)
    val _ =
      audit "mapped HOL type changed"
        (resolved_type = \<^typ>\<open>nat\<close>)
    val ((), use_markup) =
      Parser_Test_Reports.markup
        (fn () =>
          Navigation.replay declaration_ctxt deferred_reports)
    val _ =
      audit "mapping reference identity or exact range changed"
        (mapping_ids Markup.refN "MarkupId"
          expected_use_position use_markup = [identity])
    val _ =
      audit "mapping reference typing markup changed"
        (count_markup Markup.typingN
          expected_use_position use_markup = 1)
    val _ =
      audit "mapping reference keyword styling changed"
        (count_markup Markup.keyword3N
          expected_use_position use_markup = 1)

    val unknown_text =
      " struct PositionedUnknown(missing::Type); "
    val unknown_start =
      Position.make0 52 8000 0 "" ""
        "urust-type-mapping-diagnostic"
    val SOME parsed_unknown =
      URust_Parser.parse_datatype_source
        \<^context>
        (Parser_Lex_Util.positioned_content_source
          unknown_text unknown_start)
    val unknown_type =
      (case parsed_unknown of
         URust_AST.Struct_Item
           (_, _, URust_AST.Tuple_Shape [typ], _) => typ
       | _ => error "unexpected positioned diagnostic AST")
    val unknown_position =
      URust_AST.rust_type_position unknown_type
    val unknown_message =
      (case Exn.result
          (fn () =>
            Navigation.capture
              (fn () =>
                URust_Type_Mappings.resolve
                  \<^context> unknown_type)) () of
         Exn.Res _ =>
           error "unknown positioned type unexpectedly resolved"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    val _ =
      audit "unknown-type guidance changed"
        (String.isSubstring
          ("unknown Rust type \"missing::Type\"; " ^
           "declare it with urust_type or use")
          unknown_message)
    val _ =
      audit "unknown-type diagnostic range changed"
        (diagnostic_ranges
          (YXML.parse_body unknown_message) =
            [range_of unknown_position])

    val failure_text =
      "urust_datatype " ^
        cartouche
          (" struct MarkupFailure { " ^
           "accepted: PacketId, rejected: MissingMarkupType, } ")
    val (failure_result, failure_markup) =
      Parser_Test_Reports.markup
        (fn () =>
          Exn.result
            (run "urust-type-mapping-failure" failure_text) ())
    val _ =
      (case failure_result of
         Exn.Res _ =>
           error "failing datatype unexpectedly succeeded"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit "failing datatype diagnostic changed"
               (String.isSubstring
                 "unknown Rust type \"MissingMarkupType\""
                 (Runtime.exn_message exn)))
    val _ =
      audit "failed datatype emitted registry success markup"
        (null (mapping_entities failure_markup))
  in
    val _ = ()
  end
\<close>

section\<open> Diagnostics, rollback, and recovery \<close>

ML_val \<open>
  local
    fun cartouche body =
      Symbol.open_ ^ body ^ Symbol.close

    fun run source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun rejected label expected command_text =
      (case Exn.result (run label command_text) () of
         Exn.Res _ =>
           error
             ("expected command rejection for " ^ quote label)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else if String.isSubstring expected
               (Runtime.exn_message exn)
           then ()
           else
             error
               ("unexpected diagnostic for " ^ quote label ^
                 "\nexpected: " ^ quote expected ^
                 "\nactual: " ^
                 Runtime.exn_message exn))

    fun accepted label command_text =
      (case Exn.result (run label command_text) () of
         Exn.Res state => state
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             error
               ("unexpected rejection for " ^ quote label ^ ": " ^
                 Runtime.exn_message exn))

    fun datatype_command name field_type =
      "urust_datatype " ^ name ^ " " ^
        cartouche
          (" struct " ^ name ^ "(" ^ field_type ^ "); ")

    fun mapping key typ =
      "urust_type " ^ quote key ^ " = " ^ cartouche typ

    val SOME alpha_before =
      URust_Type_Mappings.lookup \<^context> "AlphaMap"
    val alpha_state =
      accepted "mapping-idempotent-alpha-renaming"
        (mapping "AlphaMap<'first, 'second>"
          "('first, 'second) result")
    val SOME alpha_after =
      URust_Type_Mappings.lookup
        (Toplevel.context_of alpha_state) "AlphaMap"
    val _ =
      if URust_Type_Mappings.entry_identity alpha_before =
          URust_Type_Mappings.entry_identity alpha_after
      then ()
      else error "idempotent mapping registration changed identity"

    val _ =
      rejected "mapping-template-conflict"
        "conflicting active mappings for \"PacketId\""
        (mapping "PacketId" "32 word")
    val _ =
      rejected "mapping-arity-conflict"
        "different generic arity"
        (mapping "PacketId<'a>" "'a")
    val _ =
      rejected "mapping-missing-placeholder"
        "missing \"'b\""
        (mapping "Missing<'a, 'b>" "'a option")
    val _ =
      rejected "mapping-extra-placeholder"
        "undeclared \"'b\""
        (mapping "Extra<'a>" "('a, 'b) result")
    val _ =
      rejected "mapping-duplicate-placeholder"
        "mapping placeholders must be distinct"
        (mapping "Duplicate<'a, 'a>" "'a option")
    val _ =
      rejected "mapping-malformed-parameters"
        "malformed Rust type key"
        (mapping "Malformed<'a,,>" "'a")
    val _ =
      rejected "builtin-override"
        "conflicting active mappings for \"u8\""
        (mapping "u8" "nat")
    val _ =
      rejected "bundle-conflict"
        "conflicting active mappings for \"BundleConflict\""
        ("context includes conflicting_type_mapping_left\n" ^
          "begin\n" ^
          "context includes conflicting_type_mapping_right\n" ^
          "begin\n" ^
          "end\n" ^
          "end")

    val _ =
      rejected "unknown-path"
        "unknown Rust type \"missing::Type\""
        (datatype_command "UnknownPath" "missing::Type")
    val _ =
      rejected "unknown-str"
        "unknown Rust type \"str\""
        (datatype_command "UnknownStr" "str")
    val _ =
      rejected "unknown-never"
        "unknown Rust type \"!\""
        (datatype_command "UnknownNever" "!")
    val _ =
      rejected "wrong-generic-arity"
        "active urust_type mapping expects [2]"
        (datatype_command "WrongArity" "ResultMap<u8>")
    val _ =
      rejected "numeric-generic"
        "numeric generic arguments is not supported"
        (datatype_command "NumericGeneric" "Wrap<4>")
    val _ =
      rejected "wrong-sort"
        "does not satisfy sort"
        (datatype_command "WrongSort" "Ordered<FunctionType>")
    val _ =
      rejected "singleton-tuple"
        "singleton tuple types is not supported"
        (datatype_command "SingletonTuple" "(u8,)")
    val _ =
      rejected "reference"
        "Rust reference types is not supported"
        (datatype_command "ReferenceField" "&u32")
    val _ =
      rejected "mutable-reference"
        "Rust reference types is not supported"
        (datatype_command "MutableReferenceField" "&mut u32")
    val _ =
      rejected "raw-pointer"
        "Rust raw pointer types is not supported"
        (datatype_command "RawPointerField" "*const u8")
    val _ =
      rejected "slice"
        "Rust slice types is not supported"
        (datatype_command "SliceField" "[u8]")
    val _ =
      rejected "array"
        "Rust array types is not supported"
        (datatype_command "ArrayField" "[u8; 4]")
    val _ =
      rejected "recursive"
        "recursive Rust datatype reference \"RecursiveMapped\""
        (datatype_command "RecursiveMapped" "RecursiveMapped")
    val _ =
      rejected "nested-recursive"
        "recursive Rust datatype reference \"NestedRecursiveMapped\""
        (datatype_command "NestedRecursiveMapped"
          "Wrap<NestedRecursiveMapped>")
    val _ =
      rejected "enum-recursive"
        "recursive Rust datatype reference \"EnumRecursiveMapped\""
        ("urust_datatype " ^
          cartouche
            (" enum EnumRecursiveMapped { " ^
             "Again(EnumRecursiveMapped), } "))
    val _ =
      rejected "malformed-hol-escape"
        "Inner syntax error"
        (datatype_command "MalformedEscape"
          ("\<tau>" ^ cartouche "nat \<Rightarrow>"))
    val _ =
      rejected "polymorphic-hol-escape"
        "type variables are not supported"
        (datatype_command "PolymorphicEscape"
          ("\<tau>" ^ cartouche "'a"))
    val _ =
      rejected "generated-mapping-conflict"
        "conflicting active mappings for \"PacketId\""
        ("urust_datatype rollback_conflict " ^
          cartouche " struct PacketId; ")
    val _ =
      rejected "generation-failure"
        "Duplicate type name declaration"
        ("urust_datatype ordinary_type_registry_control " ^
          cartouche " struct GenerationFailure; ")

    val NONE =
      URust_Type_Mappings.lookup \<^context> "UnknownPath"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "UnknownPath"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "RecursiveMapped"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "RecursiveMapped"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "EnumRecursiveMapped"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "EnumRecursiveMapped"
    val NONE =
      URust_Type_Mappings.lookup \<^context> "GenerationFailure"
    val NONE =
      URust_Item_Scope.lookup_type \<^context> "GenerationFailure"

    val malformed =
      Parser_Lex_Util.text_source
        " struct Broken(ResultMap<Wrap<u8>,); "
    val _ =
      (case Exn.result
          (fn () =>
            URust_Parser.parse_datatype_source
              \<^context> malformed) () of
         Exn.Res _ => error "malformed generic unexpectedly parsed"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())
    val SOME _ =
      URust_Parser.parse_datatype_source \<^context>
        (Parser_Lex_Util.text_source
          " struct Recovered(ResultMap<Wrap<u8>, bool>); ")
    val SOME _ =
      URust_Parser.parse_source \<^context>
        (Parser_Lex_Util.text_source "8u32 >> 1u32")
  in
    val _ = ()
  end
\<close>

end
