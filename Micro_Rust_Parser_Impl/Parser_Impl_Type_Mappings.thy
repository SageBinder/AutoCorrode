theory Parser_Impl_Type_Mappings
  imports
    Parser_Impl_AST
    Shallow_Micro_Rust.Semantic_Navigation
    Shallow_Micro_Rust.Tuple
    Shallow_Micro_Rust.Global_Store
  keywords "urust_type" :: thy_decl
begin

section\<open> Extensible Rust-to-HOL type mappings \<close>

text\<open>
Named Rust types, including lexical primitive spellings, acquire HOL meanings only through this
context-local registry. A mapping key may be qualified and may contain ordered generic
placeholders. The placeholders are mapping parameters rather than Rust lifetimes, and must be
exactly the free type variables of the checked HOL template.
\<close>

ML\<open>
signature URUST_TYPE_MAPPINGS =
sig
  type entry

  val resolve: Proof.context -> URust_AST.rust_type -> typ
  val resolve_signature:
    Proof.context -> URust_AST.rust_type list -> typ list
  val resolve_function_signature:
    Proof.context -> Input.source option ->
      URust_AST.rust_type list -> URust_AST.rust_type option -> typ
  val resolve_fields:
    Proof.context -> URust_AST.rust_type list ->
      {types: typ list, backend_parameters: (string * sort) list}
  val resolve_cast:
    Proof.context -> URust_AST.source_cast_target -> URust_AST.cast_target
  val declare_alias:
    {registration: (string * Position.T) option,
     item_name: string * Position.T,
     parameters: (string * Position.T) list,
     rhs: URust_AST.rust_type} ->
    local_theory -> local_theory
  val lookup: Proof.context -> string -> entry option
  val dump: Proof.context -> (string * entry) list

  val entry_template: entry -> typ
  val entry_arities: entry -> int list
  val entry_parameter_sorts: entry -> sort list
  val entry_backend_parameter_sorts: entry -> sort list
  val entry_declaration_position: entry -> Position.T
  val entry_origin: entry -> string
  val entry_identity: entry -> serial

  val preflight_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
    local_theory -> unit
  val register_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
    local_theory -> local_theory
  val preflight_generated_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, backend_parameters: (string * sort) list} ->
    local_theory -> unit
  val register_generated_scheme:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string,
     hol_type: typ, backend_parameters: (string * sort) list} ->
    local_theory -> local_theory
end

structure URust_Type_Mappings :> URUST_TYPE_MAPPINGS =
struct
  open URust_AST
  structure Navigation = Micro_Rust_Semantic_Navigation

  val mappingN = "micro_rust_type_mapping"

  datatype origin =
      Manual
    | Generated of string
    | Alias

  (* Rust identity is independent of HOL equality: i32/u32, pointer
     mutability, and an arbitrary mapping to a word remain distinct. Alias
     dependencies are expanded once, when declared. Mapped nodes retain
     the dependency scheme so locale morphisms also reach captured meaning. *)
  datatype meaning =
      Meaning_Parameter of int
    | Meaning_Primitive of rust_primitive_type
    | Meaning_Mapped of typ * sort list * sort list * meaning list
    | Meaning_Tuple of meaning list
    | Meaning_Pointer of raw_pointer_mutability * meaning
    | Meaning_HOL of typ

  type key =
    {base: string,
     segment_arities: int list,
     parameters: string list,
     parameter_positions: Position.T list}

  type entry =
    {segment_arities: int list,
     template: typ,
     parameter_sorts: sort list,
     backend_parameter_sorts: sort list,
     meaning: meaning,
     dependencies: string list,
     declaration_pos: Position.T,
     origin: origin,
     identity: serial}

  fun entry_template ({template, ...}: entry) = template
  fun entry_arities ({segment_arities, ...}: entry) = segment_arities
  fun entry_parameter_sorts ({parameter_sorts, ...}: entry) =
    parameter_sorts
  fun entry_backend_parameter_sorts
      ({backend_parameter_sorts, ...}: entry) =
    backend_parameter_sorts
  fun entry_declaration_position ({declaration_pos, ...}: entry) =
    declaration_pos
  fun entry_identity ({identity, ...}: entry) = identity

  fun origin_text Manual = "urust_type declaration"
    | origin_text (Generated hol_type_name) =
        "generated datatype " ^ quote hol_type_name
    | origin_text Alias = "urust_type_alias declaration"

  fun alias_origin Alias = true
    | alias_origin _ = false

  fun entry_origin ({origin, ...}: entry) = origin_text origin

  fun same_entry
      ({segment_arities = left_arities,
        template = left_template,
        parameter_sorts = left_sorts,
        backend_parameter_sorts = left_backend,
        meaning = left_meaning, origin = left_origin, ...}: entry,
       {segment_arities = right_arities,
        template = right_template,
        parameter_sorts = right_sorts,
        backend_parameter_sorts = right_backend,
        meaning = right_meaning, origin = right_origin, ...}: entry) =
    left_arities = right_arities andalso
    left_template = right_template andalso
    left_sorts = right_sorts andalso
    left_backend = right_backend andalso
    alias_origin left_origin = alias_origin right_origin andalso
    (not (alias_origin left_origin) orelse left_meaning = right_meaning)

  fun ordered_entries (left: entry, right: entry) =
    if #identity left <= #identity right then (left, right)
    else (right, left)

  fun conflict base reason (left: entry, right: entry) =
    let
      val (first, second) = ordered_entries (left, right)
    in
      error
        ("urust_type: conflicting active mappings for " ^ quote base ^
          " (" ^ reason ^ ")\n  " ^
          origin_text (#origin first) ^
          Position.here (#declaration_pos first) ^ "\n  " ^
          origin_text (#origin second) ^
          Position.here (#declaration_pos second))
    end

  fun join_entry base (left: entry, right: entry) =
    if same_entry (left, right)
    then #1 (ordered_entries (left, right))
    else if alias_origin (#origin left) <> alias_origin (#origin right)
    then conflict base "alias and direct/generated mapping collide" (left, right)
    else if #segment_arities left <> #segment_arities right orelse
        length (#parameter_sorts left) <> length (#parameter_sorts right)
    then conflict base "different generic arity" (left, right)
    else conflict base "different Rust meanings, HOL templates or parameter sorts"
      (left, right)

  structure Data = Generic_Data
  (
    type T = entry Symtab.table
    val empty = Symtab.empty
    fun merge (left, right) =
      Symtab.join join_entry (left, right)
  )

  fun lookup ctxt base =
    Symtab.lookup (Data.get (Context.Proof ctxt)) base

  fun dump ctxt =
    Symtab.dest (Data.get (Context.Proof ctxt))

  fun add_entry base entry =
    Data.map
      (fn table =>
        (case Symtab.lookup table base of
           NONE => Symtab.update (base, entry) table
         | SOME active =>
             Symtab.update
               (base, join_entry base (active, entry))
               table))

  fun mapping_error message pos =
    error ("urust_type: " ^ message ^ Position.here pos)

  fun ascii_letter character =
    (#"A" <= character andalso character <= #"Z") orelse
    (#"a" <= character andalso character <= #"z")

  fun identifier_start character =
    ascii_letter character orelse character = #"_"

  fun identifier_rest character =
    identifier_start character orelse Char.isDigit character orelse
    character = #"'"

  fun parse_mapping_key (raw, pos) source_symbols =
    let
      val input = raw
      val input_size = size input
      val symbols = Vector.fromList source_symbols
      val offset = Unsynchronized.ref 0

      fun fail detail =
        mapping_error
          ("malformed Rust type key " ^ quote raw ^ " (" ^ detail ^ ")")
          pos

      fun at_end () = !offset >= input_size
      fun current () =
        if at_end () then NONE else SOME (String.sub (input, !offset))
      fun advance () = offset := !offset + 1
      fun skip_blanks () =
        (case current () of
           SOME character =>
             if Char.isSpace character
             then (advance (); skip_blanks ())
             else ()
         | NONE => ())
      fun accept character =
        (skip_blanks ();
         case current () of
           SOME actual =>
             if actual = character
             then (advance (); true)
             else false
         | NONE => false)
      fun require character expected =
        if accept character then ()
        else fail ("expected " ^ expected)
      fun source_position start stop =
        if start < stop andalso stop <= Vector.length symbols
        then
          let
            val (_, start_pos) = Vector.sub (symbols, start)
            val (last_symbol, last_pos) =
              Vector.sub (symbols, stop - 1)
          in
            Position.range_position
              (Position.range
                (start_pos, Position.symbol last_symbol last_pos))
          end
        else Position.none
      fun accept_double_colon () =
        let
          val _ = skip_blanks ()
        in
          if !offset + 1 < input_size andalso
              String.sub (input, !offset) = #":" andalso
              String.sub (input, !offset + 1) = #":"
          then (offset := !offset + 2; true)
          else false
        end

      fun identifier description =
        let
          val _ = skip_blanks ()
          val start = !offset
          val _ =
            (case current () of
               SOME character =>
                 if identifier_start character
                 then advance ()
                 else fail ("expected " ^ description)
             | NONE => fail ("expected " ^ description))
          fun rest () =
            (case current () of
               SOME character =>
                 if identifier_rest character
                 then (advance (); rest ())
                 else ()
             | NONE => ())
          val _ = rest ()
        in String.substring (input, start, !offset - start) end

      fun placeholder () =
        let
          val start = !offset
          val _ = require #"'" "a mapping placeholder such as 'a"
          val parameter = "'" ^ identifier "a placeholder name"
        in (parameter, source_position start (!offset)) end

      fun placeholders () =
        let
          val first = placeholder ()
          fun more parameters =
            if accept #","
            then
              (skip_blanks ();
               if accept #">"
               then (rev parameters, true)
               else more (placeholder () :: parameters))
            else (rev parameters, false)
          val (parameters, closed) = more [first]
          val _ = if closed then () else require #">" "`>`"
        in parameters end

      fun segment () =
        let
          val name = identifier "a Rust path segment"
          val parameters =
            if accept #"<" then placeholders () else []
        in (name, parameters) end

      fun path segments =
        let
          val next = segment ()
          val segments' = next :: segments
        in
          if accept_double_colon ()
          then path segments'
          else rev segments'
        end

      val special =
        if Symbol.trim_blanks input = "()"
        then SOME ("()", [0], [])
        else if Symbol.trim_blanks input = "!"
        then SOME ("!", [0], [])
        else NONE
      val (base, arities, parameters) =
        (case special of
           SOME result => result
         | NONE =>
             let
               val segments = path []
               val _ =
                 (skip_blanks ();
                  if at_end () then ()
                  else fail "unexpected trailing input")
               val names = map fst segments
               val parameter_rows = map snd segments
             in
               (space_implode "::" names,
                map length parameter_rows,
                flat parameter_rows)
             end)
      val _ =
        if length parameters =
            length (distinct (op =) (map fst parameters))
        then ()
        else fail "mapping placeholders must be distinct"
    in
      {base = base,
       segment_arities = arities,
       parameters = map fst parameters,
       parameter_positions = map snd parameters}: key
    end

  fun parse_mapping_key_source source =
    parse_mapping_key
      (Input.source_content source)
      (Input.source_explode source)

  fun parse_mapping_key_text raw_position =
    parse_mapping_key raw_position []

  fun canonical_parameter index sort =
    TVar (("_urust_type", index), sort)

  fun canonical_backend_parameter index sort =
    TVar (("_urust_backend", index), sort)

  fun primitive_meaning base =
    get_first
      (fn primitive =>
        if rust_primitive_name primitive = base then SOME primitive else NONE)
      [DPT_U8, DPT_U16, DPT_U32, DPT_U64, DPT_U128, DPT_Usize,
       DPT_I8, DPT_I16, DPT_I32, DPT_I64, DPT_I128, DPT_Isize,
       DPT_Bool, DPT_Char, DPT_Str, DPT_Never, DPT_Unit]

  fun mapped_meaning base template parameter_sorts backend_sorts =
    (case primitive_meaning base of
       SOME primitive => Meaning_Primitive primitive
     | NONE =>
         Meaning_Mapped (template, parameter_sorts, backend_sorts,
           map_index (fn (index, _) => Meaning_Parameter index)
             parameter_sorts))

  fun morph_meaning phi =
    let
      fun morph (Meaning_Parameter index) = Meaning_Parameter index
        | morph (Meaning_Primitive primitive) = Meaning_Primitive primitive
        | morph (Meaning_Mapped (template, sorts, backend_sorts, arguments)) =
            Meaning_Mapped
              (Morphism.typ phi template, sorts, backend_sorts,
               map morph arguments)
        | morph (Meaning_Tuple types) = Meaning_Tuple (map morph types)
        | morph (Meaning_Pointer (mutability, typ)) =
            Meaning_Pointer (mutability, morph typ)
        | morph (Meaning_HOL typ) = Meaning_HOL (Morphism.typ phi typ)
    in morph end

  fun instantiate_meaning arguments =
    let
      fun instantiate (Meaning_Parameter index) = nth arguments index
        | instantiate (Meaning_Primitive primitive) =
            Meaning_Primitive primitive
        | instantiate (Meaning_Mapped (template, sorts, backend_sorts, types)) =
            Meaning_Mapped
              (template, sorts, backend_sorts, map instantiate types)
        | instantiate (Meaning_Tuple types) =
            Meaning_Tuple (map instantiate types)
        | instantiate (Meaning_Pointer (mutability, typ)) =
            Meaning_Pointer (mutability, instantiate typ)
        | instantiate (Meaning_HOL typ) = Meaning_HOL typ
    in instantiate end

  fun checked_template lthy
      ({parameters, ...}: key) source =
    let
      val pos = Input.pos_of source
      val typ =
        (case Exn.result
            (fn () =>
              Syntax.read_typ lthy (Syntax.implode_input source)) () of
           Exn.Res typ => typ
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else error (Runtime.exn_message exn ^ Position.here pos))
      val _ =
        if null (Term.add_tvarsT typ []) then ()
        else mapping_error
          "schematic type variables are not supported in HOL templates"
          pos
      val tfrees = Term.add_tfreesT typ []
      val tfree_names = map fst tfrees
      val missing =
        filter_out (member (op =) tfree_names) parameters
      val extra =
        filter_out (member (op =) parameters) tfree_names
      val _ =
        if null missing andalso null extra then ()
        else
          mapping_error
            ("mapping placeholders must correspond exactly to the HOL template's free type variables" ^
              (if null missing then ""
               else "; missing " ^ commas_quote missing) ^
              (if null extra then ""
               else "; undeclared " ^ commas_quote extra))
            pos
      fun parameter_sort name =
        (case AList.lookup (op =) tfrees name of
           SOME sort =>
             Sign.minimize_sort (Proof_Context.theory_of lthy) sort
         | NONE =>
             raise Fail
               "uRust type registry: validated template parameter is absent")
      val parameter_sorts = map parameter_sort parameters
      val canonical =
        map_index
          (fn (index, (name, sort)) =>
            (TFree (name, sort), canonical_parameter index sort))
          (parameters ~~ parameter_sorts)
      val normalized = Term.typ_subst_atomic canonical typ
    in
      (Proof_Context.cert_typ lthy normalized, parameter_sorts)
    end

  fun make_entry origin declaration_pos segment_arities template
      parameter_sorts backend_parameter_sorts meaning dependencies =
    {segment_arities = segment_arities,
     template = template,
     parameter_sorts = parameter_sorts,
     backend_parameter_sorts = backend_parameter_sorts,
     meaning = meaning,
     dependencies = dependencies,
     declaration_pos = declaration_pos,
     origin = origin,
     identity = serial ()}: entry

  fun morph_entry phi
      ({segment_arities, template, parameter_sorts, backend_parameter_sorts,
        meaning, dependencies, declaration_pos, origin, identity}: entry) =
    {segment_arities = segment_arities,
     template = Morphism.typ phi template,
     parameter_sorts = parameter_sorts,
     backend_parameter_sorts = backend_parameter_sorts,
     meaning = morph_meaning phi meaning,
     dependencies = dependencies,
     declaration_pos = declaration_pos,
     origin = origin,
     identity = identity}: entry

  datatype preflight =
      Existing of entry
    | Fresh of entry

  fun preflight ctxt base candidate =
    (case lookup ctxt base of
       NONE => Fresh candidate
     | SOME active =>
         if same_entry (active, candidate)
         then Existing active
         else
           (ignore (join_entry base (active, candidate));
            raise Fail
              "uRust type registry: conflicting join unexpectedly returned"))

  fun report_declaration ctxt base pos identity =
    (Navigation.defer_report ctxt pos
       (Position.make_entity_markup {def = true} identity mappingN
         (base, pos));
     Navigation.defer_report ctxt pos Markup.typing)

  fun install_new base (entry: entry) lthy =
    let
      val _ =
        report_declaration lthy base
          (#declaration_pos entry) (#identity entry)
    in
      Local_Theory.declaration
        {pervasive = false, syntax = true,
         pos = #declaration_pos entry}
        (fn phi => add_entry base (morph_entry phi entry))
        lthy
    end

  fun install_prepared base candidate lthy =
    (case preflight lthy base candidate of
       Existing _ => lthy
     | Fresh entry => install_new base entry lthy)

  fun report_parameters ctxt
      ({parameters, parameter_positions, ...}: key) =
    List.app
      (fn (parameter, pos) =>
        Navigation.defer_report ctxt pos Markup.tfree)
      (parameters ~~ parameter_positions)

  fun declare_mapping origin (key_source, source)
      lthy =
    let
      val key as {base, segment_arities, ...} =
        parse_mapping_key_source key_source
      val key_pos = Input.pos_of key_source
      val (template, parameter_sorts) =
        checked_template lthy key source
      val _ = report_parameters lthy key
      val candidate =
        make_entry origin key_pos segment_arities template
          parameter_sorts [] (mapped_meaning base template parameter_sorts []) []
    in install_prepared base candidate lthy end

  fun generated_candidate
      {rust_name, rust_pos, hol_type_name} =
    let
      val {base, segment_arities, parameters, ...} =
        parse_mapping_key_text (rust_name, rust_pos)
      val _ =
        if null parameters then ()
        else
          mapping_error
            "generated datatypes cannot declare generic mapping placeholders"
            rust_pos
    in
      (base,
       make_entry (Generated hol_type_name) rust_pos
         segment_arities (Type (hol_type_name, [])) [] []
         (mapped_meaning base (Type (hol_type_name, [])) [] []) [])
    end

  fun generated_scheme_candidate
      {rust_name, rust_pos, hol_type_name, hol_type, backend_parameters} =
    let
      val {base, segment_arities, parameters, ...} =
        parse_mapping_key_text (rust_name, rust_pos)
      val _ =
        if null parameters then ()
        else mapping_error
          "generated datatypes cannot declare generic mapping placeholders"
          rust_pos
      val _ =
        if null backend_parameters orelse length backend_parameters = 2 then ()
        else mapping_error
          "generated pointer datatypes require one address/global parameter pair"
          rust_pos
      val _ =
        if null (Term.add_tvarsT hol_type []) andalso
            length backend_parameters =
              length (distinct (op =) (map fst backend_parameters)) andalso
            eq_set (op =) (Term.add_tfreesT hol_type [], backend_parameters)
        then ()
        else mapping_error
          "generated type schemes must contain exactly their implicit backend parameters"
          rust_pos
      val backend_sorts = map snd backend_parameters
      val substitutions =
        map_index
          (fn (index, parameter as (_, sort)) =>
            (TFree parameter, canonical_backend_parameter index sort))
          backend_parameters
      val template = Term.typ_subst_atomic substitutions hol_type
    in
      (base,
       make_entry (Generated hol_type_name) rust_pos segment_arities
         template [] backend_sorts
         (mapped_meaning base template [] backend_sorts) [])
    end

  fun preflight_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
    in install_prepared base candidate lthy end

  fun preflight_generated_scheme specification lthy =
    let
      val (base, candidate) = generated_scheme_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_generated_scheme specification lthy =
    let
      val (base, candidate) = generated_scheme_candidate specification
    in install_prepared base candidate lthy end

  fun report_use ctxt base (entry: entry) positions primitive =
    let
      val _ =
        List.app
          (fn pos =>
            ((if primitive then ()
              else Navigation.defer_report ctxt pos Markup.keyword3);
             Navigation.defer_report ctxt pos Markup.typing))
          positions
      val terminal_pos =
        (case rev positions of
           pos :: _ => pos
         | [] => #declaration_pos entry)
    in
      Navigation.defer_report ctxt terminal_pos
        (Position.make_entity_markup {def = false}
          (#identity entry) mappingN
          (base, #declaration_pos entry))
    end

  datatype resolution_kind =
      Datatype_Fields
    | Function_Signature
    | Alias_Declaration
    | Cast_Target

  fun command_label Datatype_Fields = "urust_datatype"
    | command_label Function_Signature = "urust_fn"
    | command_label Alias_Declaration = "urust_type_alias"
    | command_label Cast_Target = "urust_expr"

  fun type_context Datatype_Fields = "datatype fields"
    | type_context Function_Signature = "function signatures"
    | type_context Alias_Declaration = "type aliases"
    | type_context Cast_Target = "cast targets"

  fun positioned_result kind positions action =
    (case Exn.result action () of
       Exn.Res result => result
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           error
             (command_label kind ^ ": " ^ Runtime.exn_message exn ^
               Position.here_list positions))

  fun no_type_variables what pos typ =
    if null (Term.add_tfreesT typ []) andalso
        null (Term.add_tvarsT typ [])
    then typ
    else
      error
        ("urust_datatype: type variables are not supported in " ^
          what ^ Position.here pos)

  fun read_hol_escape ctxt source =
    let
      val pos = Input.pos_of source
      val typ =
        positioned_result Datatype_Fields [pos]
          (fn () =>
            Syntax.read_typ ctxt (Syntax.implode_input source))
    in no_type_variables "datatype fields" pos typ end

  fun unknown_type kind base pos =
    error
      (command_label kind ^ ": unknown Rust type " ^ quote base ^
        "; declare it with urust_type or use \<tau>\<open>...\<close>" ^
        " (Rust synonyms may also be declared with urust_type_alias)" ^
        Position.here pos)

  fun arity_error kind base expected actual pos =
    let
      fun arities values =
        values |> map string_of_int |> commas |> enclose "[" "]"
    in
      error
        (command_label kind ^ ": Rust type " ^ quote base ^
          " has generic arities " ^ arities actual ^
          ", but the active urust_type mapping expects " ^
          arities expected ^ Position.here pos)
    end

  fun unsupported kind description pos =
    error
      (command_label kind ^ ": " ^ description ^
        " is not supported in " ^ type_context kind ^
        "; use \<tau>\<open>...\<close>" ^
        Position.here pos)

  fun sort_error kind ctxt base argument sort pos =
    error
      (command_label kind ^ ": generic argument type " ^
        quote (Syntax.string_of_typ ctxt argument) ^
        " does not satisfy sort " ^
        quote (Syntax.string_of_sort ctxt sort) ^
        " required by the urust_type mapping for " ^
        quote base ^ Position.here pos)

  fun path_information segments =
    let
      fun one
          (Rust_Type_Path_Segment
            (name, pos, arguments, _)) =
        (name, pos, the_default [] arguments)
      val rows = map one segments
    in
      {base = space_implode "::" (map #1 rows),
       positions = map #2 rows,
       arities = map (length o #3) rows,
       arguments = maps #3 rows}
    end

  fun numeric_argument_position
      (Integer_Literal (_, layout, _)) =
    source_span layout

  type resolved = {typ: typ, meaning: meaning}

  (* One inference environment and one lazy backend pair belong to a complete
     signature or field batch. Canonical registry slots are never reused as
     flexible variables by two independent resolutions. *)
  fun inference_state kind ctxt initial_types =
    let
      val instance_name = "_urust_inference_" ^ string_of_int (serial ())
      val unification: (Type.tyenv * int) Unsynchronized.ref =
        Unsynchronized.ref
          (Vartab.empty,
           fold Term.maxidx_typ initial_types (Variable.maxidx_of ctxt))
      val backend_slots: typ list option Unsynchronized.ref =
        Unsynchronized.ref NONE

      fun fresh sort =
        let
          val (environment, index) = !unification
          val next = index + 1
          val _ = unification := (environment, next)
        in Type_Infer.param next (instance_name, sort) end

      fun normalize typ =
        Envir.norm_type (#1 (!unification)) typ

      fun check_sort base argument sort pos =
        let
          val constraint = fresh sort
          val environment =
            Type.unify (Proof_Context.tsig_of ctxt)
              (argument, constraint) (!unification)
            handle Type.TUNIFY =>
              sort_error kind ctxt base (normalize argument) sort pos
        in unification := environment end

      fun unify label pos (expected, actual) =
        let
          val environment =
            Type.unify (Proof_Context.tsig_of ctxt)
              (expected, actual) (!unification)
            handle Type.TUNIFY =>
              error
                (command_label kind ^ ": " ^ label ^
                  " conflicts with the semantic type annotation\n" ^
                  "annotation: " ^ Syntax.string_of_typ ctxt (normalize expected) ^
                  "\nRust signature: " ^ Syntax.string_of_typ ctxt (normalize actual) ^
                  Position.here pos)
        in unification := environment end

      fun backend sorts =
        if null sorts then []
        else
          let
            val _ =
              if length sorts = 2 then ()
              else raise Fail
                "uRust type registry: invalid backend parameter scheme"
            val slots =
              (case !backend_slots of
                 SOME slots => slots
               | NONE =>
                   let
                     val slots = map (fn _ => fresh []) sorts
                     val _ = backend_slots := SOME slots
                   in slots end)
            val _ =
              List.app
                (fn (slot, sort) =>
                  check_sort "implicit pointer backend" slot sort Position.none)
                (slots ~~ sorts)
          in map normalize slots end
    in
      {fresh = fresh, normalize = normalize, check_sort = check_sort, unify = unify,
       backend = backend,
       backend_slots = fn () => the_default [] (!backend_slots)}
    end

  fun resolve_values kind ctxt read_escape check_sort normalize backend
      parameter dependency rust_types =
    let
      fun resolve_nominal base positions arities arguments pos primitive =
        (case parameter base arities pos of
           SOME value => value
         | NONE =>
             let
               val active = lookup ctxt base
               val _ = dependency base active pos
               val entry =
                 (case active of
                    SOME entry => entry
                  | NONE => unknown_type kind base pos)
               val expected_arities = #segment_arities entry
               val _ =
                 if expected_arities = arities then ()
                 else arity_error kind base expected_arities arities pos
               fun resolve_argument (Rust_Type_Argument argument) =
                     (resolve_type argument, rust_type_position argument)
                 | resolve_argument (Rust_Numeric_Argument integer) =
                     unsupported kind "numeric generic arguments"
                       (numeric_argument_position integer)
               val resolved_arguments = map resolve_argument arguments
               val parameter_sorts = #parameter_sorts entry
               val backend_sorts = #backend_parameter_sorts entry
               val _ =
                 if length resolved_arguments = length parameter_sorts then ()
                 else raise Fail
                   "uRust type registry: generic arity metadata is inconsistent"
               val _ =
                 List.app
                   (fn (({typ, ...}: resolved, argument_pos), sort) =>
                     check_sort base typ sort argument_pos)
                   (resolved_arguments ~~ parameter_sorts)
               val argument_types =
                 map (normalize o #typ o fst) resolved_arguments
               val backend_types = backend backend_sorts
               val substitutions =
                 map_index
                   (fn (index, (sort, argument)) =>
                     ((("_urust_type", index), sort), argument))
                   (parameter_sorts ~~ argument_types) @
                 map_index
                   (fn (index, (sort, argument)) =>
                     ((("_urust_backend", index), sort), argument))
                   (backend_sorts ~~ backend_types)
               val result =
                 Term_Subst.instantiateT
                   (TVars.make substitutions) (#template entry)
                 |> normalize
                 |> Proof_Context.cert_typ ctxt
               val terminal_pos =
                 (case rev positions of
                    terminal :: _ => terminal
                  | [] => pos)
               val _ =
                 (case result of
                    Type (name, _) =>
                      Navigation.defer_type ctxt terminal_pos name
                  | _ => ())
               val _ = report_use ctxt base entry positions primitive
             in
               {typ = result,
                meaning = instantiate_meaning
                  (map (#meaning o fst) resolved_arguments) (#meaning entry)}
             end)

      and resolve_type
          (Primitive_Type (primitive, pos)) =
            resolve_nominal
              (rust_primitive_name primitive) [pos] [0] [] pos true
        | resolve_type (Path_Type (segments, layout)) =
            let
              val {base, positions, arities, arguments} =
                path_information segments
            in
              resolve_nominal base positions arities arguments
                (source_span layout) false
            end
        | resolve_type (Tuple_Type (types, layout)) =
            if length types < 2
            then unsupported kind "singleton tuple types" (source_span layout)
            else
              let val resolved = map resolve_type types in
                {typ =
                   fold_rev
                     (fn typ => fn rest => HOLogic.mk_prodT (typ, rest))
                     (map #typ resolved) \<^typ>\<open>tnil\<close>,
                 meaning = Meaning_Tuple (map #meaning resolved)}
              end
        | resolve_type (Group_Type (typ, _)) =
            resolve_type typ
        | resolve_type (Reference_Type (_, _, layout)) =
            unsupported kind "Rust reference types" (source_span layout)
        | resolve_type (Raw_Pointer_Type (mutability, target, _)) =
            let
              val target_type = resolve_type target
              val [address, global] =
                backend [\<^sort>\<open>type\<close>, \<^sort>\<open>type\<close>]
              val typ =
                Term.typ_subst_atomic
                  [(\<^typ>\<open>'urust_address\<close>, address),
                   (\<^typ>\<open>'urust_global\<close>, global),
                   (\<^typ>\<open>'urust_value\<close>, #typ target_type)]
                  \<^typ>\<open>('urust_address, 'urust_global, 'urust_value) Global_Store.ref\<close>
                |> Proof_Context.cert_typ ctxt
            in
              {typ = typ,
               meaning = Meaning_Pointer (mutability, #meaning target_type)}
            end
        | resolve_type (Slice_Type (_, layout)) =
            unsupported kind "Rust slice types" (source_span layout)
        | resolve_type (Array_Type (_, _, layout)) =
            unsupported kind "Rust array types" (source_span layout)
        | resolve_type (HOL_Type_Source source) =
            let val typ = read_escape source in
              {typ = typ, meaning = Meaning_HOL typ}
            end
    in map resolve_type rust_types end

  fun no_parameter _ _ _ = NONE
  fun no_dependency _ _ _ = ()

  fun finish_backend ctxt normalize slots types =
    let
      val names =
        Name.variants (Variable.names_of ctxt)
          ["'urust_address", "'urust_global"]
      fun parameter (typ as TVar (_, sort)) =
            (typ, sort)
        | parameter _ =
            raise Fail
              "uRust type registry: backend parameter became a concrete type"
      val normalized = map (parameter o normalize) slots
      val parameters = take (length normalized) names ~~ map snd normalized
      val substitutions =
        map2 (fn (typ, _) => fn parameter => (typ, TFree parameter))
          normalized parameters
      val result =
        map
          (normalize #>
            Term.typ_subst_atomic substitutions #>
            Proof_Context.cert_typ ctxt)
          types
    in
      {types = result, backend_parameters = parameters}
    end

  fun resolve_fields ctxt rust_types =
    let
      val {normalize, check_sort, backend, backend_slots, ...} =
        inference_state Datatype_Fields ctxt []
      val resolved =
        resolve_values Datatype_Fields ctxt (read_hol_escape ctxt)
          check_sort normalize backend no_parameter no_dependency rust_types
    in finish_backend ctxt normalize (backend_slots ()) (map #typ resolved) end

  fun resolve ctxt rust_type =
    the_single (#types (resolve_fields ctxt [rust_type]))

  fun hol_sources (HOL_Type_Source source) = [source]
    | hol_sources (Path_Type (segments, _)) =
        let
          fun argument (Rust_Type_Argument typ) = hol_sources typ
            | argument (Rust_Numeric_Argument _) = []
          fun segment (Rust_Type_Path_Segment (_, _, arguments, _)) =
            maps argument (the_default [] arguments)
        in maps segment segments end
    | hol_sources (Tuple_Type (types, _)) = maps hol_sources types
    | hol_sources (Group_Type (typ, _)) = hol_sources typ
    | hol_sources (Reference_Type (_, typ, _)) = hol_sources typ
    | hol_sources (Raw_Pointer_Type (_, typ, _)) = hol_sources typ
    | hol_sources (Slice_Type (typ, _)) = hol_sources typ
    | hol_sources (Array_Type (typ, _, _)) = hol_sources typ
    | hol_sources (Primitive_Type _) = []

  fun resolve_signature_with ctxt rust_types constrain =
    let
      val sources = maps hol_sources rust_types
      fun parse source =
        positioned_result Function_Signature [Input.pos_of source]
          (fn () =>
            Syntax.parse_typ ctxt (Syntax.implode_input source))
      val parsed = map parse sources
      val checked =
        positioned_result Function_Signature (map Input.pos_of sources)
          (fn () => Syntax.check_typs ctxt parsed)

      (* Keep sort inference shared across the whole signature. Only fresh
         signature variables are flexible; ambient variables remain rigid. *)
      val {fresh, normalize, check_sort, unify, backend, ...} =
        inference_state Function_Signature ctxt checked
      val named_parameters: typ Symtab.table Unsynchronized.ref =
        Unsynchronized.ref Symtab.empty

      fun import_typ (typ as Type (name, types)) =
            if typ = dummyT then fresh []
            else Type (name, map import_typ types)
        | import_typ (TFree ("'_dummy_", sort)) = fresh sort
        | import_typ (typ as TFree (name, sort)) =
            if is_some (Variable.def_sort ctxt (name, ~1)) then typ
            else
              (case Symtab.lookup (!named_parameters) name of
                 SOME parameter => parameter
               | NONE =>
                   let
                     val parameter = fresh sort
                     val _ =
                       named_parameters :=
                         Symtab.update (name, parameter) (!named_parameters)
                   in parameter end)
        | import_typ (typ as TVar _) = typ

      val pending = Unsynchronized.ref (map import_typ checked)

      fun read_escape _ =
        (case !pending of
           typ :: rest => (pending := rest; typ)
         | [] =>
             raise Fail
               "uRust type registry: signature HOL escape is absent")

      fun finish types =
        let
          fun named (name, parameter) =
            (case normalize parameter of
               TVar (variable, sort) =>
                 SOME ((variable, sort), TFree (name, sort))
             | _ => NONE)
          (* Several authored names may unify; restore one name per resulting variable.
             A name specialized to a concrete type needs no restoration. *)
          val names =
            TVars.make (map_filter named (Symtab.dest (!named_parameters)))
          fun inference_parameter (typ as TVar ((name, index), sort)) =
                if Type_Infer.is_param (name, index) then typ
                else Type_Infer.param index (name, sort)
            | inference_parameter typ = typ
        in
          map
            (normalize #>
              Term_Subst.instantiateT names #>
              Term.map_atyps inference_parameter #>
              Proof_Context.cert_typ ctxt)
            types
        end

      val resolved =
        resolve_values Function_Signature ctxt read_escape check_sort normalize
          backend no_parameter no_dependency rust_types
      val _ =
        if null (!pending) then ()
        else
          raise Fail
            "uRust type registry: unconsumed signature HOL escape"
    in finish (constrain normalize unify (map #typ resolved)) end

  fun resolve_signature ctxt rust_types =
    resolve_signature_with ctxt rust_types (fn _ => fn _ => I)

  (* The outer HOL declaration and Rust escapes are parsed/checked/imported in the same
     batch. Unify before restoring named variables: ambient locale variables stay rigid,
     fresh signature variables can acquire sorts or concrete types, and every _ is fresh. *)
  fun resolve_function_signature ctxt declared_type parameters result =
    let
      val types =
        map HOL_Type_Source (the_list declared_type) @ parameters @ the_list result
      fun constrain normalize unify resolved =
        let
          val (outer, rust_signature) = chop (length (the_list declared_type)) resolved
          val (parameter_types, result_types) = chop (length parameters) rust_signature
          val result_type =
            (case result_types of
               [typ] => typ
             | [] => dummyT
             | _ => raise Fail "uRust type registry: signature result count mismatch")
          val inferred =
            parameter_types --->
              Type (\<^type_name>\<open>function_body\<close>,
                [dummyT, result_type, dummyT, dummyT, dummyT])
        in
          (case (declared_type, outer) of
             (NONE, []) => [inferred]
           | (SOME source, [complete_type]) =>
               let
                 val (outer_parameters, terminal) = Term.strip_type (normalize complete_type)
                 val value_type =
                   (case terminal of
                      Type (name, [_, value, _, _, _]) =>
                        if name = \<^type_name>\<open>function_body\<close> then value
                        else error
                          ("urust_fn: semantic type must end in function_body" ^
                            Position.here (Input.pos_of source))
                    | _ => error
                        ("urust_fn: semantic type must end in function_body" ^
                          Position.here (Input.pos_of source)))
                 val _ =
                   if length outer_parameters = length parameters then ()
                   else error
                     ("urust_fn: semantic type expects " ^
                       string_of_int (length outer_parameters) ^
                       " parameters, but the Rust signature has " ^
                       string_of_int (length parameters) ^
                       Position.here (Input.pos_of source))
                 val _ =
                   List.app
                     (fn ((expected, actual), parameter) =>
                       unify "parameter type" (rust_type_position parameter)
                         (expected, actual))
                     ((outer_parameters ~~ parameter_types) ~~ parameters)
                 val _ =
                   (case result of
                      SOME typ =>
                        unify "return type" (rust_type_position typ) (value_type, result_type)
                    | NONE => ())
               in [normalize complete_type] end
           | _ => raise Fail "uRust type registry: outer signature count mismatch")
        end
    in the_single (resolve_signature_with ctxt types constrain) end

  fun alias_error message pos =
    error ("urust_type_alias: " ^ message ^ Position.here pos)

  fun split_alias_path raw =
    let
      fun split input =
        let val (segment, rest) = Substring.position "::" input in
          if Substring.isEmpty rest then [Substring.string segment]
          else Substring.string segment :: split (Substring.triml 2 rest)
        end
    in split (Substring.full raw) end

  val alias_reserved_segments =
    ["true", "false", "as", "let", "const", "return", "if", "else",
     "fuel", "while", "loop", "for", "in", "unsafe", "match",
     "match_switch", "match_case", "mut", "type", "struct", "enum", "fn",
     "async", "await", "break", "continue", "crate", "dyn", "extern",
     "impl", "mod", "move", "pub", "ref", "self", "Self", "static",
     "super", "trait", "use", "where"] @
    map rust_primitive_name
      [DPT_U8, DPT_U16, DPT_U32, DPT_U64, DPT_U128, DPT_Usize,
       DPT_I8, DPT_I16, DPT_I32, DPT_I64, DPT_I128, DPT_Isize,
       DPT_Bool, DPT_Char, DPT_Str, DPT_Never, DPT_Unit]

  fun declare_alias
      {registration, item_name = (item_name, declaration_pos), parameters, rhs}
      lthy =
    let
      val (raw, registration_pos) =
        the_default (item_name, declaration_pos) registration
      val {base, segment_arities, parameters = key_parameters, ...} =
        (case Exn.result
            (fn () => parse_mapping_key_text (raw, Position.none)) () of
           Exn.Res key => key
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else alias_error
               ("invalid alias path " ^ quote raw ^ ": " ^ Runtime.exn_message exn)
               registration_pos)
      val _ =
        if null key_parameters andalso base <> "()" andalso base <> "!" then ()
        else alias_error
          "registration paths cannot contain generic arguments or primitive unit/never spellings"
          registration_pos
      val segments = split_alias_path base
      val _ =
        (case find_first (member (op =) alias_reserved_segments) segments of
           NONE => ()
         | SOME segment =>
             alias_error
               ("invalid alias path " ^ quote raw ^ ": reserved segment " ^
                 quote segment ^ " cannot occur in an alias path")
               registration_pos)
      val _ =
        if List.last segments = item_name then ()
        else error
          ("urust_type_alias: registration path terminal " ^
            quote (List.last segments) ^ " must match item name " ^
            quote item_name ^ Position.here_list [registration_pos, declaration_pos])
      val parameter_names = map fst parameters
      val _ =
        (case duplicates (op =) parameter_names of
           [] => ()
         | duplicate :: _ =>
             let
               val positions =
                 parameters |> filter (fn (name, _) => name = duplicate) |> map snd
             in error
               ("urust_type_alias: duplicate type parameter " ^ quote duplicate ^
                 Position.here_list positions)
             end)
      val {fresh, normalize, check_sort, backend, backend_slots, ...} =
        inference_state Alias_Declaration lthy []
      val base_sort = the_default [] (Object_Logic.get_base_sort lthy)
      val parameter_types = map (fn _ => fresh base_sort) parameters
      val parameter_table =
        Symtab.make
          (map_index
            (fn (index, ((name, _), typ)) =>
              (name, {typ = typ, meaning = Meaning_Parameter index}))
            (parameters ~~ parameter_types))
      val used_parameters = Unsynchronized.ref ([]: string list)
      val dependencies = Unsynchronized.ref ([]: string list)

      fun parameter name arities pos =
        (case Symtab.lookup parameter_table name of
           NONE => NONE
         | SOME value =>
             let
               val _ =
                 if arities = [0] then ()
                 else alias_error
                   ("type parameter " ^ quote name ^ " cannot take generic arguments")
                   pos
               val _ = used_parameters := insert (op =) name (!used_parameters)
               val _ = Navigation.defer_report lthy pos Markup.tfree
             in SOME value end)

      fun dependency name active pos =
        let
          val inherited =
            (case active of SOME (entry: entry) => #dependencies entry | NONE => [])
          val _ =
            if name = base orelse member (op =) inherited base then
              alias_error
                ("recursive alias dependency " ^ quote name ^ " reaches " ^ quote base)
                pos
            else ()
          val _ =
            dependencies :=
              fold (insert (op =)) (name :: inherited) (!dependencies)
        in () end

      fun read_escape source =
        let
          val pos = Input.pos_of source
          val typ =
            positioned_result Alias_Declaration [pos]
              (fn () => Syntax.read_typ lthy (Syntax.implode_input source))
          val _ =
            if null (Term.add_tfreesT typ []) andalso
                null (Term.add_tvarsT typ []) then ()
            else alias_error
              "unrelated HOL type variables are not supported in aliases; use Rust type parameters"
              pos
        in typ end

      val result =
        the_single
          (resolve_values Alias_Declaration lthy read_escape
            check_sort normalize backend parameter dependency [rhs])
      val unused = filter_out (member (op =) (!used_parameters)) parameter_names
      val _ =
        if null unused then ()
        else alias_error
          ("unused type parameters " ^ commas_quote unused)
          (the_default declaration_pos
            (AList.lookup (op =) parameters (hd unused)))
      fun normalized_parameter typ =
        (case normalize typ of
           parameter as TVar (_, sort) =>
             (parameter, Sign.minimize_sort (Proof_Context.theory_of lthy) sort)
         | _ => raise Fail
             "uRust type registry: alias parameter became a concrete type")
      val normalized_parameters = map normalized_parameter parameter_types
      val normalized_backend =
        map normalized_parameter (backend_slots ())
      val parameter_sorts = map snd normalized_parameters
      val backend_sorts = map snd normalized_backend
      val substitutions =
        map_index
          (fn (index, (parameter, sort)) =>
            (parameter, canonical_parameter index sort))
          normalized_parameters @
        map_index
          (fn (index, (parameter, sort)) =>
            (parameter, canonical_backend_parameter index sort))
          normalized_backend
      val template =
        normalize (#typ result)
        |> Term.typ_subst_atomic substitutions
        |> Proof_Context.cert_typ lthy
      val expected_variables =
        map_index (fn (index, sort) => canonical_parameter index sort)
          parameter_sorts @
        map_index (fn (index, sort) => canonical_backend_parameter index sort)
          backend_sorts
      val _ =
        if null (Term.add_tfreesT template []) andalso
            forall
              (fn variable => member (op =) expected_variables (TVar variable))
              (Term.add_tvarsT template [])
        then ()
        else raise Fail
          "uRust type registry: alias template contains an uncaptured type variable"
      val arities =
        take (length segment_arities - 1) segment_arities @
          [length parameters]
      val candidate =
        make_entry Alias declaration_pos arities template
          parameter_sorts backend_sorts (#meaning result) (!dependencies)
      val prepared = preflight lthy base candidate
      val _ =
        List.app
          (fn (_, pos) => Navigation.defer_report lthy pos Markup.tfree)
          parameters
    in
      (case prepared of
         Existing _ => lthy
       | Fresh entry => install_new base entry lthy)
    end

  fun cast_target (Meaning_Primitive DPT_U8) = SOME (CT_Unsigned UT_U8)
    | cast_target (Meaning_Primitive DPT_U16) = SOME (CT_Unsigned UT_U16)
    | cast_target (Meaning_Primitive DPT_U32) = SOME (CT_Unsigned UT_U32)
    | cast_target (Meaning_Primitive DPT_U64) = SOME (CT_Unsigned UT_U64)
    | cast_target (Meaning_Primitive DPT_Usize) = SOME (CT_Unsigned UT_Usize)
    | cast_target (Meaning_Primitive DPT_I32) = SOME (CT_Signed ST_I32)
    | cast_target (Meaning_Primitive DPT_I64) = SOME (CT_Signed ST_I64)
    | cast_target (Meaning_Pointer (mutability, target)) =
        (case cast_target target of
           SOME (CT_Unsigned width) => SOME (CT_RawPointer (mutability, width))
         | _ => NONE)
    | cast_target _ = NONE

  fun resolve_cast _ (SCT_Primitive (target, _)) = target
    | resolve_cast ctxt source =
        let
          val rust_type = source_cast_target_rust_type source
          val {normalize, check_sort, backend, ...} =
            inference_state Cast_Target ctxt []
          fun read_escape source =
            unsupported Cast_Target "HOL type escapes" (Input.pos_of source)
          val result =
            the_single
              (resolve_values Cast_Target ctxt read_escape check_sort normalize
                backend no_parameter no_dependency [rust_type])
        in
          (case cast_target (#meaning result) of
             SOME target => target
           | NONE =>
               error
                 ("urust_expr: expanded Rust type has no supported cast operation" ^
                   Position.here (rust_type_position rust_type)))
        end

  fun declare_manual payload =
    declare_mapping Manual payload

  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>urust_type\<close>
      "declare a context-local Rust-to-HOL type mapping"
      ((Parse.token Parse.string --| \<^keyword>\<open>=\<close>) --
        Parse.embedded_input >>
          (fn (token, source) =>
            declare_manual (Token.input_of token, source)))
end
\<close>

end
