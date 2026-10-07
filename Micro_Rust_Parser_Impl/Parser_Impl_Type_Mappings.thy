theory Parser_Impl_Type_Mappings
  imports
    Parser_Impl_AST
    Shallow_Micro_Rust.Tuple
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
  val lookup: Proof.context -> string -> entry option
  val dump: Proof.context -> (string * entry) list

  val entry_template: entry -> typ
  val entry_arities: entry -> int list
  val entry_parameter_sorts: entry -> sort list
  val entry_declaration_position: entry -> Position.T
  val entry_origin: entry -> string
  val entry_identity: entry -> serial

  val preflight_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
    local_theory -> unit
  val register_generated:
    {rust_name: string, rust_pos: Position.T, hol_type_name: string} ->
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

  type key =
    {base: string,
     segment_arities: int list,
     parameters: string list,
     parameter_positions: Position.T list}

  type entry =
    {segment_arities: int list,
     template: typ,
     parameter_sorts: sort list,
     declaration_pos: Position.T,
     origin: origin,
     identity: serial}

  fun entry_template ({template, ...}: entry) = template
  fun entry_arities ({segment_arities, ...}: entry) = segment_arities
  fun entry_parameter_sorts ({parameter_sorts, ...}: entry) =
    parameter_sorts
  fun entry_declaration_position ({declaration_pos, ...}: entry) =
    declaration_pos
  fun entry_identity ({identity, ...}: entry) = identity

  fun origin_text Manual = "urust_type declaration"
    | origin_text (Generated hol_type_name) =
        "generated datatype " ^ quote hol_type_name

  fun entry_origin ({origin, ...}: entry) = origin_text origin

  fun same_entry
      ({segment_arities = left_arities,
        template = left_template,
        parameter_sorts = left_sorts, ...}: entry,
       {segment_arities = right_arities,
        template = right_template,
        parameter_sorts = right_sorts, ...}: entry) =
    left_arities = right_arities andalso
    left_template = right_template andalso
    left_sorts = right_sorts

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
    else if #segment_arities left <> #segment_arities right orelse
        length (#parameter_sorts left) <> length (#parameter_sorts right)
    then conflict base "different generic arity" (left, right)
    else conflict base "different HOL templates or parameter sorts"
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
      parameter_sorts =
    {segment_arities = segment_arities,
     template = template,
     parameter_sorts = parameter_sorts,
     declaration_pos = declaration_pos,
     origin = origin,
     identity = serial ()}: entry

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
        (fn _ => add_entry base entry)
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
          parameter_sorts
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
         segment_arities (Type (hol_type_name, [])) [])
    end

  fun preflight_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
    in ignore (preflight lthy base candidate) end

  fun register_generated specification lthy =
    let
      val (base, candidate) = generated_candidate specification
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

  fun command_label Datatype_Fields = "urust_datatype"
    | command_label Function_Signature = "urust_fn"

  fun type_context Datatype_Fields = "datatype fields"
    | type_context Function_Signature = "function signatures"

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

  fun resolve_types kind ctxt read_escape check_sort normalize rust_types =
    let
      fun resolve_nominal base positions arities arguments pos primitive =
        let
          val entry =
            (case lookup ctxt base of
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
          val _ =
            if length resolved_arguments = length parameter_sorts then ()
            else
              raise Fail
                "uRust type registry: generic arity metadata is inconsistent"
          val _ =
            List.app
              (fn ((argument, argument_pos), sort) =>
                check_sort base argument sort argument_pos)
              (resolved_arguments ~~ parameter_sorts)
          val argument_types = map (normalize o fst) resolved_arguments
          val substitutions =
            map_index
              (fn (index, (sort, argument)) =>
                ((("_urust_type", index), sort), argument))
              (parameter_sorts ~~ argument_types)
          val result =
            Term_Subst.instantiateT
              (TVars.make substitutions) (#template entry)
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
        in result end

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
              fold_rev
                (fn typ => fn rest =>
                  HOLogic.mk_prodT (typ, rest))
                (map resolve_type types) \<^typ>\<open>tnil\<close>
        | resolve_type (Group_Type (typ, _)) =
            resolve_type typ
        | resolve_type (Reference_Type (_, _, layout)) =
            unsupported kind "Rust reference types" (source_span layout)
        | resolve_type (Raw_Pointer_Type (_, _, layout)) =
            unsupported kind "Rust raw pointer types" (source_span layout)
        | resolve_type (Slice_Type (_, layout)) =
            unsupported kind "Rust slice types" (source_span layout)
        | resolve_type (Array_Type (_, _, layout)) =
            unsupported kind "Rust array types" (source_span layout)
        | resolve_type (HOL_Type_Source source) =
            read_escape source
    in map resolve_type rust_types end

  fun resolve ctxt rust_type =
    let
      fun check_sort base argument sort pos =
        if Sign.of_sort (Proof_Context.theory_of ctxt) (argument, sort)
        then ()
        else sort_error Datatype_Fields ctxt base argument sort pos
    in
      singleton
        (resolve_types Datatype_Fields ctxt
          (read_hol_escape ctxt) check_sort I) rust_type
    end

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

  fun resolve_signature ctxt rust_types =
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
      val unification: (Type.tyenv * int) Unsynchronized.ref =
        Unsynchronized.ref
          (Vartab.empty,
           fold Term.maxidx_typ checked (Variable.maxidx_of ctxt))
      val named_parameters: typ Symtab.table Unsynchronized.ref =
        Unsynchronized.ref Symtab.empty

      fun fresh sort =
        let
          val (environment, index) = !unification
          val next = index + 1
          val _ = unification := (environment, next)
        in Type_Infer.mk_param next sort end

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

      fun normalize typ =
        Envir.norm_type (#1 (!unification)) typ

      fun finish types =
        let
          fun named (name, parameter) =
            (case normalize parameter of
               TVar (variable, sort) =>
                 ((variable, sort), TFree (name, sort))
             | _ =>
                 raise Fail
                   "uRust type registry: signature parameter is not a variable")
          val names = TVars.make (map named (Symtab.dest (!named_parameters)))
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

      fun check_sort base argument sort pos =
        let
          val constraint = fresh sort
          val environment =
            Type.unify (Proof_Context.tsig_of ctxt)
              (argument, constraint) (!unification)
            handle Type.TUNIFY =>
              sort_error Function_Signature ctxt base
                (singleton finish argument) sort pos
        in unification := environment end

      val resolved =
        resolve_types Function_Signature ctxt read_escape check_sort normalize
          rust_types
      val _ =
        if null (!pending) then ()
        else
          raise Fail
            "uRust type registry: unconsumed signature HOL escape"
    in finish resolved end

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
