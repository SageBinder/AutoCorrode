(* ML audits for trait mappings and generic function items.
   The readable examples are in Parser_Generics_Examples. *)

theory Parser_Generics_ML_Tests
  imports
    Parser_Generics_Examples
    Parser_Test_Fixtures_Left
    Parser_Test_Fixtures_Right
    Micro_Rust_Parser_Impl.Parser_Impl_Chunk
begin

chapter\<open> Trait mappings \<close>

declare [[urust_verbosity = 0]]

ML\<open>
structure Parser_Trait_Test =
struct
  structure Traits = URust_Trait_Mappings
  structure Navigation = Micro_Rust_Semantic_Navigation
  structure Reports = URust_Report_Transaction

  fun require message condition =
    if condition then () else error ("trait mapping regression: " ^ message)

  fun start label = Position.make0 1 1 0 "" label label
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun source label text = Parser_Lex_Util.positioned_content_source text (start label)
  fun initial thy = Toplevel.make_state (SOME thy)
  fun run_from state label text =
    let
      val thy = Toplevel.theory_of state
      val commands = Outer_Syntax.parse_text thy (K thy) (start label) text
    in fold (Toplevel.command_exception true) commands state end
  fun run thy label text = run_from (initial thy) label text
  fun context state =
    if Toplevel.is_toplevel state then Proof_Context.init_global (Toplevel.theory_of state)
    else Toplevel.context_of state
  fun mapping ctxt name = the (Traits.lookup ctxt name)
  fun term ctxt entry name = #term (the (Traits.associated_constant ctxt entry name))

  fun neighboring_snapshot (bindings: URust_Import_Scope.binding list) ctxt =
    (URust_Type_Mappings.dump ctxt |> map (fn (key, entry) =>
       (key, URust_Type_Mappings.entry_template entry,
        URust_Type_Mappings.entry_arities entry,
        URust_Type_Mappings.entry_parameter_sorts entry,
        URust_Type_Mappings.entry_backend_parameter_sorts entry,
        URust_Type_Mappings.entry_declaration_position entry,
        URust_Type_Mappings.entry_origin entry,
        URust_Type_Mappings.entry_identity entry)),
     URust_Item_Scope.dump_types ctxt |> map (fn entry =>
       (URust_Item_Scope.type_rust_name entry, URust_Item_Scope.type_position entry,
        URust_Item_Scope.type_hol_name entry)),
     URust_Item_Scope.dump_constructors ctxt |> map (fn entry =>
       (URust_Item_Scope.constructor_rust_type entry,
        URust_Item_Scope.constructor_rust_path entry,
        URust_Item_Scope.constructor_position entry,
        URust_Item_Scope.constructor_hol_type entry,
        URust_Item_Scope.constructor_term entry,
        URust_Item_Scope.constructor_scheme entry,
        URust_Item_Scope.constructor_origin entry,
        URust_Item_Scope.constructor_shape entry,
        URust_Item_Scope.constructor_fields entry)),
     Micro_Rust_Names.dump ctxt,
     Symtab.dest (Micro_Rust_Names.Declaration_Owners.get (Context.Proof ctxt)),
     Inttab.dest (Micro_Rust_Names.Automatic_Registrations.get (Context.Proof ctxt)),
     (URust_Import_Scope.frame_depth ctxt,
      map (fn binding =>
        (URust_Import_Scope.lookup_scoped ctxt (#namespace binding) (#alias binding),
         URust_Import_Scope.pending_roles ctxt binding)) bindings))

  fun capture action =
    let
      val reports = Synchronized.var "trait_test_reports" ([]: string list)
      val output = Synchronized.var "trait_test_output" ([]: string list)
      fun collect target chunks = Synchronized.change target (fn previous => previous @ chunks)
      val result = Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn (collect reports) (fn () =>
          Unsynchronized.setmp Private_Output.writeln_fn (collect output) (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE] (fn () => Exn.capture action ()) ()) ()) ())
      val chunks = Synchronized.value reports
      val markup = rev (fold Parser_Test_Reports.collect_markup (maps YXML.parse_body chunks) [])
      fun plain chunks = XML.content_of (maps YXML.parse_body chunks)
        |> Symbol.explode |> filter_out Symbol.is_control |> implode
    in {result = result, markup = markup, reports = plain chunks,
        output = plain (Synchronized.value output)} end

  fun plain_message exn = XML.content_of (YXML.parse_body (Runtime.exn_message exn))
  fun error_message label expected result =
    (case result of
       Exn.Res _ => error ("trait mapping regression: " ^ label ^ " was accepted")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (require (label ^ ": wrong rejection: " ^ plain_message exn)
              (String.isSubstring expected (plain_message exn));
            Runtime.exn_message exn))

  fun find_from text needle offset =
    if offset + size needle > size text then error ("missing probe token " ^ quote needle)
    else if String.substring (text, offset, size needle) = needle then offset
    else find_from text needle (offset + 1)

  fun range_nth occurrence label text needle =
    let
      fun search 0 offset = find_from text needle offset
        | search n offset = search (n - 1) (find_from text needle offset + size needle)
      val offset = search occurrence 0
      val first = Position.symbol_explode (String.substring (text, 0, offset)) (start label)
    in Position.range_position (Position.range (first, Position.symbol_explode needle first)) end

  val range = range_nth 0

  fun same_position props pos =
    Properties.get props Markup.offsetN = Option.map Value.print_int (Position.offset_of pos) andalso
    Properties.get props Markup.end_offsetN =
      Option.map Value.print_int (Position.end_offset_of pos) andalso
    Properties.get props Markup.fileN = Position.file_of pos

  fun positioned_message pos message =
    let
      fun positions (XML.Text _) result = result
        | positions (XML.Elem ((_, props), body)) result =
            fold positions body (props :: result)
      val props = fold positions (YXML.parse_body message) []
    in exists (fn props => same_position props pos) props end

  fun entities property name markup =
    markup |> map_filter (fn (element, props) =>
      if element = Markup.entityN andalso
        Properties.get props Markup.kindN = SOME "urust_trait" andalso
        Properties.get props Markup.nameN = SOME name
      then Properties.get props property else NONE)

  fun declaration name sort constants =
    "urust_trait " ^ quote name ^ " = " ^ cartouche sort ^
      (if null constants then "" else
        " urust_consts " ^ space_implode " and "
          (map (fn (name, rhs) => quote name ^ " = " ^ cartouche rhs) constants))
end
\<close>

section\<open> Direct lookups and builtins \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val ctxt = \<^context>
  val scale = mapping ctxt "Scale"
  val both = mapping ctxt "demo::ScaleFlag"
  val _ = require "class sort changed" (#sort scale = \<^sort>\<open>trait_scale\<close>)
  val _ = require "class intersection changed"
    (#sort both = Sign.minimize_sort \<^theory> \<^sort>\<open>{trait_scale, trait_flag}\<close>)
  val _ = require "marker sort changed" (#sort (mapping ctxt "Marker") = \<^sort>\<open>type\<close>)
  val _ = require "redundant superclass was not minimized"
    (#sort (mapping ctxt "RedundantScale") = #sort scale)
  val _ = require "unknown lookup was not absent" (is_none (Traits.lookup ctxt "UnknownTrait"))
  val _ = require "unknown associated constant was not absent"
    (is_none (Traits.associated_constant ctxt scale "MISSING"))
  val expected = \<^term>\<open>trait_ceiling TYPE(nat)\<close>
  val [(entry, value)] = Traits.traits_with_constant ctxt \<^typ>\<open>nat\<close> "CEILING"
  val _ = require "concrete lookup selected a wrong trait" (#path entry = "Scale")
  val _ = require "concrete lookup did not instantiate and apply its template" (value aconv expected)
  val [(redundant, height)] = Traits.traits_with_constant ctxt \<^typ>\<open>nat\<close> "HEIGHT"
  val _ = require "sufficient redundant sort changed its constant"
    (#path redundant = "RedundantScale" andalso height aconv expected)
  val intersection = TFree ("'both", #sort both)
  val intersection_candidates = Traits.traits_with_constant ctxt intersection "CEILING"
  val intersection_value = the (AList.lookup (op =)
    (map (fn (entry, value) => (#path entry, value)) intersection_candidates) "demo::ScaleFlag")
  val _ = require "sufficient intersection did not apply its constant"
    (intersection_value aconv
      \<^term>\<open>trait_ceiling TYPE('both::{trait_scale, trait_flag})\<close>)
  val _ = require "insufficient sort was accepted"
    (null (Traits.traits_with_constant ctxt (TFree ("'plain", \<^sort>\<open>type\<close>)) "CEILING"))
  val _ = require "missing constant produced a candidate"
    (null (Traits.traits_with_constant ctxt \<^typ>\<open>nat\<close> "MISSING"))
  val candidates = Traits.traits_with_constant ctxt \<^typ>\<open>bool\<close> "SLOT"
  val _ = require "two traits declaring one constant were not both retained"
    (map (#path o fst) candidates = ["SlotOne", "SlotTwo"])
  val _ = require "two constant values changed"
    (map snd candidates = [\<^term>\<open>3 :: nat\<close>, \<^term>\<open>4 :: nat\<close>])
  val builtins =
    [("Copy", \<^sort>\<open>type\<close>), ("Clone", \<^sort>\<open>type\<close>),
     ("PartialEq", \<^sort>\<open>type\<close>), ("Eq", \<^sort>\<open>type\<close>),
     ("Hash", \<^sort>\<open>type\<close>), ("Debug", \<^sort>\<open>type\<close>),
     ("PartialOrd", \<^sort>\<open>ord\<close>), ("Ord", \<^sort>\<open>ord\<close>)]
  val _ = List.app (fn (name, sort) =>
    require ("builtin " ^ name ^ " changed")
      (#sort (mapping ctxt name) = sort andalso null (#constants (mapping ctxt name)))) builtins
  val (_, report_free) = Parser_Test_Reports.markup (fn () =>
    (ignore (Traits.lookup ctxt "Scale");
     ignore (Traits.associated_constant ctxt scale "CEILING");
     ignore (Traits.traits_with_constant ctxt \<^typ>\<open>nat\<close> "CEILING")))
  val _ = require "report-free lookup API emitted markup" (null report_free)
  val _ = require "verbosity attribute's original full name changed"
    (Attrib.check_name ctxt ("urust_verbosity", Position.none) =
      "Parser_Impl_Command.urust_verbosity")
  val configured = run \<^theory> "trait-verbosity-short"
    "declare [[urust_verbosity = 1]]" |> context
  val _ = require "verbosity attribute does not share the lower config identity"
    (Config.get configured URust_Parser_Config.verbosity = 1)
  val configured_full = run \<^theory> "trait-verbosity-full"
    "declare [[Parser_Impl_Command.urust_verbosity = 2]]" |> context
  val _ = require "original full attribute no longer configures verbosity"
    (Config.get configured_full URust_Parser_Config.verbosity = 2)
in
  val _ = ()
end
\<close>

section\<open> Complete typed polymorphic schemes \<close>

text\<open>
The following audits distinguish alpha-equivalent polymorphic schemes from different result
types, class constraints and variable sharing. Fixed context types remain rigid.
\<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val ctxt = \<^context>
  val empty = mapping ctxt "PolymorphicEmpty"
  val template = term ctxt empty "POLY_EMPTY"
  val _ = require "independent result template retained a free type"
    (null (Term.add_tfrees template []) andalso length (Term.add_tvars template []) = 2)
  val repeated_text = declaration "RepeatedEmpty" "type"
    [("EMPTY_REPEAT", "(\<lambda>(_ :: 'a itself). ([] :: 'b list))")]
  val first = run \<^theory> "trait-polymorphic-first" repeated_text
  val original = mapping (context first) "RepeatedEmpty"
  val second = run_from first "trait-polymorphic-repeat" repeated_text
  val renamed = run_from second "trait-polymorphic-alpha"
    (declaration "RepeatedEmpty" "type"
      [("EMPTY_REPEAT", "(\<lambda>(_ :: 'x itself). ([] :: 'y list))")])
  val _ = List.app (fn state =>
    require "polymorphic redeclaration replaced its original entry or source positions"
      (mapping (context state) "RepeatedEmpty" = original)) [second, renamed]

  val conflicts =
    [("result-type", "undefined :: nat", "undefined :: bool"),
     ("result-constructor", "undefined :: 'b list", "undefined :: 'c option"),
     ("result-sort", "[] :: 'b::ord list", "[] :: 'c list"),
     ("result-sharing", "(([] :: 'b list), ([] :: 'b list))",
       "(([] :: 'c list), ([] :: 'd list))")]
  fun rhs result = "(\<lambda>(_ :: 'a itself). (" ^ result ^ "))"
  fun reject (label, left, right) =
    let
      val original_text = declaration "SchemeConflict" "type" [("VALUE", rhs left)]
      val state = run \<^theory> ("trait-scheme-first-" ^ label) original_text
      val original_entry = mapping (context state) "SchemeConflict"
      val neighbors = neighboring_snapshot [] (context state)
      val attempted = declaration "SchemeConflict" "type" [("VALUE", rhs right)]
      val failed = capture (fn () => run_from state ("trait-scheme-second-" ^ label) attempted)
      val message = error_message label "conflicting mappings" (#result failed)
      val _ = require (label ^ ": conflict lost either source")
        (positioned_message (range ("trait-scheme-first-" ^ label) original_text
           "SchemeConflict") message andalso
         positioned_message (range ("trait-scheme-second-" ^ label) attempted
           "SchemeConflict") message)
      val _ = require (label ^ ": conflict emitted reports or output")
        (null (#markup failed) andalso #reports failed = "" andalso #output failed = "")
      val _ = require (label ^ ": conflict changed its entry or neighboring data")
        (mapping (context state) "SchemeConflict" = original_entry andalso
         neighboring_snapshot [] (context state) = neighbors)
    in () end
  val _ = List.app reject conflicts

  val fixed = run \<^theory> "trait-fixed-results"
    ("locale trait_fixed_results = fixes left :: " ^ cartouche "'b itself" ^
      " and right :: " ^ cartouche "'c itself" ^ "\nbegin\n")
  val fixed_text = declaration "FixedResult" "type" [("FIXED", rhs "[] :: 'b list")]
  val fixed_first = run_from fixed "trait-fixed-result-first" fixed_text
  val fixed_entry = mapping (context fixed_first) "FixedResult"
  val fixed_repeat = run_from fixed_first "trait-fixed-result-repeat" fixed_text
  val _ = require "identical fixed-result declaration changed its entry"
    (mapping (context fixed_repeat) "FixedResult" = fixed_entry)
  val _ = require "fixed ambient result type was generalized"
    (Term.add_tfrees (term (context fixed_first) fixed_entry "FIXED") [] =
      [("'b", \<^sort>\<open>type\<close>)])
  val fixed_failure = capture (fn () => run_from fixed_first "trait-fixed-result-conflict"
    (declaration "FixedResult" "type" [("FIXED", rhs "[] :: 'c list")]))
  val _ = error_message "fixed result conflict" "conflicting mappings" (#result fixed_failure)
  val _ = require "fixed-result failure emitted reports or output"
    (null (#markup fixed_failure) andalso #reports fixed_failure = "" andalso
      #output fixed_failure = "")
  val _ = require "fixed-result conflict changed the original entry"
    (mapping (context fixed_first) "FixedResult" = fixed_entry)
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val ctxt = Proof_Context.set_mode Proof_Context.mode_schematic \<^context>
    |> Variable.declare_term (Var (("retained_scheme_index", 37), \<^typ>\<open>nat\<close>))
  val entry = mapping ctxt "FreshPair"
  val template = term ctxt entry "POLY_PAIR"
  val Type (_, [_, Type (_, [Type (_, [result_variable]), _])]) = fastype_of template
  val target = Proof_Context.cert_typ ctxt result_variable
  val native = Syntax.check_term ctxt
    (Const (\<^const_name>\<open>trait_fresh_pair\<close>, dummyT) $ Logic.mk_type target)
  val native_target = Logic.dest_type (the_single (#2 (Term.strip_comb native)))
  val observed = capture (fn () => Traits.traits_with_constant ctxt target "POLY_PAIR")
  val [(selected, actual)] = Exn.release (#result observed)
  val actual_target = Logic.dest_type (the_single (#2 (Term.strip_comb actual)))
  val Type (_, [Type (_, [actual_left]), Type (_, [actual_right])]) = fastype_of actual
  val _ = require "native or associated application changed the supplied witness"
    (native_target = target andalso actual_target = target andalso #path selected = "FreshPair")
  val _ = require "native application captured the independent result"
    (not (Term.exists_subtype (fn T => T = target) (fastype_of native)))
  val _ = require "associated application captured the independent result"
    (not (Term.exists_subtype (fn T => T = target) (fastype_of actual)))
  val _ = require "fresh associated result lost sharing or its class sort"
    (actual_left = actual_right andalso Type.sort_of_atyp actual_left = \<^sort>\<open>ord\<close>)
  val _ = require "associated result was not fresh relative to the context"
    (case actual_left of TVar ((_, index), _) => index > Variable.maxidx_of ctxt | _ => false)
  val native_scheme = singleton (Variable.polymorphic ctxt) native
  val _ = require "native and associated applications have different typed result schemes"
    (can (Pattern.match \<^theory> (actual, native_scheme)) (Vartab.empty, Vartab.empty) andalso
      can (Pattern.match \<^theory> (native_scheme, actual)) (Vartab.empty, Vartab.empty))
  val _ = require "polymorphic associated lookup emitted reports or output"
    (null (#markup observed) andalso #reports observed = "" andalso #output observed = "")
in
  val _ = ()
end
\<close>

section\<open> Locale transport \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val ctxt = \<^context>
  val offset = mapping ctxt "OffsetScale"
  val template = term ctxt offset "OFFSET"
  val _ = require "interpretation did not morph the associated term"
    (null (Term.add_frees template []) andalso
      Term.exists_subterm (fn Const (name, _) => name = \<^const_name>\<open>trait_offset.offset_ceiling\<close>
        | _ => false) template)
  val [(entry, value)] = Traits.traits_with_constant ctxt \<^typ>\<open>bool\<close> "OFFSET"
  val _ = require "interpreted template is not applied at the requested type"
    (#path entry = "OffsetScale" andalso
      value aconv \<^term>\<open>trait_offset.offset_ceiling 7 TYPE(bool)\<close>)
  val scoped = run \<^theory> "trait-local-scope"
    ("locale trait_block_scope = fixes token :: nat\nbegin\n" ^
      declaration "BlockMarker" "type" [])
  val _ = require "locale-local trait is absent inside its context"
    (is_some (Traits.lookup (context scoped) "BlockMarker"))
  val completed = run_from scoped "trait-local-end" "end"
  val _ = require "locale-local trait escaped without interpretation"
    (is_none (Traits.lookup (context completed) "BlockMarker"))
in
  val _ = ()
end
\<close>

section\<open> Validation, positions and atomic failure \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val thy = \<^theory>
  val base = initial thy
  val original = mapping (Proof_Context.init_global thy) "Scale"
  val candidate_keys =
    ["BadSort", "BadShape", "ConcreteWitness", "DependentResult", "WeakScale",
     "DuplicateConstant", "Scale", "bad:::Trait", "LateFailure"]
  val original_entries = map (fn key => (key, Traits.lookup (context base) key)) candidate_keys
  val original_neighbors = neighboring_snapshot [] (context base)
  val cases =
    [("unreadable-sort", "missing_trait_sort",
       declaration "BadSort" "missing_trait_sort" [], ("missing_trait_sort", 0)),
     ("wrong-shape", "must have type",
       declaration "BadShape" "type" [("CAP", "(3 :: nat)")], ("(3 :: nat)", 0)),
     ("concrete-witness", "must have type",
       declaration "ConcreteWitness" "type" [("CAP", "(\<lambda>(_ :: nat itself). (3 :: nat))")],
       ("(\<lambda>(_ :: nat itself). (3 :: nat))", 0)),
     ("dependent-result", "result type depends",
       declaration "DependentResult" "type" [("CAP", "(\<lambda>(_ :: 'a itself). (undefined :: 'a))")],
       ("(\<lambda>(_ :: 'a itself). (undefined :: 'a))", 0)),
     ("sort-mismatch", "beyond mapped sort",
       declaration "WeakScale" "type" [("CAP", "trait_ceiling")], ("trait_ceiling", 0)),
     ("duplicate-constant", "duplicate associated constant",
       declaration "DuplicateConstant" "type"
         [("CAP", "(\<lambda>(_ :: 'a itself). (3 :: nat))"),
          ("CAP", "(\<lambda>(_ :: 'a itself). (4 :: nat))")], ("CAP", 1)),
     ("conflicting-key", "conflicting mappings",
       declaration "Scale" "type" [], ("Scale", 0)),
     ("malformed-path", "malformed Rust trait path",
       declaration "bad:::Trait" "type" [], ("bad:::Trait", 0)),
     ("late-failure", "must have type",
       declaration "LateFailure" "type"
         [("GOOD", "(\<lambda>(_ :: 'a itself). (3 :: nat))"), ("BAD", "(4 :: nat)")],
       ("(4 :: nat)", 0))]

  fun check (label, expected, text, (token, occurrence)) =
    let
      val observed = capture (fn () => run_from base label text)
      val message = error_message label expected (#result observed)
      val _ = require (label ^ ": diagnostic lost the offending source")
        (positioned_message (range_nth occurrence label text token) message)
      val _ = require (label ^ ": failure emitted native or semantic reports")
        (null (#markup observed) andalso #reports observed = "")
      val _ = require (label ^ ": failure printed successful output") (#output observed = "")
      val _ = require (label ^ ": original theory changed")
        (Context.eq_thy (thy, Toplevel.theory_of base))
      val after = mapping (context base) "Scale"
      val _ = require (label ^ ": existing mapping changed")
        (#sort original = #sort after andalso #constants original = #constants after)
      val _ = require (label ^ ": failing declaration changed its registry")
        (forall (fn (key, entry) => Traits.lookup (context base) key = entry) original_entries)
      val _ = require (label ^ ": failing declaration changed a neighboring registry")
        (neighboring_snapshot [] (context base) = original_neighbors)
    in () end
  val _ = List.app check cases

  val rigid_prefix =
    "locale rigid_trait_domain = fixes token :: " ^ cartouche "'a itself" ^ "\nbegin\n"
  val rigid = declaration "RigidDomain" "type"
    [("CAP", "(\<lambda>(_ :: 'a itself). (3 :: nat))")]
  val state = run thy "rigid-trait-prefix" rigid_prefix
  val observed = capture (fn () => run_from state "rigid-trait-domain" rigid)
  val message = error_message "rigid-domain" "witness type is fixed by the context"
    (#result observed)
  val _ = require "rigid witness rejection lost its associated-term source"
    (positioned_message (range "rigid-trait-domain" rigid
      "(\<lambda>(_ :: 'a itself). (3 :: nat))") message)
  val _ = require "rigid-domain failure leaked a mapping"
    (is_none (Traits.lookup (context state) "RigidDomain"))
  val recovered = run_from base "trait-recovery" (declaration "RecoveredMarker" "type" [])
  val _ = require "declaration recovery failed"
    (is_some (Traits.lookup (context recovered) "RecoveredMarker"))
in
  val _ = ()
end
\<close>

section\<open> Full failure reports and registry preservation \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val thy = \<^theory>
  val loud = run thy "trait-atomic-verbosity" "declare [[urust_verbosity = 2]]"
  val loud_neighbors = neighboring_snapshot [] (context loud)
  val failed = capture (fn () => run_from loud "trait-atomic-loud-failure"
    (declaration "AtomicOutputFailure" "trait_scale"
      [("GOOD", "trait_ceiling"), ("BAD", "(4 :: nat)")]))
  val _ = error_message "loud late failure" "must have type" (#result failed)
  val _ = require "loud failure emitted native/semantic reports or successful output"
    (null (#markup failed) andalso #reports failed = "" andalso #output failed = "")
  val command_recovery = capture (fn () => run_from loud "trait-atomic-loud-recovery"
    (declaration "AtomicOutputRecovery" "trait_scale" [("CAP", "trait_ceiling")]))
  val recovered_state = Exn.release (#result command_recovery)
  val _ = require "command recovery lost its successful reports or output"
    (length (entities Markup.defN "AtomicOutputRecovery" (#markup command_recovery)) = 1 andalso
      String.isSubstring "trait AtomicOutputRecovery" (#output command_recovery))
  val _ = require "command failure/recovery changed a neighboring registry"
    (neighboring_snapshot [] (context recovered_state) = loud_neighbors)
  val _ = require "command recovery retained the failed declaration"
    (is_none (Traits.lookup (context recovered_state) "AtomicOutputFailure"))

  val import_pos = start "trait-retained-import"
  val import_layout = URust_AST.make_source_layout import_pos []
  val import_item = URust_AST.Use_Item
    (URust_AST.Use_Path ([("U8Alias", import_pos)],
      SOME ("RetainedTraitType", import_pos), import_layout), import_layout)
  val framed = Named_Target.theory_init thy
    |> (fn ctxt => URust_Imports.prepare_batch_unreported URust_Imports.Require_Targets ctxt
      (URust_Imports.validate_batch [import_item]))
  val retained = the (URust_Import_Scope.lookup framed
    URust_Import_Scope.Type_Namespace "RetainedTraitType")
  val local_base = framed
    |> URust_Import_Scope.add_pending_roles [(retained, [URust_Import_Scope.Generated_Enum])]
  val previous = neighboring_snapshot [retained] local_base
  val previous_theory = Proof_Context.theory_of local_base
  val local_failure =
    {path = ("AtomicRegistryFailure", start "trait-registry-failure-key"),
     sort = source "trait-registry-failure-sort" "trait_scale",
     constants =
       [(("GOOD", start "trait-registry-good-name"),
          source "trait-registry-good-term" "trait_ceiling"),
        (("BAD", start "trait-registry-bad-name"),
          source "trait-registry-bad-term" "(4 :: nat)")]}
  val failed_api = capture (fn () => Traits.declare local_failure local_base)
  val _ = error_message "local registry failure" "must have type" (#result failed_api)
  val _ = require "local registry failure emitted native/semantic reports or output"
    (null (#markup failed_api) andalso #reports failed_api = "" andalso #output failed_api = "")
  val _ = require "local registry failure changed neighboring data or its theory"
    (neighboring_snapshot [retained] local_base = previous andalso
      Context.eq_thy (Proof_Context.theory_of local_base, previous_theory))
  val recovery = capture (fn () => Traits.declare
    {path = ("AtomicRegistryRecovery", start "trait-registry-recovery-key"),
     sort = source "trait-registry-recovery-sort" "trait_scale",
     constants = [(("CAP", start "trait-registry-recovery-name"),
       source "trait-registry-recovery-term" "trait_ceiling")]} local_base)
  val recovered = Exn.release (#result recovery)
  val _ = require "local recovery did not release its successful native and trait reports"
    (length (entities Markup.defN "AtomicRegistryRecovery" (#markup recovery)) = 1 andalso
      exists (fn (name, props) => name = Markup.entityN andalso
        Properties.get props Markup.kindN = SOME Markup.constantN) (#markup recovery))
  val _ = require "local API failure/recovery changed a neighboring registry or import frame"
    (neighboring_snapshot [retained] recovered = previous)
  val _ = require "local recovery retained the failed trait or lost the new trait"
    (is_none (Traits.lookup recovered "AtomicRegistryFailure") andalso
      is_some (Traits.lookup recovered "AtomicRegistryRecovery"))
  val _ = require "local recovery changed verbosity"
    (Config.get recovered URust_Parser_Config.verbosity = 0)
in
  val _ = ()
end
\<close>

section\<open> Nested report transactions and recovery \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val lthy = Named_Target.theory_init \<^theory>
  val previous = neighboring_snapshot [] lthy

  fun event label marker = Reports.report_text lthy (start label) Markup.typing marker
  fun native label marker = Reports.native lthy (fn ctxt =>
    Context_Position.report_text ctxt (start label) Markup.typing marker)
  fun forwarded label marker =
    Reports.output_reporter Output.report
      [YXML.string_of_body [XML.Elem
        ((Markup.typingN, Position.properties_of (start label)), [XML.Text marker])]]
  fun navigation label marker = Navigation.defer_report_text lthy (start label) Markup.typing marker
  fun events prefix suffix =
    (event (prefix ^ "-report") ("REPORT_" ^ suffix);
     native (prefix ^ "-read") ("READ_" ^ suffix);
     forwarded (prefix ^ "-forward") ("FORWARD_" ^ suffix);
     navigation (prefix ^ "-navigation") ("NAVIGATION_" ^ suffix))
  val payload =
    {path = ("NestedAtomicFailure", start "trait-nested-failure-key"),
     sort = source "trait-nested-failure-sort" "trait_scale",
     constants =
       [(("GOOD", start "trait-nested-good-name"),
          source "trait-nested-good-term" "trait_ceiling"),
        (("BAD", start "trait-nested-bad-name"),
          source "trait-nested-bad-term" "(4 :: nat)")]}

  fun check capture_reports label =
    let
      val observed = capture (fn () => capture_reports (fn () =>
        let
          val _ = events (label ^ "-before") "BEFORE"
          val rejected = Exn.capture (fn () => Reports.capture (fn () =>
            (events (label ^ "-failed") "FAILED";
             error "expected nested report failure"))) ()
          val _ = error_message "nested report failure" "expected nested report failure" rejected
          val failed = Exn.capture (Traits.declare payload) lthy
          val _ = error_message "nested trait failure" "must have type" failed
          val (_, successful) = Reports.capture (fn () => events (label ^ "-success") "SUCCESS")
          val _ = Reports.replay lthy successful
          val _ = events (label ^ "-after") "AFTER"
        in () end))
      val (_, pending) = Exn.release (#result observed)
      val _ = require (label ^ ": nested work emitted before parent replay")
        (null (#markup observed) andalso #reports observed = "" andalso #output observed = "")
      val replayed = capture (fn () => Reports.replay lthy pending)
      val _ = Exn.release (#result replayed)
      val expected =
        ["REPORT_BEFORE", "READ_BEFORE", "FORWARD_BEFORE",
         "REPORT_SUCCESS", "READ_SUCCESS", "FORWARD_SUCCESS",
         "REPORT_AFTER", "READ_AFTER", "FORWARD_AFTER",
         "NAVIGATION_BEFORE", "NAVIGATION_SUCCESS", "NAVIGATION_AFTER"]
      val _ = require (label ^ ": failed events leaked or successful event order changed")
        (#reports replayed = implode expected andalso length (#markup replayed) = length expected)
      val _ = require (label ^ ": replay printed successful output")
        (#output replayed = "")
      val _ = require (label ^ ": caught failure changed registries or installed its trait")
        (neighboring_snapshot [] lthy = previous andalso
          is_none (Traits.lookup lthy "NestedAtomicFailure"))
    in () end
  val _ = check Reports.capture "trait-nested-capture"
  val _ = check Reports.capture_members "trait-nested-members"
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val ctxt = \<^context>
  fun event label marker = Navigation.defer_report_text ctxt (start label) Markup.typing marker
  val observed = capture (fn () => Navigation.capture (fn () =>
    let
      val _ = event "trait-navigation-before" "PARENT_BEFORE"
      val failed = Exn.capture (fn () => Navigation.capture (fn () =>
        (event "trait-navigation-failed" "FAILED_INNER";
         error "expected nested navigation failure"))) ()
      val _ = error_message "nested navigation failure" "expected nested navigation failure" failed
      val (_, successful) = Navigation.capture (fn () =>
        event "trait-navigation-success" "SUCCESSFUL_INNER")
      val _ = Navigation.replay ctxt successful
      val _ = event "trait-navigation-after" "PARENT_AFTER"
    in () end))
  val (_, pending) = Exn.release (#result observed)
  val _ = require "navigation nesting emitted before parent replay"
    (null (#markup observed) andalso #reports observed = "" andalso #output observed = "")
  val replayed = capture (fn () => Navigation.replay ctxt pending)
  val _ = Exn.release (#result replayed)
  val _ = require "navigation rollback lost successful events or retained its failed event"
    (#reports replayed = "PARENT_BEFORESUCCESSFUL_INNERPARENT_AFTER" andalso
      map (fn (_, props) => Properties.get props Markup.fileN) (#markup replayed) =
        map SOME ["trait-navigation-before", "trait-navigation-success", "trait-navigation-after"])
  val _ = require "navigation replay printed output" (#output replayed = "")
in
  val _ = ()
end
\<close>

section\<open> Theory merges in both orders \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val left = \<^theory>\<open>Parser_Test_Fixtures_Left\<close>
  val right = \<^theory>\<open>Parser_Test_Fixtures_Right\<close>
  fun merge label parents = Theory.begin_theory (label, Position.none) parents
  val forward = merge "Trait_Fixture_Forward" [left, right] |> Proof_Context.init_global
  val backward = merge "Trait_Fixture_Backward" [right, left] |> Proof_Context.init_global
  val _ = List.app (fn ctxt =>
    (require "identical merge lost shared mapping"
       (is_some (Traits.lookup ctxt "merge::SharedMarker"));
     require "merge lost one branch"
       (is_some (Traits.lookup ctxt "merge::LeftMarker") andalso
        is_some (Traits.lookup ctxt "merge::RightMarker")))) [forward, backward]
  val shared_forward = mapping forward "merge::SharedMarker"
  val shared_backward = mapping backward "merge::SharedMarker"
  val _ = require "identical merge chose different navigation origins"
    (#pos shared_forward = #pos shared_backward)
  val _ = require "identical merge changed its associated constant"
    (term forward shared_forward "COUNT" aconv term backward shared_backward "COUNT")
  val [(shared, count)] = Traits.traits_with_constant forward \<^typ>\<open>nat\<close> "COUNT"
  val _ = require "identical merge did not retain the applied associated value"
    (#path shared = "merge::SharedMarker" andalso count aconv \<^term>\<open>5 :: nat\<close>)

  fun branch label sort =
    merge label [\<^theory>]
    |> (fn thy => run thy label (declaration "MergeCollision" sort []))
    |> Toplevel.theory_of |> Theory.end_theory
  val conflicting_left = branch "Trait_Conflict_Left" "type"
  val conflicting_right = branch "Trait_Conflict_Right" "ord"
  fun reject_merge (label, parents) =
    let
      val result = Exn.capture (fn () => merge label parents) ()
      val message = error_message label "conflicting mappings for \"MergeCollision\"" result
      val _ = require (label ^ ": merge conflict lost both source files")
        (String.isSubstring "Trait_Conflict_Left" message andalso
         String.isSubstring "Trait_Conflict_Right" message)
    in () end
  val _ = List.app reject_merge
    [("Trait_Conflict_Forward", [conflicting_left, conflicting_right]),
     ("Trait_Conflict_Backward", [conflicting_right, conflicting_left])]

  val polymorphic_forward = mapping forward "merge::Polymorphic"
  val polymorphic_backward = mapping backward "merge::Polymorphic"
  val _ = require "alpha-equivalent merge selected different navigation origins"
    (#pos polymorphic_forward = #pos polymorphic_backward)
  val _ = List.app (fn name =>
    require ("alpha-equivalent merge changed typed template " ^ name)
      (term forward polymorphic_forward name aconv term backward polymorphic_backward name))
    ["MERGE_EMPTY", "MERGE_PAIR"]
  val _ = List.app (fn ctxt =>
    let
      val (empty_entry, empty_value) =
        the_single (Traits.traits_with_constant ctxt \<^typ>\<open>nat\<close> "MERGE_EMPTY")
      val (pair_entry, pair_value) =
        the_single (Traits.traits_with_constant ctxt \<^typ>\<open>bool\<close> "MERGE_PAIR")
      val empty_type =
        (case fastype_of empty_value of
           Type (\<^type_name>\<open>list\<close>, [T]) => T
         | _ => error "merged empty result is not a list")
      val (left_type, right_type) =
        (case fastype_of pair_value of
           Type (\<^type_name>\<open>prod\<close>,
             [Type (\<^type_name>\<open>list\<close>, [T]), Type (\<^type_name>\<open>list\<close>, [U])]) => (T, U)
         | _ => error "merged pair result is not a pair of lists")
      val _ = require "merged result lost its independent class-constrained type"
        (#path empty_entry = "merge::Polymorphic" andalso
          Type.sort_of_atyp empty_type = \<^sort>\<open>ord\<close>)
      val _ = require "merged result lost its independent variable sharing"
        (#path pair_entry = "merge::Polymorphic" andalso left_type = right_type)
    in () end) [forward, backward]

  val scheme_conflicts =
    [("Types", "undefined :: nat", "undefined :: bool"),
     ("Constructors", "undefined :: 'b list", "undefined :: 'c option"),
     ("Sorts", "[] :: 'b::ord list", "[] :: 'c list"),
     ("Sharing", "(([] :: 'b list), ([] :: 'b list))",
       "(([] :: 'c list), ([] :: 'd list))")]
  fun reject_scheme_merge (kind, first, second) =
    let
      fun scheme_branch side result =
        let val label = "Trait_Scheme_" ^ kind ^ "_" ^ side in
          merge label [\<^theory>]
          |> (fn thy => run thy label (declaration "MergeSchemeConflict" "type"
            [("VALUE", "(\<lambda>(_ :: 'a itself). (" ^ result ^ "))")]))
          |> Toplevel.theory_of |> Theory.end_theory
        end
      val first_parent = scheme_branch "Left" first
      val second_parent = scheme_branch "Right" second
      fun reject parents =
        let
          val failed = capture (fn () =>
            merge ("Trait_Scheme_Conflict_" ^ kind) parents)
          val message = error_message kind
            "conflicting mappings for \"MergeSchemeConflict\"" (#result failed)
          val _ = require (kind ^ ": scheme merge lost both conflict sources")
            (String.isSubstring ("Trait_Scheme_" ^ kind ^ "_Left") message andalso
              String.isSubstring ("Trait_Scheme_" ^ kind ^ "_Right") message)
          val _ = require (kind ^ ": failed scheme merge emitted reports or output")
            (null (#markup failed) andalso #reports failed = "" andalso #output failed = "")
        in () end
    in List.app reject [[first_parent, second_parent], [second_parent, first_parent]] end
  val _ = List.app reject_scheme_merge scheme_conflicts
in
  val _ = ()
end
\<close>

section\<open> Declaration and bound markup, verbosity \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  val label = "trait-declaration-markup"
  val text = declaration "MarkupScale" "type"
    [("CAP", "(\<lambda>(_ :: 'a itself). (3 :: nat))")]
  val observed = capture (fn () => run \<^theory> label text)
  val state = Exn.release (#result observed)
  val ctxt = context state
  val {term = template, pos = constant_pos} =
    the (Traits.associated_constant ctxt (mapping ctxt "MarkupScale") "CAP")
  val _ = require "associated constant did not retain its complete term source"
    (constant_pos = range label text "(\<lambda>(_ :: 'a itself). (3 :: nat))")
  val _ = require "associated constant lookup returned an applied value"
    (case fastype_of template of
       Type (\<^type_name>\<open>fun\<close>, [Type (\<^type_name>\<open>itself\<close>, [TVar _]), _]) => true
     | _ => false)
  val ids = entities Markup.defN "MarkupScale" (#markup observed)
  val _ = require "declaration has no unique definition entity" (length ids = 1)
  val _ = require "declaration tooltip has no mapped sort"
    (String.isSubstring "MarkupScale = type" (#reports observed))
  val use_label = "trait-bound-markup"
  val use_pos = range use_label "MarkupScale" "MarkupScale"
  val bound = Traits.Rust_Trait_Bound ([("MarkupScale", use_pos)],
    URust_AST.make_source_layout use_pos [])
  val ((resolved, deferred), immediate) = Parser_Test_Reports.markup (fn () =>
    Navigation.capture (fn () => Traits.resolve_bound ctxt bound))
  val _ = require "bound resolution emitted reports before transaction release" (null immediate)
  val references = capture (fn () => Navigation.replay ctxt deferred)
  val _ = require "bound resolves another trait" (#path resolved = "MarkupScale")
  val _ = require "bound did not navigate to its declaration"
    (entities Markup.refN "MarkupScale" (#markup references) = ids)
  val _ = require "bound tooltip has no mapped sort"
    (String.isSubstring "MarkupScale = type" (#reports references))
  val missing_pos = range "trait-missing-bound" "Missing" "Missing"
  val missing = Traits.Rust_Trait_Bound ([("Missing", missing_pos)],
    URust_AST.make_source_layout missing_pos [])
  val message = error_message "missing-bound" "unregistered Rust trait \"Missing\""
    (Exn.capture (fn () => Navigation.capture (fn () => Traits.resolve_bound ctxt missing)) ())
  val _ = require "unregistered bound lost its use position"
    (positioned_message missing_pos message)

  fun output level =
    let
      val label = "trait-verbosity-" ^ string_of_int level
      val text = "declare [[urust_verbosity = " ^ string_of_int level ^ "]]\n" ^
        declaration "OutputScale" "type"
          [("CAP", "(\<lambda>(_ :: 'a itself). (3 :: nat))")]
      val observed = capture (fn () => run \<^theory> label text)
      val _ = Exn.release (#result observed)
    in #output observed end
  val _ = require "verbosity zero is not quiet" (output 0 = "")
  val _ = List.app (fn level =>
    let val printed = output level in
      require ("verbosity " ^ string_of_int level ^ " omitted mapping output")
        (String.isSubstring "trait OutputScale" printed andalso
         String.isSubstring "CAP" printed)
    end) [1, 2]
in
  val _ = ()
end
\<close>

section\<open> Shared AST trait-bound identity \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  structure AST = URust_AST
  fun from_ast (bound: AST.rust_trait_bound): Traits.rust_trait_bound = bound
  fun to_ast (bound: Traits.rust_trait_bound): AST.rust_trait_bound = bound
  val resolve_ast: Proof.context -> AST.rust_trait_bound -> Traits.trait_entry = Traits.resolve_bound
  val declared = capture (fn () => run \<^theory> "trait-bridge-declaration"
    (declaration "bridge::Scale" "trait_scale" []))
  val ctxt = context (Exn.release (#result declared))
  val identity = entities Markup.defN "bridge::Scale" (#markup declared)
  val _ = require "bridge fixture lost its definition identity" (length identity = 1)
  val neighbors = neighboring_snapshot [] ctxt
  val previous_theory = Proof_Context.theory_of ctxt
  val keys = ["bridge::Scale", "Marker", "Scale", "Copy"]
  val entries = map (mapping ctxt) keys

  fun parse label text =
    the (URust_Parser.parse_function_source ctxt (source label text))
  val label = "trait-bridge-carrier"
  val text = "fn BoundBridge<T: bridge::Scale + Marker>()\n" ^
    "/* \<alpha> */ where T: Scale + Copy {}"
  val parsed = capture (fn () => parse label text)
  val function = Exn.release (#result parsed)
  val (parameter, bounds) = the_single (AST.function_bounds function)
  val _ = require "parser resolved trait bounds prematurely"
    (forall (fn key => null (entities Markup.refN key (#markup parsed))) keys)
  val _ = require "parser-to-registry carrier changed bound order"
    (parameter = "T" andalso
      map (fn AST.Rust_Trait_Bound (segments, _) => space_implode "::" (map fst segments)) bounds = keys)
  val ast_bound: AST.rust_trait_bound = hd bounds
  val legacy_bound: Traits.rust_trait_bound = from_ast ast_bound
  val Traits.Rust_Trait_Bound (segments, layout) = ast_bound
  val rebuilt: AST.rust_trait_bound = Traits.Rust_Trait_Bound (segments, layout)
  val AST.Rust_Trait_Bound (legacy_segments, legacy_layout) = to_ast legacy_bound
  val AST.Rust_Trait_Bound (rebuilt_segments, rebuilt_layout) = rebuilt
  val _ = require "constructor replication changed the bound payload"
    (segments = legacy_segments andalso segments = rebuilt_segments andalso
      AST.source_span layout = AST.source_span legacy_layout andalso
      AST.source_span layout = AST.source_span rebuilt_layout andalso
      AST.source_tokens layout = AST.source_tokens legacy_layout andalso
      AST.source_tokens layout = AST.source_tokens rebuilt_layout)
  val _ = require "qualified parsed bound lost its exact segment positions"
    (map snd segments = [range label text "bridge", range label text "Scale"])

  val observed = capture (fn () => Navigation.capture (fn () => map (resolve_ast ctxt) bounds))
  val (resolved, pending) = Exn.release (#result observed)
  val _ = require "parsed bound resolution emitted before replay"
    (null (#markup observed) andalso #reports observed = "" andalso #output observed = "")
  val _ = require "parsed bound resolution changed its mapped entries or sorts"
    (resolved = entries andalso map #sort resolved =
      [\<^sort>\<open>trait_scale\<close>, \<^sort>\<open>type\<close>,
       \<^sort>\<open>trait_scale\<close>, \<^sort>\<open>type\<close>])
  val replayed = capture (fn () => Navigation.replay ctxt pending)
  val _ = Exn.release (#result replayed)
  val _ = require "AST bound did not reference the original trait definition"
    (entities Markup.refN "bridge::Scale" (#markup replayed) = identity)
  val _ = List.app (fn key => require ("parsed bound lost reference " ^ key)
    (length (entities Markup.refN key (#markup replayed)) = 1)) keys
  val expected_segments = maps (fn AST.Rust_Trait_Bound (segments, _) => map snd segments) bounds
  val _ = require "inline/where bound ranges changed after the source symbol"
    (expected_segments = [range label text "bridge", range label text "Scale",
      range label text "Marker", range_nth 1 label text "Scale", range label text "Copy"])
  val tooltip_positions = #markup replayed |> map_filter (fn (name, props) =>
    if name = Markup.typingN then SOME props else NONE)
  val _ = require "parsed bound changed segment tooltip positions or order"
    (ListPair.allEq (fn (props, pos) => same_position props pos) (tooltip_positions, expected_segments))
  val expected_tooltips = maps (fn (AST.Rust_Trait_Bound (segments, _), entry) =>
    replicate (length segments) (#path entry ^ " = " ^
      XML.content_of (YXML.parse_body (Syntax.string_of_sort ctxt (#sort entry)))))
    (bounds ~~ resolved)
  val _ = require "parsed bound changed mapped-sort tooltip text or printed output"
    (#reports replayed = implode expected_tooltips andalso #output replayed = "")

  val missing_label = "trait-bridge-missing"
  val missing_text = "fn MissingBridge<T: bridge::Absent>() {}"
  val missing_parsed = capture (fn () => parse missing_label missing_text)
  val (_, missing_bounds) = the_single (AST.function_bounds (Exn.release (#result missing_parsed)))
  val missing = the_single missing_bounds
  val failed = capture (fn () => Navigation.capture (fn () => resolve_ast ctxt missing))
  val message = error_message "parsed missing bound" "unregistered Rust trait \"bridge::Absent\""
    (#result failed)
  val _ = require "parsed missing bound lost its final segment range"
    (positioned_message (range missing_label missing_text "Absent") message)
  val _ = require "parsed missing bound emitted successful reports or output"
    (null (#markup failed) andalso #reports failed = "" andalso #output failed = "")
  val recovery = capture (fn () => Navigation.capture (fn () => Traits.resolve_bound ctxt legacy_bound))
  val (recovered, recovery_reports) = Exn.release (#result recovery)
  val released = capture (fn () => Navigation.replay ctxt recovery_reports)
  val _ = Exn.release (#result released)
  val _ = require "legacy constructor recovery changed resolution or definition identity"
    (recovered = hd entries andalso
      entities Markup.refN "bridge::Scale" (#markup released) = identity)
  val _ = require "bridge resolution/failure/recovery changed registries or theory"
    (map (mapping ctxt) keys = entries andalso neighboring_snapshot [] ctxt = neighbors andalso
      is_none (Traits.lookup ctxt "bridge::Absent") andalso
      Context.eq_thy (Proof_Context.theory_of ctxt, previous_theory))
in
  val _ = ()
end
\<close>

chapter\<open> Syntax \<close>

text\<open>
Generic headers parse and print before signature elaboration. These syntax audits preserve the
delivered lifetime, receiver, datatype and retained literal-type behavior. Executable generic
signature, registration and atomicity audits appear in the Signatures chapter.
\<close>

section\<open> Source positions and test support \<close>

ML\<open>
structure Generic_Syntax_Test =
struct
  open URust_AST
  fun require label condition =
    if condition then () else error ("generic syntax audit: " ^ label)
  fun start label =
    let val position = Position.make0 1 1 0 "" label label
        val thread_position = Position.thread_data ()
    in if is_some (Position.id_of thread_position)
       then Position.copy_id thread_position position else position end
  fun source label text = Parser_Lex_Util.positioned_content_source text (start label)
  fun parse ctxt label text =
    (case URust_Parser.parse_function_source ctxt (source label text) of
       SOME function => function | NONE => error (label ^ ": empty function"))
  fun chunk ctxt label text =
    (case URust_Parser.parse_chunk_source ctxt (source label text) of
       SOME chunk => chunk | NONE => error (label ^ ": empty chunk"))
  fun position_range pos =
    (the_default ~1 (Position.offset_of pos), the_default ~1 (Position.end_offset_of pos))
  fun raw_index text needle occurrence =
    let
      val target = Symbol.explode needle
      fun search _ [] _ = error ("missing test token " ^ quote needle)
        | search offset (symbols as symbol :: rest) n =
            if take (length target) symbols = target andalso n = 0 then offset
            else search (offset + size symbol) rest
              (if take (length target) symbols = target then n - 1 else n)
    in search 0 (Symbol.explode text) occurrence end
  fun range_of text needle occurrence =
    let val raw = raw_index text needle occurrence
        val start = length (Symbol.explode (String.substring (text, 0, raw))) + 1
    in (start, start + length (Symbol.explode needle)) end
  fun message_positions text =
    let
      fun collect (XML.Elem ((name, props), body)) =
            (if name = Markup.positionN then [Position.of_properties props] else []) @ maps collect body
        | collect (XML.Text _) = []
    in maps collect (YXML.parse_body text) end
  fun failure label expected action =
    (case Exn.capture action () of
       Exn.Res _ => error (label ^ ": unexpectedly accepted")
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else let val message = Runtime.exn_message exn in
           require (label ^ ": wrong diagnostic " ^ message) (String.isSubstring expected message);
           message
         end)
  fun rejects ctxt (label, expected, text, needle, occurrence) =
    let val message = failure label expected (fn () => parse ctxt label text)
        val positions = map position_range (message_positions message)
    in require (label ^ ": wrong error range")
         (not (null positions) andalso hd positions = range_of text needle occurrence) end
  fun roundtrip ctxt label text =
    let
      val function = parse ctxt label text
      fun check options =
        let val generated = URust_Printer.string_of_function options function
            val reparsed = parse ctxt (label ^ "-reparsed") generated
        in require (label ^ ": printer tokens changed: " ^ generated)
             (URust_Printer.tokens_of_function options function =
              URust_Printer.tokens_of_function options reparsed) end
      val _ = List.app check [URust_Printer.serialized_options, URust_Printer.human_options]
    in function end
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun run thy label text =
    fold (Toplevel.command_exception true)
      (Outer_Syntax.parse_text thy (K thy) (start label) text) (Toplevel.make_state (SOME thy))
  fun reports action =
    let
      val (result, markup) = Parser_Test_Reports.markup action
      val events = map (fn (name, props) =>
        (name, position_range (Position.of_properties props), props)) markup
    in (result, events) end
  fun has_role events name range = exists (fn (role, at, _) => role = name andalso at = range) events
end
\<close>

section\<open> Accepted headers and printer roundtrips \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val shapes =
    [("absent", "fn Plain() {}"),
     ("empty", "fn Empty<>() {}"),
     ("rust-function-parser-generics", "fn Generic<T>(value: T) -> T { value }"),
     ("types", "fn Pair<T, U,>(left: T, right: U) -> T { left }"),
     ("lifetimes", "fn Borrow<'a, 'b,>(value: &'a mut u8) -> &'a mut u8 { value }"),
     ("const", "fn Sized<const N: usize,>(value: [u8; N]) -> usize { 0 }"),
     ("mixed-type-const", "fn Mix<'a, T, const N: usize, U, const M: usize>(value: T) -> T { value }"),
     ("mixed-const-type", "fn Mix<const N: usize, T, const M: usize, U,>(value: T) -> T { value }"),
     ("inline", "fn Bounds<T: Marker + outer::inner::Scale, U: Copy>(value: T) -> T { value }"),
     ("where-only", "fn Bounds<T, U>(value: T) -> T where T: Marker, U: outer::Scale, { value }"),
     ("both-bounds", "fn Bounds<T: Marker>(value: T) -> T where T: Scale + Copy { value }"),
     ("unused", "fn Unused<T>() {}"),
     ("retained-types", "fn Retained<T>(value: impl Marker, callback: fn(T) -> T) -> impl Marker { value }"),
     ("signature-identifiers", "fn Names(for: u8, where: u8) {}"),
     ("bare-return-identifier", "fn Named(value: where) -> where { value }"),
     ("reference-return-identifier", "fn Named<T>() -> &mut where where T: Marker {}"),
     ("impl-return-identifier", "fn Named<T>() -> impl where where T: Marker {}"),
     ("function-return-identifier", "fn Named<T>() -> fn(u8) -> where where T: Marker {}"),
     ("qualified-result-where", "fn PathClause<T>() -> outer::Result where T: Marker {}"),
     ("where-tail-then-clause", "fn PathClause<T>() -> outer::where where T: Marker {}"),
     ("commented-path-tail", "fn PathClause<T>() -> outer:: /* tail */ where where T: Marker {}"),
     ("path-tail-identifiers", "fn PathTail(value: outer::where) -> outer::where { value }"),
     ("qualified-bound-identifiers", "fn BoundTail<T: outer::where>() where T: other::where {}"),
     ("function-keyword-name", "fn where() {}"),
     ("nested-identifiers", "fn Nested<T>(value: outer::where<T>, callback: fn(where) -> where) {}")]
  val _ = List.app (fn (label, text) => ignore (roundtrip ctxt label text)) shapes
  val projected = roundtrip ctxt "projection"
    "fn Project<'a, T: A + outer::B, const N: usize, U>(value: T) where U: C, T: D + E, T: F { value }"
  val _ = require "source generic order"
    (map (fn Generic_Lifetime (Rust_Lifetime (name, _)) => name
           | Generic_Type (name, _, _) => name | Generic_Const (name, _, _) => name)
       (#parameters (function_generics projected)) = ["'a", "T", "N", "U"])
  val _ = require "lifetime projection" (length (function_lifetime_parameters projected) = 1)
  val _ = require "type/const descriptor identity"
    (map (fn Generic_Parameter (name, _, kind) => (name, kind)) (function_type_parameters projected) =
      [("T", Type_Parameter), ("N", Const_Parameter), ("U", Type_Parameter)])
  fun bound_name (Rust_Trait_Bound (path, _)) = space_implode "::" (map #1 path)
  val _ = require "inline/where bound order"
    (map (fn (name, bounds) => (name, map bound_name bounds)) (function_bounds projected) =
      [("T", ["A", "outer::B", "D", "E", "F"]), ("U", ["C"])])
  val _ = require "authored where entries stay separate"
    (map (fn Rust_Type_Predicate
        (Path_Type ([Rust_Type_Path_Segment (name, _, NONE, _)], _), _, _) => name
      | _ => error "unexpected projected predicate")
      (#where_clause (function_generics projected)) = ["U", "T", "T"])
  val _ = require "empty list stays authored"
    (String.isSubstring "Empty<>" (URust_Printer.string_of_function URust_Printer.serialized_options
      (parse ctxt "empty-preservation" "fn Empty<>() {}")))
  val members =
    "fn Free<T: Copy>(value: T) -> T where T: Marker { value }\n" ^
    "impl Counter {\n" ^
    "fn Value<T>(self, value: T) -> T { value }\n" ^
    "fn Mutable<const N: usize>(mut self) -> usize { 0 }\n" ^
    "fn Shared<'a, T>(&'a self, value: T) -> T where T: Copy { value }\n" ^
    "fn Unique<T>(&mut self, value: T) -> T { value }\n" ^
    "fn Typed<T>(self: Self, value: T) -> T { value }\n}"
  val parsed_chunk = chunk ctxt "generic-members" members
  fun check_chunk options =
    let val generated = URust_Printer.string_of_chunk options parsed_chunk
        val reparsed = chunk ctxt "generic-members-reparsed" generated
    in require "generic chunk/member roundtrip"
      (URust_Printer.tokens_of_chunk options parsed_chunk = URust_Printer.tokens_of_chunk options reparsed) end
  val _ = List.app check_chunk [URust_Printer.serialized_options, URust_Printer.human_options]
  val _ = List.app (fn envelope =>
    let val generated = URust_Printer.string_of_annotated_item URust_Printer.serialized_options envelope
        val reparsed = hd (chunk_items (chunk ctxt "generic-envelope-reparsed" generated))
    in require "generic envelope roundtrip"
      (URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options envelope =
       URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options reparsed) end)
      (chunk_items parsed_chunk)
in val _ = () end
\<close>

section\<open> Positioned unsupported forms \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val tests =
    [("lifetime-after-type", "lifetime parameters must be declared prior", "fn Bad<T, 'a>() {}", "'a", 0),
     ("lifetime-after-const", "lifetime parameters must be declared prior", "fn Bad<const N: usize, 'a>() {}", "'a", 0),
     ("type-default", "defaults on function generic parameters", "fn Bad<T = u8>() {}", "=", 0),
     ("const-default", "defaults on function generic parameters", "fn Bad<const N: usize = 3>() {}", "=", 0),
     ("default-block", "defaults on function generic parameters", "fn Bad<const N: usize = { 3 }>() {}", "=", 0),
     ("optional-inline", "optional trait bounds are not supported", "fn Bad<T: ?Sized>() {}", "?", 0),
     ("optional-where", "optional trait bounds are not supported", "fn Bad<T>() where T: ?Sized {}", "?", 0),
     ("lifetime-parameter-bound", "lifetime bounds are not supported", "fn Bad<'a: 'b>() {}", ":", 0),
     ("lifetime-parameter-plus-bounds", "lifetime bounds are not supported", "fn Bad<'a: 'b + 'c>() {}", ":", 0),
     ("fn-inline-bound", "generic trait bounds are not supported", "fn Bad<T: Fn<u8>>() {}", "<", 1),
     ("fn-where-bound", "generic trait bounds are not supported", "fn Bad<T>() where T: Fn<u8> {}", "<", 1),
     ("generic-inline-bound", "generic trait bounds are not supported", "fn Bad<T: Trait<u8>>() {}", "<", 1),
     ("generic-empty-bound", "generic trait bounds are not supported", "fn Bad<T: Trait<>>() {}", "<", 1),
     ("generic-associated-bound", "generic trait bounds are not supported", "fn Bad<T>() where T: outer::Trait<Item = u8> {}", "<", 1),
     ("const-colon-bound", "bounds on const parameters are not supported", "fn Bad<const N: usize: Trait>() {}", ":", 1),
     ("const-plus-bound", "bounds on const parameters are not supported", "fn Bad<const N: usize + Trait>() {}", "+", 0),
     ("const-u8", "urust_datatype: const parameters require usize", "fn Bad<const N: u8>() {}", "u8", 0),
     ("const-named-type", "urust_datatype: const parameters require usize", "fn Bad<const N: Length>() {}", "Length", 0),
     ("where-unknown", "where clauses may only bound this function's type parameters", "fn Bad<T>() where U: Trait {}", "U", 0),
     ("where-const", "where clauses may only bound this function's type parameters", "fn Bad<const N: usize>() where N: Trait {}", "N", 1),
     ("where-concrete", "where clauses may only bound this function's type parameters", "fn Bad<T>() where u8: Trait {}", "u8", 0),
     ("where-qualified", "where clauses may only bound this function's type parameters", "fn Bad<T>() where outer::T: Trait {}", "outer", 0),
     ("where-applied", "where clauses may only bound this function's type parameters", "fn Bad<T>() where T<u8>: Trait {}", "T", 1),
     ("where-reference", "where clauses may only bound this function's type parameters", "fn Bad<T>() where &T: Trait {}", "&", 0),
     ("legacy-parser-where", "where clauses may only bound this function's type parameters", "fn Where(value: u64) -> u64 where u64: Copy { value }", "u64", 2),
     ("legacy-command-where", "where clauses may only bound this function's type parameters", "fn WhereClause(x: u64) -> u64 where X: Y { x }", "X", 0)]
  val deferred =
    ["lifetime-parameter-bound", "lifetime-parameter-plus-bounds", "fn-inline-bound", "fn-where-bound",
     "generic-inline-bound", "generic-empty-bound", "generic-associated-bound", "const-u8",
     "const-named-type", "where-unknown", "where-const", "where-concrete", "where-qualified",
     "where-applied", "where-reference", "legacy-parser-where", "legacy-command-where"]
  val _ = List.app (rejects ctxt)
    (filter_out (fn (label, _, _, _, _) => member (op =) deferred label) tests)
  val _ = List.app (fn (label, expected, rust, needle, occurrence) =>
    if member (op =) deferred label then
      let
        val _ = roundtrip ctxt (label ^ "-retained") rust
        val (expected, needle, occurrence) =
          if label = "lifetime-parameter-bound" orelse label = "lifetime-parameter-plus-bounds"
          then ("undeclared lifetime \"'b\"", "'b", 0)
          else if label = "where-reference"
          then ("reference lifetime must be explicit in a where predicate", "&", 0)
          else if label = "where-const"
          then ("const parameters cannot be used as type where heads", needle, occurrence)
          else (expected, needle, occurrence)
        val text = "urust_fn [verbosity = 0] " ^ cartouche rust
        val diagnostic = failure label expected (fn () => run @{theory} label text)
        val _ = require (label ^ ": authoritative phase lost the original unsupported span")
          (hd (map position_range (message_positions diagnostic)) = range_of text needle occurrence)
      in () end
    else ()) tests
in val _ = () end
\<close>

section\<open> Declaration markup and duplicate locations \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val ctxt = Context_Position.set_visible true @{context}
  val text = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ fn Mark<'a, T: outer::Scale + Copy, const N: usize>(value: T) -> T where T: Marker { value }"
  val (function, captured) =
    Parser_Test_Reports.chunks (fn () => parse ctxt "generic-markup" text)
  val trees = maps YXML.parse_body captured
  val events = map (fn (name, props) =>
    (name, position_range (Position.of_properties props), props))
    (fold Parser_Test_Reports.collect_markup trees [])
  fun typing_texts range (XML.Elem ((name, props), body)) =
        (if name = Markup.typingN andalso position_range (Position.of_properties props) = range
         then [XML.content_of body] else []) @ maps (typing_texts range) body
    | typing_texts _ (XML.Text _) = []
  fun role name token occurrence =
    require ("missing " ^ name ^ " at " ^ token)
      (has_role events name (range_of text token occurrence))
  val _ = List.app (fn (token, occurrence) => role Markup.keyword1N token occurrence)
    [("fn", 0), ("const", 0), ("where", 0)]
  val _ = List.app (fn (token, occurrence) => role Markup.delimiterN token occurrence)
    [("<", 0), (">", 0), (",", 0), (",", 1), (":", 0), ("::", 0), ("(", 0), (")", 0), ("->", 0)]
  val _ = role Markup.operatorN "+" 0
  val _ = List.app (fn (token, occurrence) => role Markup.tfreeN token occurrence)
    [("'a", 0), ("T", 0), ("N", 0)]
  val _ = List.app (fn (token, occurrence) => role Markup.typingN token occurrence)
    [("'a", 0), ("T", 0), ("N", 0)]
  val _ = List.app (fn (token, descriptor) =>
    require ("missing native parameter tooltip at " ^ token)
      (member (op =) (maps (typing_texts (range_of text token 0)) trees) descriptor))
    [("T", "type parameter T"), ("N", "const parameter N")]
  val _ = List.app (fn token =>
    require ("syntax prematurely resolved bound " ^ token)
      (not (has_role events Markup.entityN (range_of text token 0)))) ["outer", "Scale", "Copy", "Marker"]
  val generic_layout = #layout (function_generics function)
  fun token_position token expected =
    require "generic source-layout token range"
      (exists (fn pos => position_range pos = expected) (source_token_positions generic_layout token))
  val _ = token_position (Keyword_Token "const") (range_of text "const" 0)
  val _ = token_position (Keyword_Token "where") (range_of text "where" 0)
  val _ = token_position Operator_Token (range_of text "+" 0)
  val first_bound = hd (#2 (hd (function_bounds function)))
  val _ = (case first_bound of Rust_Trait_Bound ([("outer", outer), ("Scale", scale)], layout) =>
      (require "qualified bound head exact symbol range" (position_range outer = range_of text "outer" 0);
       require "qualified bound tail exact symbol range" (position_range scale = range_of text "Scale" 0);
       require "qualified bound separator exact symbol range"
         (map position_range (source_token_positions layout (Delimiter_Token "::")) = [range_of text "::" 0]))
    | _ => error "qualified bound shape changed")
  val _ = require "symbol offsets do not count bytes"
    (#1 (range_of text "T" 0) < raw_index text "T" 0 + 1)
  val _ = List.app (fn (label, item, needle, occurrence) =>
    let val diagnostic = failure label "duplicate generic parameter" (fn () => parse ctxt label item)
        val positions = map position_range (message_positions diagnostic)
    in require (label ^ ": both duplicate declaration ranges")
      (positions = [range_of item needle occurrence, range_of item needle 0]) end)
    [("duplicate-types", "fn Bad<T, T>() {}", "T", 1),
     ("duplicate-consts", "fn Bad<const N: usize, const N: usize>() {}", "N", 1),
     ("duplicate-type-const", "fn Bad<T, const T: usize>() {}", "T", 1),
     ("duplicate-const-type", "fn Bad<const T: usize, T>() {}", "T", 1)]
in val _ = () end
\<close>

section\<open> Delivered compatibility \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val thy = @{theory}
  val hol_type = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun declaration declared item =
    "urust_fn [pp_test, verbosity = 0] generic_syntax_failure " ^
    (if declared then ":: " ^ cartouche hol_type ^ " " else "") ^ cartouche item
  val _ = ignore (run thy "lifetime-only-command"
    (declaration false "fn Borrow<'a>(value: &'a mut u8) -> &'a mut u8 { value }"))
  val _ = List.app (fn (label, expected, item) => ignore (failure label expected
    (fn () => run thy label (declaration false item))))
    [("lifetime-undeclared", "undeclared lifetime", "fn Borrow(value: &'a mut u8) -> u8 { 0 }"),
     ("lifetime-duplicate", "duplicate lifetime parameter", "fn Borrow<'a, 'a>(value: &'a mut u8) -> u8 { 0 }"),
     ("lifetime-static", "cannot be declared as a lifetime parameter", "fn Borrow<'static>(value: u8) -> u8 { 0 }"),
     ("lifetime-anonymous", "cannot be declared as a lifetime parameter", "fn Borrow<'_>(value: u8) -> u8 { 0 }"),
     ("inferred-impl-trait", "Rust impl Trait types", "fn Retained(value: impl Marker) -> u8 { 0 }")]
  val retained = run thy "declared-literal-types"
    (declaration true "fn Retained(value: impl Marker) -> impl Marker { value }") |> Toplevel.context_of
  val _ = require "declared HOL type retained impl Trait bypass"
    (is_some (Parser_Test_Calls.lookup retained "Retained"))
  val ctxt = Proof_Context.init_global thy
  fun datatype_of text = the (URust_Parser.parse_datatype_source ctxt (source "datatype-generic-control" text))
  fun alias_of text = the (URust_Parser.parse_type_alias_source ctxt (source "alias-generic-control" text))
  val datatype_item = datatype_of "struct Cell<T, const N: usize> { value: T, bytes: [u8; N] }"
  val alias_item = alias_of "type CellAlias<T, const N: usize> = Cell<T, N>;"
  val _ = (case datatype_item of Datatype_Header (parameters, _, _, _) =>
    require "datatype descriptor identity"
      (map (fn Generic_Parameter (name, _, kind) => (name, kind)) parameters =
        [("T", Type_Parameter), ("N", Const_Parameter)]) | _ => error "datatype header changed")
  val _ = require "alias descriptor identity"
    (map (fn Generic_Parameter (name, _, kind) => (name, kind)) (type_alias_parameter_descriptors alias_item) =
      [("T", Type_Parameter), ("N", Const_Parameter)])
  val _ = List.app (fn options =>
    (require "datatype generic printer compatibility"
      (URust_Printer.tokens_of_datatype options datatype_item =
       URust_Printer.tokens_of_datatype options (datatype_of (URust_Printer.string_of_datatype options datatype_item)));
     require "alias generic printer compatibility"
      (URust_Printer.tokens_of_type_alias options alias_item =
       URust_Printer.tokens_of_type_alias options (alias_of (URust_Printer.string_of_type_alias options alias_item)))))
    [URust_Printer.serialized_options, URust_Printer.human_options]
  val _ = ignore (failure "datatype-bounds-control" "syntax error"
    (fn () => datatype_of "struct Cell<T: Copy> { value: T }"))
  val _ = ignore (failure "datatype-optional-bound-control" "unexpected input \"?\""
    (fn () => datatype_of "struct Cell<T: ?Sized> { value: T }"))
  val _ = ignore (failure "alias-optional-bound-control" "unexpected input \"?\""
    (fn () => alias_of "type CellAlias<T: ?Sized> = T;"))
  val _ = ignore (failure "impl-plus-target-control" "unexpected input \"+\""
    (fn () => chunk ctxt "impl-plus-target-control" "impl SyntaxCounter + Marker {}"))
  val _ = List.app (fn (label, token, text) => ignore (failure label
    ("unexpected input " ^ quote token) (fn () => parse ctxt label text)))
    [("retained-numeric-argument-plus", "+", "fn Numeric(value: Cell<u8, 4+4>) {}"),
     ("retained-optional-type", "?", "fn Optional(value: ?Sized) {}")]
  val _ = ignore (failure "extracted-numeric-argument-plus" "unexpected input \"+\""
    (fn () => URust_Parser.parse_generic_argument_source ctxt
      (source "extracted-numeric-argument-plus" "4+4")))
in val _ = () end
\<close>

section\<open> Native result channels and callback restoration \<close>

text\<open>
Native datatype generation keeps its synchronous ordinary and urgent results quiet. These
unfiltered captures preserve every callback's channel and chunks, check exact predecessor
identities, and exercise nested scopes, independent physical threads, child joins and interrupts.
Semantic channels remain audible, including native aliases to ordinary output.
\<close>

ML\<open>
(* Direct native result channel probes against the canonical A20 owner. *)
structure Generic_Syntax_Native_Output =
struct
  val require = Generic_Syntax_Test.require

  val owned =
    [("writeln", Private_Output.writeln_fn),
     ("urgent", Private_Output.writeln_urgent_fn),
     ("state", Private_Output.state_fn),
     ("tracing", Private_Output.tracing_fn),
     ("system", Private_Output.system_message_fn)]

  val simple_channels = owned @
    [("information", Private_Output.information_fn),
     ("warning", Private_Output.warning_fn),
     ("legacy", Private_Output.legacy_fn),
     ("status", Private_Output.status_fn),
     ("report", Private_Output.report_fn)]

  fun with_callbacks settings action =
    fold_rev (fn (reference, callback) => fn body => fn () =>
      Unsynchronized.setmp reference callback body ()) settings action ()

  fun saved_callbacks () = map (fn (_, reference) => !reference) owned
  fun same_callbacks saved =
    forall (fn (callback, (_, reference)) => PolyML.pointerEq (callback, !reference))
      (saved ~~ owned)

  (* Complete result/report chunks are retained without source/thread/message filtering.
     Native lifecycle callbacks stay installed during source-generation matrices. *)
  fun capture_with semantic_probe action =
    let
      val events = Synchronized.var "generic syntax native output" ([]: (string * string list) list)
      fun collect channel chunks = Synchronized.change events (fn prior => prior @ [(channel, chunks)])
      val probe: unit Thread_Data.var = Thread_Data.var ()
      fun owns_probe () = is_some (Thread_Data.get probe)
      val captured_channels = ["writeln", "urgent", "report"]
      val channels = if semantic_probe then simple_channels
        else filter (fn (channel, _) => member (op =) captured_channels channel) simple_channels
      fun callback channel original chunks =
        if member (op =) captured_channels channel orelse owns_probe ()
        then collect channel chunks else original chunks
      val settings = map (fn (channel, reference) =>
        (reference, callback channel (!reference))) channels
      val original_error = !Private_Output.error_message_fn
      val original_result = !Private_Output.result_fn
      val original_protocol = !Private_Output.protocol_message_fn
      fun body () = Print_Mode.with_modes [Print_Mode.PIDE] (fn () => Exn.capture action ()) ()
      (* Only the explicit synchronous semantic probe uses these collectors. Unmarked native
         threads retain exact status/protocol properties, bodies and chunks. *)
      fun semantic_body () =
        Thread_Data.setmp probe (SOME ()) (fn () =>
          Unsynchronized.setmp Private_Output.error_message_fn
            (fn (serial, chunks) =>
              if owns_probe () then collect "error" chunks else original_error (serial, chunks))
            (fn () =>
              Unsynchronized.setmp Private_Output.result_fn
                (fn props => fn chunks =>
                  if owns_probe () then collect "result" chunks else original_result props chunks)
                (fn () =>
                  Unsynchronized.setmp Private_Output.protocol_message_fn
                    (fn props => fn bodies =>
                      if owns_probe () then collect "protocol" (map YXML.string_of_body bodies)
                      else original_protocol props bodies) body ()) ()) ()) ()
      val result = Parser_Test_Report_Lock.run (fn () =>
        with_callbacks settings (if semantic_probe then semantic_body else body))
    in (result, Synchronized.value events) end

  fun capture action = capture_with false action
  fun capture_semantics action = capture_with true action

  fun chunks channel events = maps #2 (filter (fn (name, _) => name = channel) events)
  fun ordinary events = chunks "writeln" events @ chunks "urgent" events
  fun trees channel events = maps YXML.parse_body (chunks channel events)

  (* Physical native threads make overlap independent of the configured future worker count. *)
  fun fork label action =
    let
      val result = Single_Assignment.var label
      val thread = Isabelle_Thread.fork (Isabelle_Thread.params label)
        (fn () => Single_Assignment.assign result (Exn.capture action ()))
    in fn () => (Isabelle_Thread.join thread; Exn.release (Single_Assignment.await result)) end

  val quiet = URust_Report_Transaction.quiet_native_results
end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Native_Output
  exception Scope_Failure
  fun hidden label =
    (Output.writelns [label, "-ordinary"]; Output.writelns_urgent [label, "-urgent"])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val attributes = Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ())
      val normal = quiet (fn () =>
        (require "native result action retains original interrupt attributes"
           (Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ()) = attributes);
         hidden "normal"; 37))
      val _ = require "normal native result value and callback identities"
        (normal = 37 andalso same_callbacks callbacks)
      val failure = Exn.capture (fn () => quiet (fn () => (hidden "failure"; raise Scope_Failure))) ()
      val _ = require "native result exception and callback identities"
        ((case failure of Exn.Exn Scope_Failure => true | _ => false) andalso same_callbacks callbacks)
      val interrupt = Exn.capture (fn () =>
        quiet (fn () => (hidden "interrupt"; Isabelle_Thread.raise_interrupt ()))) ()
      val _ = require "native result interrupt and callback identities"
        ((case interrupt of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso
          same_callbacks callbacks)
      val _ = quiet (fn () =>
        let
          val callbacks = saved_callbacks ()
          val nested = Exn.capture (fn () =>
            quiet (fn () => (hidden "nested-failure"; raise Scope_Failure))) ()
          val _ = require "same-thread nested failure retains outer callback installation"
            ((case nested of Exn.Exn Scope_Failure => true | _ => false) andalso
              same_callbacks callbacks)
        in hidden "outer-after-nested-failure" end)
      val _ = require "nested failure restores exact enclosing callbacks" (same_callbacks callbacks)
      val _ = Output.writelns ["after", "normal-exception-interrupt"]
      val _ = Output.writelns_urgent ["after", "urgent"]
    in () end)
  val _ = Exn.release result
  val _ = require "native result scope suppresses only owned ordinary and urgent chunks"
    (events = [("writeln", ["after", "normal-exception-interrupt"]),
      ("urgent", ["after", "urgent"])])

  val foreign_probe: unit Thread_Data.var = Thread_Data.var ()
  val foreign_status = Synchronized.var "foreign native status chunks" ([]: string list)
  val foreign_protocol =
    Synchronized.var "foreign native protocol payload" (NONE: (Properties.T * XML.body list) option)
  val status_callback = !Private_Output.status_fn
  val protocol_callback = !Private_Output.protocol_message_fn
  val foreign_properties = [("function", "foreign-output-probe"), ("probe", "native")]
  val foreign_bodies = [[XML.Text "foreign-protocol"]]
  (* The controlled predecessor consumes only the explicitly tagged worker's synthetic payload.
     All real lifecycle traffic keeps its original native sink. *)
  val (result, events) = Native_Output_Ownership.with_temporary_hooks (fn () =>
    Unsynchronized.setmp Private_Output.status_fn
      (fn chunks => if is_some (Thread_Data.get foreign_probe)
        then Synchronized.change foreign_status (fn _ => chunks) else status_callback chunks)
      (fn () =>
        Unsynchronized.setmp Private_Output.protocol_message_fn
          (fn props => fn bodies => if is_some (Thread_Data.get foreign_probe)
            then Synchronized.change foreign_protocol (fn _ => SOME (props, bodies))
            else protocol_callback props bodies)
          (fn () => capture_semantics (fn () =>
            let
              val callbacks = saved_callbacks ()
              val untouched = drop 5 simple_channels
                |> map (fn (_, reference) => (!reference, reference))
              val error_callback = !Private_Output.error_message_fn
              val result_callback = !Private_Output.result_fn
              val protocol_callback = !Private_Output.protocol_message_fn
              val _ = quiet (fn () =>
                (require "other semantic channel refs are untouched"
                   (forall (fn (callback, reference) => PolyML.pointerEq (callback, !reference)) untouched
                    andalso PolyML.pointerEq (error_callback, !Private_Output.error_message_fn)
                    andalso PolyML.pointerEq (result_callback, !Private_Output.result_fn)
                    andalso PolyML.pointerEq (protocol_callback, !Private_Output.protocol_message_fn));
                 hidden "semantic-control";
                 Output.state ["state", "-chunks"];
                 Output.tracing "tracing";
                 Output.system_message "system";
                 Output.information "information";
                 Output.warning "warning";
                 Output.legacy_feature "legacy";
                 Output.error_message "error";
                 Output.status ["status", "-chunks"];
                 Output.report ["report", "-chunks"];
                 Output.result [] ["result", "-chunks"];
                 Output.protocol_message [] [[XML.Text "protocol"]]))
              val foreign = fork "foreign native lifecycle traffic" (fn () =>
                Thread_Data.setmp foreign_probe (SOME ()) (fn () =>
                  (Output.status ["foreign-status", "-chunks"];
                   Output.protocol_message foreign_properties foreign_bodies)) ())
              val _ = foreign ()
            in require "semantic channels restore exact five callbacks" (same_callbacks callbacks) end)) ()) ())
  val _ = Exn.release result
  val _ = require "semantic probe forwards unrelated native status/protocol without changing payloads"
    (Synchronized.value foreign_status = ["foreign-status", "-chunks"] andalso
      Synchronized.value foreign_protocol = SOME (foreign_properties, foreign_bodies))
  val _ = require "all semantic channels remain audible with their chunks and channels"
    (events =
      [("state", ["state", "-chunks"]), ("tracing", ["tracing"]), ("system", ["system"]),
       ("information", ["information"]), ("warning", ["warning"]),
       ("legacy", ["Legacy feature! legacy"]), ("error", ["error"]),
       ("status", ["status", "-chunks"]), ("report", ["report", "-chunks"]),
       ("result", ["result", "-chunks"]), ("protocol", ["protocol"])])

  val (result, events) = capture (fn () =>
    with_callbacks
      [(Private_Output.writeln_urgent_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.state_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.tracing_fn, fn chunks => !Private_Output.writeln_fn chunks),
       (Private_Output.system_message_fn, fn chunks => !Private_Output.writeln_fn chunks)]
      (fn () =>
        let
          val callbacks = saved_callbacks ()
          val _ = quiet (fn () =>
            (hidden "standalone-alias-hidden";
             Output.state ["alias-state", "-chunks"];
             Output.tracing "alias-tracing";
             Output.system_message "alias-system";
             hidden "after-alias-hidden"))
          val _ = require "standalone aliases restore exact callback objects" (same_callbacks callbacks)
        in Output.writelns_urgent ["outside", "-urgent-alias"] end))
  val _ = Exn.release result
  val _ = require "standalone semantic aliases clear only the physical quiet marker"
    (events = [("writeln", ["alias-state", "-chunks"]),
      ("writeln", ["alias-tracing"]), ("writeln", ["alias-system"]),
      ("writeln", ["outside", "-urgent-alias"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val ready_a = Single_Assignment.var "quiet owner A entered"
      val ready_b = Single_Assignment.var "quiet owner B entered"
      val release_a = Single_Assignment.var "quiet owner A leave"
      val release_b = Single_Assignment.var "quiet owner B leave"
      fun owner label ready release = fork label (fn () => quiet (fn () =>
        (hidden (label ^ "-first"); Single_Assignment.assign ready ();
         Single_Assignment.await release; hidden (label ^ "-last"))))
      val join_a = owner "scope-A" ready_a release_a
      val _ = Single_Assignment.await ready_a
      val installed = saved_callbacks ()
      val join_b = owner "scope-B" ready_b release_b
      val _ = Single_Assignment.await ready_b
      val overlap_reuses_installation = same_callbacks installed
      val unrelated = fork "unrelated physical output" (fn () =>
        (Output.writelns ["foreign", "-ordinary"];
         Output.writelns_urgent ["foreign", "-urgent"]))
      val _ = unrelated ()
      val future = Future.fork (fn () =>
        (Output.writelns ["future", "-ordinary"]; Output.writelns_urgent ["future", "-urgent"]))
      val _ = Future.join future
      val _ = Single_Assignment.assign release_a ()
      val _ = join_a ()
      val first_leave_retains_installation = same_callbacks installed
      val _ = Output.writelns ["between", "-owners"]
      val _ = Single_Assignment.assign release_b ()
      val _ = join_b ()
      val _ = require "overlapping physical owners share and retain one installation"
        (overlap_reuses_installation andalso first_leave_retains_installation)
      val _ = require "last physical owner restores exact callbacks" (same_callbacks callbacks)
    in Output.writelns_urgent ["after", "-owners"] end)
  val _ = Exn.release result
  val _ = require "unrelated threads and futures preserve ordinary/urgent channel chunks"
    (events = [("writeln", ["foreign", "-ordinary"]), ("urgent", ["foreign", "-urgent"]),
      ("writeln", ["future", "-ordinary"]), ("urgent", ["future", "-urgent"]),
      ("writeln", ["between", "-owners"]), ("urgent", ["after", "-owners"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val _ = quiet (fn () =>
        let
          val installed = saved_callbacks ()
          val child = fork "explicit child quiet scope" (fn () =>
            quiet (fn () => hidden "child-helper"))
          val _ = child ()
          val _ = require "parent join retains its installation" (same_callbacks installed)
        in hidden "parent-after-child-join" end)
    in require "parent child join restores callbacks without an action lock"
      (same_callbacks callbacks) end)
  val _ = Exn.release result
  val _ = require "explicit child helpers suppress their own synchronous results" (null events)

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val entered = Single_Assignment.var "interruptible quiet scope entered"
      val blocked = Single_Assignment.var "interruptible quiet scope blocker"
      val finished = Single_Assignment.var "interruptible quiet scope result"
      val thread = Isabelle_Thread.fork
        (Isabelle_Thread.interrupts (Isabelle_Thread.params "interruptible native result scope"))
        (fn () => Single_Assignment.assign finished
          (Exn.capture (fn () => quiet (fn () =>
            (hidden "actual-interrupt"; Single_Assignment.assign entered ();
             Single_Assignment.await blocked))) ()))
      val _ = Single_Assignment.await entered
      val _ = Isabelle_Thread.interrupt_thread thread
      val _ = Isabelle_Thread.join thread
      val interrupted = Single_Assignment.await finished
      val _ = require "native interrupt leaves scope before propagating the original interrupt"
        ((case interrupted of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso
          same_callbacks callbacks)
    in Output.writelns ["after", "-actual-interrupt"] end)
  val _ = Exn.release result
  val _ = require "interrupt cleanup restores a live enclosing collector"
    (events = [("writeln", ["after", "-actual-interrupt"])])
in val _ = () end
\<close>

section\<open> Native hook publication \<close>

text\<open>
The canonical neutral owner coordinates temporary result and printer-report callbacks with
permanent tool publication. Native barriers exercise draining, admission and interruption;
publication from its own temporary scope and recursive publication reject before mutation.
\<close>

ML_val\<open>
local
  open Generic_Syntax_Test Generic_Syntax_Native_Output
  exception Publication_Failure
  val temporary = Native_Output_Ownership.with_temporary_hooks
  val publish = Native_Output_Ownership.publish_hooks

  val _ = require "Parser_Utils uses the canonical imported native result operation"
    (PolyML.pointerEq (URust_Report_Transaction.quiet_native_results,
      Native_Output_Ownership.quiet_results))

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val normal = publish (fn () =>
        (require "publication callback masks interrupts for its complete update"
          (Thread_Attributes.convert_attributes (Thread_Attributes.get_attributes ()) =
            Thread_Attributes.convert_attributes Thread_Attributes.no_interrupts);
         43))
      val _ = require "publication preserves its original result" (normal = 43)
      val failed = Exn.capture (fn () => publish (fn () => raise Publication_Failure)) ()
      val _ = require "publication preserves its original exception"
        (case failed of Exn.Exn Publication_Failure => true | _ => false)
      val _ = temporary (fn () => quiet (fn () => Output.writeln "quiet after publication failure"))
      val mutated = Unsynchronized.ref false
      val _ = temporary (fn () =>
        ignore (failure "same-thread publication" "publication inside temporary hooks" (fn () =>
          publish (fn () => mutated := true))))
      val _ = publish (fn () =>
        (ignore (failure "recursive publication" "recursive publication" (fn () =>
           publish (fn () => mutated := true)));
         ignore (failure "temporary scope in publication" "temporary hooks inside publication" (fn () =>
           temporary (fn () => mutated := true)))))
      val _ = require "reentrant publication rejects before callback mutation"
        (not (!mutated) andalso same_callbacks callbacks)
      val _ = temporary (fn () => temporary (fn () => ()))
    in Output.writelns ["after", "-publication-failure-and-rejections"] end)
  val _ = Exn.release result
  val _ = require "publication failure and rejected recursion leave live predecessor routing"
    (events = [("writeln", ["after", "-publication-failure-and-rejections"])])

  val (result, events) = capture (fn () =>
    let
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val publication_count = Synchronized.var "publication executes once" 0
      val forwarded = Synchronized.var "published callback forwarding" 0
      val ready_quiet = Single_Assignment.var "publication quiet scope entered"
      val child_go = Single_Assignment.var "pending publisher child go"
      val child_done = Single_Assignment.var "pending publisher child done"
      val quiet_release = Single_Assignment.var "publication quiet scope release"
      val ready_report = Single_Assignment.var "publication report capture entered"
      val report_release = Single_Assignment.var "publication report capture release"
      val attempted = Single_Assignment.var "publication attempt"
      val published = Single_Assignment.var "publication complete"
      val installed = Single_Assignment.var "published callback objects"
      val quiet_join = fork "publication held quiet scope" (fn () => quiet (fn () =>
        (Output.writeln "held quiet output";
         Single_Assignment.assign ready_quiet ();
         Single_Assignment.await child_go;
         let
           val child = fork "quiet child while publication waits" (fn () =>
             quiet (fn () => Output.writeln_urgent "held child output"))
         in child () end;
         Single_Assignment.assign child_done ();
         Single_Assignment.await quiet_release)))
      val _ = Single_Assignment.await ready_quiet
      val function = parse (Context_Position.set_visible true @{context})
        "publication-report-function" "fn Plain() {}"
      val report_join = fork "publication held native printer capture" (fn () =>
        Print_Mode.with_modes [Print_Mode.PIDE] (fn () =>
          ignore (URust_Printer_Output.pretty_human_function_with_reparse
            (fn source =>
              (Single_Assignment.assign ready_report ();
               Single_Assignment.await report_release;
               ignore (URust_Parser.parse_function_source
                 (Context_Position.set_visible true @{context}) source)))
            function)) ())
      val _ = Single_Assignment.await ready_report
      fun wrap callback chunks =
        (Synchronized.change forwarded (fn count => count + 1); callback chunks)
      val publication_join = fork "publication waits for both hook scopes" (fn () =>
        (Single_Assignment.assign attempted ();
         publish (fn () =>
           let
             val _ = require "publication captures restored ordinary/semantic and report sinks"
               (same_callbacks callbacks andalso
                PolyML.pointerEq (!Private_Output.report_fn, report_callback))
             val replacements = map wrap callbacks
             val replacement_report = wrap report_callback
             val _ = List.app (fn (callback, (_, reference)) => reference := callback)
               (replacements ~~ owned)
             val _ = Private_Output.report_fn := replacement_report
             val _ = Synchronized.change publication_count (fn count => count + 1)
             val _ = Single_Assignment.assign installed (replacements, replacement_report)
           in () end);
         Single_Assignment.assign published ()))
      val _ = Single_Assignment.await attempted
      (* Necessary child admission remains open while a publisher drains its parent. *)
      val _ = Single_Assignment.assign child_go ()
      val _ = Single_Assignment.await child_done
      val waited_for_both = is_none (Single_Assignment.peek published)
      val _ = Single_Assignment.assign quiet_release ()
      val _ = quiet_join ()
      val waited_for_report = is_none (Single_Assignment.peek published)
      val _ = Single_Assignment.assign report_release ()
      val _ = report_join ()
      val _ = publication_join ()
      val (replacement_callbacks, replacement_report) = Single_Assignment.await installed
      val stable = same_callbacks replacement_callbacks andalso
        PolyML.pointerEq (!Private_Output.report_fn, replacement_report)
      val _ = quiet (fn () => Output.writeln "quiet after completed publication")
      val stable_after_quiet = same_callbacks replacement_callbacks
      val _ = Output.writelns ["published", "-ordinary"]
      val _ = Output.writelns_urgent ["published", "-urgent"]
      val _ = Output.report [YXML.string_of_body [XML.Text "published-report"]]
      (* Restore the enclosing fixture before propagating any assertion failure. *)
      val _ = publish (fn () =>
        (List.app (fn (callback, (_, reference)) => reference := callback) (callbacks ~~ owned);
         Private_Output.report_fn := report_callback))
      val _ = require "publication waits for both result and actual printer-report scopes"
        (waited_for_both andalso waited_for_report)
      val _ = require "publication resumes once without later temporary restoration clobbering it"
        (Synchronized.value publication_count = 1 andalso stable andalso stable_after_quiet)
      val _ = require "published callbacks preserve forwarding after native quieting"
        (Synchronized.value forwarded = 3)
      val _ = require "publication fixture restores exact original callbacks"
        (same_callbacks callbacks andalso PolyML.pointerEq (!Private_Output.report_fn, report_callback))
    in () end)
  val _ = Exn.release result
  val _ = require "published ordinary and urgent chunks remain exact"
    (chunks "writeln" events = ["published", "-ordinary"] andalso
      chunks "urgent" events = ["published", "-urgent"])
  val _ = require "published reports remain audible" (member (op =) (chunks "report" events) "published-report")

  val (result, events) = capture (fn () =>
    let
      val entered = Single_Assignment.var "exclusive publication entered"
      val release = Single_Assignment.var "exclusive publication release"
      val attempted = Single_Assignment.var "temporary entry during publication"
      val complete = Single_Assignment.var "exclusive publication complete"
      val publication_join = fork "publication excludes temporary admission" (fn () =>
        publish (fn () =>
          (Single_Assignment.assign entered (); Single_Assignment.await release;
           Single_Assignment.assign complete ())))
      val _ = Single_Assignment.await entered
      val temporary_join = fork "temporary scope waits for publication" (fn () =>
        (Single_Assignment.assign attempted ();
         temporary (fn () =>
           require "temporary entry begins after complete publication"
             (is_some (Single_Assignment.peek complete)))))
      val _ = Single_Assignment.await attempted
      val _ = Single_Assignment.assign release ()
      val _ = publication_join ()
      val _ = temporary_join ()
    in () end)
  val _ = Exn.release result
  val _ = require "publication admission probe emits no channel payload" (null events)

  val (result, events) = capture (fn () =>
    let
      val ready = Single_Assignment.var "interrupt publication quiet scope entered"
      val release = Single_Assignment.var "interrupt publication quiet scope release"
      val attempted = Single_Assignment.var "interruptible publication attempted"
      val complete = Single_Assignment.var "interruptible publication result"
      val mutated = Unsynchronized.ref false
      val quiet_join = fork "interrupt publication held quiet scope" (fn () =>
        quiet (fn () => (Single_Assignment.assign ready (); Single_Assignment.await release)))
      val _ = Single_Assignment.await ready
      val thread = Isabelle_Thread.fork
        (Isabelle_Thread.interrupts (Isabelle_Thread.params "interruptible publication wait"))
        (fn () => Single_Assignment.assign complete
          (Exn.capture (fn () =>
            (Single_Assignment.assign attempted (); publish (fn () => mutated := true))) ()))
      val _ = Single_Assignment.await attempted
      val _ = Isabelle_Thread.interrupt_thread thread
      val _ = Isabelle_Thread.join thread
      val interrupted = Single_Assignment.await complete
      val _ = Single_Assignment.assign release ()
      val _ = quiet_join ()
      val _ = require "publication wait is interruptible and captures no temporary callback"
        ((case interrupted of Exn.Exn exn => Exn.is_interrupt exn | _ => false) andalso not (!mutated))
      val _ = publish (fn () => ())
      val _ = temporary (fn () => ())
    in () end)
  val _ = Exn.release result
  val _ = require "interrupted publication wait leaves no channel mutation" (null events)
in val _ = () end
\<close>

section\<open> Complete datatype output atomicity \<close>

text\<open>
Successful structs and native HOL enums retain authored verbosity, definition reports and
all generated class artifacts. Failed chunks release no earlier successful declaration reports
or ordinary or urgent output. A failed member may report only its own exact binder declarations.
Configuration tests distinguish absent entries from explicit values through both merge orders,
and nested targets retain each original setting. The malformed nongeneric body supplies an
independent durable failure and recovery control; generic prefixes are audited in Signatures.
\<close>

ML\<open>
structure Generic_Syntax_Output_Atomicity =
struct
  open Generic_Syntax_Test Generic_Syntax_Native_Output

  fun run_with interactive thy label text =
    fold (Toplevel.command_exception interactive)
      (Outer_Syntax.parse_text thy (K thy) (start label) text) (Toplevel.make_state (SOME thy))

  fun continue interactive state label text =
    let val thy = Toplevel.theory_of state in
      fold (Toplevel.command_exception interactive)
        (Outer_Syntax.parse_text thy (K thy) (start label) text) state
    end

  fun snapshot ctxt =
    (Parser_Test_Calls.dump ctxt |> map (fn (name, entry) =>
        (name, #hol_term entry, Position.properties_of (#reg_pos entry))),
     URust_Item_Scope.dump_types ctxt |> map (fn entry =>
        (URust_Item_Scope.type_rust_name entry, URust_Item_Scope.type_hol_name entry,
         Position.properties_of (URust_Item_Scope.type_position entry))),
     URust_Item_Scope.dump_constructors ctxt |> map (fn entry =>
        (URust_Item_Scope.constructor_rust_path entry, URust_Item_Scope.constructor_term entry,
         URust_Item_Scope.constructor_fields entry,
         Position.properties_of (URust_Item_Scope.constructor_position entry))),
     Micro_Rust_Names.Declaration_Owners.get (Context.Proof ctxt) |> Symtab.dest
       |> map (fn (name, owners) => (name, map (fn ({kind, pos}: Micro_Rust_Names.declaration_owner) =>
           (kind, Position.properties_of pos)) owners)),
     Micro_Rust_Names.dump ctxt |> map (fn (kind, name, entry) =>
       (kind, name, #hol_term entry, #source_const entry, #serial entry,
        Position.properties_of (#reg_pos entry))),
     URust_Type_Mappings.dump ctxt |> map (fn (name, entry) =>
       (name, URust_Type_Mappings.entry_template entry, URust_Type_Mappings.entry_arities entry,
        URust_Type_Mappings.entry_parameter_sorts entry, URust_Type_Mappings.entry_identity entry)),
     #constants (Consts.dest (Proof_Context.consts_of ctxt)))

  fun definition_reports events =
    fold Parser_Test_Reports.collect_markup (trees "report" events) []
    |> filter (fn (name, props) => name = Markup.entityN andalso
        is_some (Properties.get props Markup.defN))
  fun declaration_reports events =
    definition_reports events
    |> filter (fn (_, props) => Properties.get props Markup.kindN <> SOME "urust_var")
  fun binder_reports events =
    definition_reports events
    |> filter (fn (_, props) => Properties.get props Markup.kindN = SOME "urust_var")
  fun callback_count channel events = length (filter (fn (name, _) => name = channel) events)
  fun exact_binders label text expected events =
    let
      val actual = binder_reports events |> map (fn (_, props) =>
        (the_default "" (Properties.get props Markup.kindN),
         the_default "" (Properties.get props Markup.nameN),
         the_default "" (Position.file_of (Position.of_properties props)),
         position_range (Position.of_properties props)))
        |> sort (string_ord o apply2 #2)
      val wanted = map (fn (name, occurrence) =>
        ("urust_var", name, label, range_of text name occurrence)) expected
        |> sort (string_ord o apply2 #2)
    in require (label ^ ": exact failed-member binder kind/name/file/source range changed")
      (actual = wanted) end

  fun command verbosity body =
    "urust [verbosity = " ^ string_of_int verbosity ^ "] " ^ cartouche ("\n" ^ body ^ "\n")

  val holder = "struct SyntaxOutputHolder { value: u8 }"
  val choice = "\<omega>" ^ cartouche "backend = \"hol\"" ^
    "\nenum SyntaxOutputChoice { Empty, Byte(u8) }"
  val member_source = "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { value } }"

  fun setting NONE thy = thy
    | setting (SOME value) thy = Config.put_global Proof_Display.show_results value thy
  fun setting_name NONE = "absent"
    | setting_name (SOME true) = "true"
    | setting_name (SOME false) = "false"

  fun native_artifacts ctxt rust_name =
    let
      val entry = the (URust_Type_Mappings.lookup ctxt rust_name)
      val T = URust_Type_Mappings.entry_template entry
      val thy = Proof_Context.theory_of ctxt
    in
      require (rust_name ^ ": native class artifacts were retained")
        (Sign.of_sort thy (T, @{sort typerep}) andalso
         Sign.of_sort thy (T, @{sort term_of}) andalso
         Sign.of_sort thy (T, @{sort equal}) andalso
         Sign.of_sort thy (T, @{sort random}))
    end

  fun target_settings ctxt =
    let
      val settings = Unsynchronized.ref ([]: (int * bool) list)
      val _ = Local_Theory.map_contexts (fn depth => fn context =>
        (settings := (depth, Config.get context Proof_Display.show_results) :: !settings; context)) ctxt
    in sort (int_ord o apply2 #1) (!settings) end
end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  fun success (setting_value, interactive, verbosity, rust_name, body) =
    let
      val configured = setting setting_value thy
      val label = "native-success-" ^ rust_name ^ "-" ^ string_of_int verbosity ^ "-" ^
        Bool.toString interactive ^ "-" ^ setting_name setting_value
      val (result, events) = capture (fn () => run_with interactive configured label
        (command verbosity body))
      val state = Exn.release result
      val ctxt = Toplevel.context_of state
      val enabled = interactive orelse Config.get_global configured Proof_Display.show_results
      val _ = require (label ^ ": authored verbosity output changed")
        ((not (null (ordinary events))) = (enabled andalso verbosity > 0))
      val _ = require (label ^ ": native backend result output escaped")
        (callback_count "writeln" events = (if enabled andalso verbosity > 0 then 1 else 0) andalso
          null (chunks "urgent" events))
      val _ = require (label ^ ": authored definitions were not released")
        (not (null (declaration_reports events)))
      val _ = require (label ^ ": type registry lost its authored item")
        (is_some (URust_Item_Scope.lookup_type ctxt rust_name))
      val _ = native_artifacts ctxt rust_name
      val _ = require (label ^ ": native global show_results value changed")
        (Config.get_global (Toplevel.theory_of state) Proof_Display.show_results =
          Config.get_global configured Proof_Display.show_results)
    in () end
  val _ = List.app success
    (maps (fn setting_value => maps (fn interactive => maps (fn verbosity =>
      [(setting_value, interactive, verbosity, "SyntaxOutputHolder", holder),
       (setting_value, interactive, verbosity, "SyntaxOutputChoice", choice)]) [0, 1, 2])
      [false, true]) [NONE, SOME true, SOME false])
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  val ctxt = Proof_Context.init_global thy
  val initial_snapshot = snapshot ctxt
  val failures =
    [("nongeneric-body", holder ^ "\nimpl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
       "missing_output_value")]
  fun failing (setting_value, verbosity, (kind, body, expected)) =
    let
      val configured = setting setting_value thy
      val label = "complete-atomicity-" ^ kind ^ "-" ^ string_of_int verbosity ^ "-" ^
        setting_name setting_value
      val (result, events) = capture (fn () => run_with true configured label (command verbosity body))
      val message =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": wrong diagnostic") (String.isSubstring expected message)
      val _ = require (label ^ ": earlier successful datatype output escaped") (null (ordinary events))
      val _ = require (label ^ ": earlier successful definition reports escaped")
        (null (declaration_reports events))
      val _ = exact_binders label (command verbosity body)
        (if kind = "nongeneric-body" then [("self", 0), ("value", 1)] else []) events
      val _ = require (label ^ ": original registry or theory artifacts changed")
        (snapshot (Proof_Context.init_global configured) = initial_snapshot)
      val (recovery, recovery_events) = capture (fn () =>
        run_with true configured (label ^ "-recovery") (command verbosity (holder ^ "\n" ^ member_source)))
      val recovered = Exn.release recovery |> Toplevel.context_of
      val _ = require (label ^ ": failure leaked artifacts or blocked a later valid declaration")
        (is_some (Parser_Test_Calls.lookup recovered "SyntaxOutputHolder::member"))
      val _ = native_artifacts recovered "SyntaxOutputHolder"
      val _ = require (label ^ ": recovery lost authored definition reports")
        (not (null (declaration_reports recovery_events)))
    in () end
  val _ = List.app failing
    (maps (fn setting_value => maps (fn verbosity =>
      map (fn failure => (setting_value, verbosity, failure)) failures) [0, 1, 2])
      [NONE, SOME true, SOME false])
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val base = Theory.end_theory @{theory}
  fun fresh label parents = Theory.begin_theory (label, Position.none) parents
  fun finished label configure = fresh label [base] |> configure |> Theory.end_theory
  fun flag_name NONE = "Absent" | flag_name (SOME true) = "True" | flag_name (SOME false) = "False"
  fun generated flag =
    let
      val label = "SyntaxOutputConfig" ^ flag_name flag
      val parent = fresh label [base] |> setting flag
      val (result, _) = capture (fn () => run_with false parent label (command 0 holder))
    in Exn.release result |> Toplevel.theory_of |> Theory.end_theory end
  fun merge label parents = fresh label parents |> Theory.end_theory
  fun value thy = Config.get_global thy Proof_Display.show_results
  val _ = List.app (fn flag =>
    let
      val generated = generated flag
      val pristine = finished ("SyntaxOutputPristine" ^ flag_name flag) (setting flag)
      val _ = List.app (fn other =>
        let
          val suffix = flag_name flag ^ Bool.toString other
          val opposite = finished ("SyntaxOutputOpposite" ^ suffix) (setting (SOME other))
          val original_first = merge ("SyntaxOutputControlFirst" ^ suffix) [pristine, opposite]
          val generated_first = merge ("SyntaxOutputGeneratedFirst" ^ suffix) [generated, opposite]
          val original_last = merge ("SyntaxOutputControlLast" ^ suffix) [opposite, pristine]
          val generated_last = merge ("SyntaxOutputGeneratedLast" ^ suffix) [opposite, generated]
          val _ = require (suffix ^ ": generation changed first-parent configuration semantics")
            (value generated_first = value original_first)
          val _ = require (suffix ^ ": generation changed last-parent configuration semantics")
            (value generated_last = value original_last)
          val _ = if is_none flag then
            require (suffix ^ ": absence control contains a show_results entry")
              (value original_first = other andalso value original_last = other) else ()
        in () end) [true, false]
    in () end) [NONE, SOME true, SOME false]
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Syntax_Output_Atomicity
  val thy = @{theory}
  val locale = run_with false thy "native-output-locale"
    "locale SyntaxOutputScope = fixes output_seed :: nat"
  val entered = continue false locale "native-output-nested-enter"
    "context SyntaxOutputScope begin\ndeclare [[show_results = true]]\n\
    \context begin\ndeclare [[show_results = false]]"
  val before_context = Toplevel.context_of entered
  val before_settings = target_settings before_context
  val before_global = Config.get_global (Toplevel.theory_of entered) Proof_Display.show_results
  val (success, events) = capture (fn () => continue true entered "native-output-nested-datatype"
    (command 2 holder))
  val declared = Exn.release success
  val declared_context = Toplevel.context_of declared
  val _ = require "nested datatype restores every original target show_results setting"
    (length before_settings >= 2 andalso target_settings declared_context = before_settings)
  val _ = require "nested datatype preserves global show_results"
    (Config.get_global (Toplevel.theory_of declared) Proof_Display.show_results = before_global)
  val _ = require "nested datatype keeps authored output and definition markup"
    (callback_count "writeln" events = 1 andalso null (chunks "urgent" events) andalso
      not (null (declaration_reports events)))
  val failures =
    [("nongeneric-body", "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
       "missing_output_value", [("self", 0), ("value", 1)])]
  val _ = List.app (fn (kind, member, expected, binders) =>
    let
      val label = "native-output-nested-failure-" ^ kind
      val text = command 2 (holder ^ "\n" ^ member)
      val (failure, failed_events) = capture (fn () => continue true entered label text)
      val _ = require (label ^ ": failure retains its diagnostic")
        (case failure of Exn.Exn exn => String.isSubstring expected (Runtime.exn_message exn)
         | _ => false)
      val _ = require (label ^ ": earlier successful output or definition markup escaped")
        (null (ordinary failed_events) andalso null (declaration_reports failed_events))
      val _ = exact_binders label text binders failed_events
      val _ = require (label ^ ": failure preserves all original target settings")
        (target_settings (Toplevel.context_of entered) = before_settings)
    in () end) failures
in val _ = () end
\<close>

chapter\<open> Signatures \<close>

text\<open>
These checks preserve the exact sources, wrappers and controls of the temporary U2 guards.
Successful generic declarations carry ordered source schemes; genuine body failures and late
chunk failures retain the original output, report, namespace, settings and recovery controls.
The two A14 legacy Function ML sources remain separate from the newer Syntax rows.
\<close>

ML\<open>
structure Generic_Signature_Test =
struct
  open Generic_Syntax_Output_Atomicity
  fun scheme ctxt backend =
    (case URust_Command.generic_scheme ctxt backend of
       SOME parameters => parameters | NONE => error "generic signature audit: missing scheme")
  (* Exact migrated names may already have an imported ordinary backend. Select the newly
     generated generic source for metadata checks while retaining every ordinary registration. *)
  fun entry ctxt key =
    Parser_Test_Calls.entries ctxt key
    |> filter (fn backend =>
      is_some (URust_Type_Mappings.generic_scheme_for_source ctxt (#serial backend)))
    |> the_single
  fun entry_scheme ctxt (backend: Micro_Rust_Names.entry) =
    (case URust_Type_Mappings.generic_scheme_for_source ctxt (#serial backend) of
       SOME parameters => parameters | NONE => error "generic signature audit: missing source scheme")
  fun require_scope_closed label ctxt =
    require (label ^ ": generic scope escaped the declaration")
      (is_none (URust_Type_Mappings.generic_scope ctxt))
  fun scheme_snapshot ctxt =
    (Parser_Test_Calls.dump ctxt |> map (fn (key, backend) =>
       (key, URust_Type_Mappings.generic_scheme_for_source ctxt (#serial backend))),
     Inttab.dest (Micro_Rust_Names.Method_Only_Registrations.get (Context.Proof ctxt)),
     Option.map (fn {parameters}: URust_Type_Mappings.generic_scope =>
       map (fn {rust, pos, kind, hol, bounds, ...}: URust_Type_Mappings.generic_parameter =>
         (rust, Position.properties_of pos, kind, hol, bounds)) parameters)
       (URust_Type_Mappings.generic_scope ctxt))
  fun parameter_definitions events =
    filter (fn (name, _, props) => name = Markup.entityN andalso
      Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
      is_some (Properties.get props Markup.defN)) events
  fun first_parameter label text token events =
    require (label ^ ": exact first generic declaration range changed")
      (exists (fn (_, range, props) =>
        range = range_of text token 0 andalso Properties.get props Markup.nameN = SOME token)
        (parameter_definitions events))
  fun header ctxt label item = parse ctxt label item |> URust_AST.function_type_parameters
  fun check_header label descriptors
      (parameters: URust_Type_Mappings.generic_scheme_parameter list) =
    require (label ^ ": ordered source parameter kinds/names changed")
      (map (fn URust_AST.Generic_Parameter (name, _, kind) => (name, kind)) descriptors =
       map (fn {rust, kind, ...} => (rust, kind)) parameters)
  fun body_failure item =
    hd (space_explode "{" item) ^ "{ missing_generic_value }"
end
\<close>

section\<open> Exact migrated declarations and receiver behavior \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val hol_type = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun declaration declared item =
    "urust_fn [pp_test, verbosity = 0] generic_syntax_failure " ^
    (if declared then ":: " ^ cartouche hol_type ^ " " else "") ^ cartouche item
  fun accepted (label, declared, item, token) =
    let
      val text = declaration declared item
      val (state, events) = reports (fn () => run thy label text)
      val ctxt = Toplevel.context_of state
      val function = parse ctxt label item
      val backend = entry ctxt (#1 (URust_AST.function_name function))
      val parameters = scheme ctxt (#hol_term backend)
      val _ = check_header label (URust_AST.function_type_parameters function) parameters
      val _ = first_parameter label text token events
      val _ = require_scope_closed label ctxt
      val _ = require (label ^ ": named HOL declaration missing")
        (can (Proof_Context.read_const {proper = true, strict = true} ctxt)
          "generic_syntax_failure")
      val _ = if declared then
        require (label ^ ": literal declared-HOL bypass changed")
          (Sign.typ_equiv (Proof_Context.theory_of ctxt)
            (fastype_of (#hol_term backend), Logic.varifyT_global (Syntax.read_typ ctxt hol_type)))
        else ()
      val original = Proof_Context.init_global thy
      val failed_text = declaration declared (body_failure item)
      val (diagnostic, failed_events) = reports (fn () =>
        failure label "missing_generic_value" (fn () => run thy label failed_text))
      val _ = require (label ^ ": genuine failure has no source range")
        (not (null (message_positions diagnostic)))
      val _ = require (label ^ ": failed declaration emitted definition markup")
        (not (exists (fn (name, _, props) => name = Markup.entityN andalso
          is_some (Properties.get props Markup.defN) andalso
          Properties.get props Markup.kindN <> SOME "urust_var") failed_events))
      val _ = require (label ^ ": failure changed original namespace/schemes")
        (snapshot original = snapshot (Proof_Context.init_global thy) andalso
         scheme_snapshot original = scheme_snapshot (Proof_Context.init_global thy))
      val recovered = run thy (label ^ "-recovery")
        (declaration false "fn Generic(value: u8) -> u8 { value }") |> Toplevel.context_of
      val _ = require (label ^ ": command did not recover")
        (is_some (Parser_Test_Calls.lookup recovered "Generic"))
    in () end
  val _ = List.app accepted
    [("guard-inferred-type", false, "fn Generic<T>(x: T) -> T { x }", "T"),
     ("guard-declared-type", true, "fn Generic<T>(value: impl Marker) -> impl Marker { value }", "T"),
     ("guard-inferred-const", false, "fn Sized<const N: usize>(value: [u8; N]) -> usize { 0 }", "N"),
     ("guard-declared-const", true, "fn Sized<const N: usize>(value: Unknown) -> Unknown { value }", "N"),
     ("guard-inferred-mixed", false, "fn Mix<'a, const N: usize, T>(value: T) -> T { value }", "N"),
     ("guard-declared-mixed", true, "fn Mix<'a, T, const N: usize>(value: Unknown) -> Unknown { value }", "T"),
     ("legacy-reference-mixed-generics", false, "fn BadReference<'a, T>(value: &'a mut u8) -> u8 { 0 }", "T")]

  val model = run thy "generic-member-model"
    ("urust_datatype [verbosity = 0] " ^ cartouche "struct SyntaxCounter { value: u8 }")
    |> Toplevel.theory_of
  val chunks =
    [("chunk-generic-function", "fn Generic<T>(value: T) -> T { value }", "T"),
     ("impl-generic-value", "impl SyntaxCounter { fn Value<T>(self, value: T) -> T { value } }", "T"),
     ("impl-generic-mutable", "impl SyntaxCounter { fn Value<T>(mut self, value: T) -> T { value } }", "T"),
     ("impl-generic-shared", "impl SyntaxCounter { fn Value<'a, T>(&'a self, value: T) -> T { value } }", "T"),
     ("impl-generic-unique", "impl SyntaxCounter { fn Value<const N: usize>(&mut self) -> usize { 0 } }", "N"),
     ("impl-generic-typed", "impl SyntaxCounter { fn Value<T>(self: Self, value: T) -> T { value } }", "T")]
  val _ = List.app (fn (label, item, token) =>
    let
      val text = "urust [pp_test, verbosity = 0] " ^ cartouche item
      val original = Proof_Context.init_global model
    in
      if label = "impl-generic-shared" then
        let
          val (diagnostic, events) = reports (fn () =>
            failure label "shared Rust references" (fn () => run model label text))
          val _ = require (label ^ ": exact shared receiver range changed")
            (hd (map position_range (message_positions diagnostic)) = range_of text "&'a self" 0)
          val _ = require (label ^ ": failed receiver installed definition markup")
            (null (parameter_definitions events))
          val _ = require (label ^ ": failed receiver mutated namespace")
            (snapshot original = snapshot (Proof_Context.init_global model))
        in () end
      else
        let
          val (state, events) = reports (fn () => run model label text)
          val ctxt = Toplevel.context_of state
          val key = if label = "chunk-generic-function" then "Generic" else "SyntaxCounter::Value"
          val backend = entry ctxt key
          val parameters = scheme ctxt (#hol_term backend)
          val _ = first_parameter label text token events
          val _ = require (label ^ ": source scheme missing") (map #rust parameters = [token])
          val _ = require_scope_closed label ctxt
          val _ = if key = "Generic" then () else
            let
              val method = entry ctxt "Value"
              val owners = Micro_Rust_Names.associated_functions ctxt key
              val _ = require (label ^ ": associated owner Self/identity lost")
                (length owners = 1 andalso #identity (hd owners) = #serial backend andalso
                 Sign.typ_equiv (Proof_Context.theory_of ctxt)
                   (#self_type (hd owners), URust_Type_Mappings.entry_template
                     (the (URust_Type_Mappings.lookup ctxt "SyntaxCounter"))))
              val _ = require (label ^ ": bare receiver entry lost method-only provenance")
                (Micro_Rust_Names.is_method_only_serial (Context.Proof ctxt) (#serial method) andalso
                 scheme ctxt (#hol_term method) = parameters)
            in () end
        in () end
    end) chunks

  val _ = List.app (fn (label, text, key) =>
    let
      val original = Proof_Context.init_global thy
      val completed = run thy label text |> Toplevel.context_of
      val _ = require (label ^ ": exact legacy positive did not install its scheme")
        (map #rust (scheme completed (#hol_term (entry completed key))) = ["T"])
      val _ = require_scope_closed label completed
      val _ = require (label ^ ": original namespace changed")
        (snapshot original = snapshot (Proof_Context.init_global thy))
    in () end)
    [("rust-function-generics", "urust_fn invalid_function_item " ^
       cartouche "fn Generic<T>(x: T) -> T { x }", "Generic"),
     ("reference-mixed-generics", "urust_fn  reference_failure " ^
       cartouche "fn BadReference<'a, T>(value: &'a mut u8) -> u8 { 0 }", "BadReference")]
in val _ = () end
\<close>

section\<open> Native twin artifacts and ordered generic metadata \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val ctxt = @{context}
  val thy = @{theory}
  fun constant name = Proof_Context.read_const {proper = true, strict = false} ctxt name
  val twins =
    [("signature_identity", "SignatureIdentity"), ("signature_array", "SignatureArray"),
     ("signature_mixed", "SignatureMixed"), ("signature_borrow", "SignatureBorrow"),
     ("signature_pointer", "SignaturePointer"), ("signature_mapped", "SignatureMapped"),
     ("signature_channels", "SignatureChannels"), ("signature_bounds", "SignatureBounds"),
     ("signature_unused", "SignatureUnused"), ("signature_disabled", "SignatureDisabled"),
     ("signature_application", "SignatureApplication")]
  val _ = List.app (fn (name, rust) =>
    let
      val backend = constant name
      val twin = constant (name ^ "_twin")
      val _ = require (name ^ ": complete native HOL types differ")
        (Sign.typ_equiv thy (fastype_of backend, fastype_of twin))
      val parameters = scheme ctxt backend
      val _ = require (name ^ ": source generic metadata missing") (not (null parameters))
      val _ = require (name ^ ": escape twin unexpectedly acquired source generic metadata")
        (is_none (URust_Command.generic_scheme ctxt twin))
      val theorem = Proof_Context.get_thm ctxt (name ^ "_def")
      val twin_theorem = Proof_Context.get_thm ctxt (name ^ "_twin_def")
      val rhs_type = fastype_of (snd (Logic.dest_equals (Thm.prop_of theorem)))
      val twin_rhs_type = fastype_of (snd (Logic.dest_equals (Thm.prop_of twin_theorem)))
      val _ = require (name ^ ": definition theorem has different type variables/sorts")
        (Sign.typ_equiv thy (rhs_type, twin_rhs_type))
      val _ = if name = "signature_disabled" then
        require (name ^ ": opt-out retained a callable")
          (null (Parser_Test_Calls.entries ctxt rust) andalso
           null (Parser_Test_Calls.entries ctxt (rust ^ "Twin")))
        else require (name ^ ": ordinary automatic registration differs")
          (length (Parser_Test_Calls.entries ctxt rust) =
             length (Parser_Test_Calls.entries ctxt (rust ^ "Twin")) andalso
           Micro_Rust_Names.is_automatic_serial (Context.Proof ctxt) (#serial (entry ctxt rust)))
    in () end) twins
  val _ = require "array parameter finalized to len"
    (map #hol (scheme ctxt (constant "signature_array")) = [("'n", @{sort len})])
  val _ = require "mixed source order omits only the lifetime"
    (map (fn {rust, kind, hol, ...} => (rust, kind, hol))
      (scheme ctxt (constant "signature_mixed")) =
      [("T", URust_AST.Type_Parameter, ("'t", @{sort type})),
       ("N", URust_AST.Const_Parameter, ("'n", @{sort len}))])
  val _ = require "bounds retain union with override name"
    (map #hol (scheme ctxt (constant "signature_bounds")) =
      [("'element", @{sort "{trait_scale, ord}"})])
  val _ = require "unused ordered parameters retain their sort requirements"
    (map #hol (scheme ctxt (constant "signature_unused")) =
      [("'t", @{sort ord}), ("'n", @{sort len0})])
  val locale_backend = #hol_term (entry ctxt "SignatureLocale")
  val _ = require "interpreted applied backend retains ordered parameter"
    (map #hol (scheme ctxt locale_backend) = [("'t", @{sort type})])
  val caller = TVar (("caller", 70000), @{sort type})
  val candidate = Logic.incr_indexes ([], 60000) locale_backend
  val instantiated = the (URust_Type_Mappings.instantiate_generic_scheme ctxt
    locale_backend candidate [(caller, Position.none)])
  val _ = require "locale helper preserves high caller variable and captured seed"
    (hd (binder_types (fastype_of instantiated)) = caller andalso
     snd (Term.strip_comb instantiated) = snd (Term.strip_comb candidate))
  val abbreviation = entry ctxt "SignatureAbbrev"
  val specialized = the (URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt
    (#serial abbreviation) (#hol_term abbreviation) [(@{typ nat}, Position.none)])
  val _ = require "input abbreviation expanded backend shares the source parameter"
    (hd (binder_types (fastype_of specialized)) = @{typ nat})
  val other_abbreviation = entry ctxt "SignatureAbbrevOther"
  val _ = require "equal expanded named abbreviations retain separate ordered/unused metadata"
    (map #rust (entry_scheme ctxt abbreviation) = ["T"] andalso
     map #rust (entry_scheme ctxt other_abbreviation) = ["T", "U"] andalso
     map #hol (entry_scheme ctxt other_abbreviation) =
       [("'t", @{sort type}), ("'u", @{sort ord})])
  val _ = ignore (failure "ambiguous-expanded-abbreviation-query" "ambiguous generic scheme query"
    (fn () => URust_Command.generic_scheme ctxt (#hol_term abbreviation)))
  val _ = require "native named abbreviation identity selects its own metadata"
    (map #rust (scheme ctxt (constant "signature_abbrev")) = ["T"] andalso
     map #rust (scheme ctxt (constant "signature_abbrev_other")) = ["T", "U"])
  val _ = require "disabled named abbreviation retains its ordered unused metadata without callables"
    (map #rust (scheme ctxt (constant "signature_abbrev_disabled")) = ["T", "U"] andalso
     map #hol (scheme ctxt (constant "signature_abbrev_disabled")) =
       [("'t", @{sort type}), ("'u", @{sort ord})] andalso
     is_none (URust_Command.generic_scheme ctxt (constant "signature_abbrev_disabled_twin")) andalso
     null (Parser_Test_Calls.entries ctxt "SignatureAbbrevDisabled") andalso
     null (Parser_Test_Calls.entries ctxt "SignatureAbbrevDisabledTwin"))
  val _ = require_scope_closed "all signature examples" ctxt
in val _ = () end
\<close>

section\<open> Native code and specification artifacts \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val ctxt = @{context}
  val thy = @{theory}
  fun full name = Proof_Context.intern_const ctxt name
  fun normalize own = Term.map_aterms
    (fn Const (name, T) => Const (if name = own then "signature_twin" else name, T)
      | term => term)
  fun equations name =
    let val (_, equations) = Code.equations_of_cert thy (Code.get_cert ctxt [] (full name))
    in these equations |> map_filter
      (fn (_, (SOME theorem, _)) => SOME (Thm.prop_of theorem |> normalize (full name))
        | _ => NONE) end
  fun specification name =
    let val theorem = Proof_Context.get_thm ctxt (name ^ "_def") in
      exists (fn {rough_classification, rules, ...} =>
        Spec_Rules.is_equational rough_classification andalso
        exists (fn rule => Thm.eq_thm_prop (rule, theorem)) rules) (Spec_Rules.get ctxt)
    end
  val _ = List.app (fn name =>
    let val twin = name ^ "_twin"
        val code = equations name
        val twin_code = equations twin
        val _ = require (name ^ ": native code equations differ from the escape twin")
          (not (null code) andalso eq_list Term.aconv_untyped (code, twin_code))
        val _ = require (name ^ ": native equational specification artifacts differ")
          (specification name = specification twin)
        val _ = require (name ^ ": raw definition artifacts differ")
          (can (Thm.axiom thy) (full name ^ "_def_raw") =
           can (Thm.axiom thy) (full twin ^ "_def_raw"))
    in () end)
    ["signature_identity", "signature_array", "signature_mixed", "signature_borrow",
     "signature_pointer", "signature_mapped", "signature_channels", "signature_bounds",
     "signature_unused", "signature_disabled", "signature_application"]
in val _ = () end
\<close>

section\<open> Named abbreviation locale provenance, replay and merge \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure Types = URust_Type_Mappings
  val ctxt = @{context}
  val thy = @{theory}
  val entries = Parser_Test_Calls.entries ctxt "SignatureAbbrevLocale"
  val source = #serial (hd entries)
  val expected = [{rust = "T", kind = URust_AST.Type_Parameter, hol = ("'t", @{sort type})},
    {rust = "U", kind = URust_AST.Type_Parameter, hol = ("'u", @{sort ord})}]
  val _ = require "three fixed type/value interpretations retain one original source serial"
    (length entries = 3 andalso forall (fn (entry: Micro_Rust_Names.entry) =>
      #serial entry = source andalso entry_scheme ctxt entry = expected andalso
      is_none (#source_const entry)) entries)
  val caller = TVar (("locale_caller", 90000), @{sort type})
  val arguments = [(caller, Position.none), (@{typ nat}, Position.none)]
  val _ = List.app (fn (entry: Micro_Rust_Names.entry) =>
    let val candidate = Logic.incr_indexes ([], 80000) (#hol_term entry)
        val instance = the (Types.instantiate_generic_scheme_for_source ctxt source candidate arguments)
        val _ = require "source-specific locale helper preserves caller and complete captured backend"
          (hd (binder_types (fastype_of instance)) = caller andalso
           Term.aconv_untyped (instance, candidate))
        val _ = require "unused interpreted abbreviation parameter still requires ord"
          (is_none (Types.instantiate_generic_scheme_for_source ctxt source candidate
            [(caller, Position.none), (TVar (("unused_weak", 90001), @{sort type}), Position.none)]))
    in () end) entries
  val unrelated = Free ("unrelated_locale_backend", fastype_of (#hol_term (hd entries)))
  val _ = require "source helper rejects an unrelated complete candidate"
    (is_none (Types.instantiate_generic_scheme_for_source ctxt source unrelated arguments))
  val named = Proof_Context.read_const {proper = true, strict = false} ctxt
    "signature_abbrev_seed.signature_abbrev_locale"
  val _ = require "native locale abbreviation identity retains ordered unused metadata"
    (Types.generic_scheme ctxt named = SOME expected)
  val replay = run thy "signature-abbrev-interpretation-replay"
    ("interpretation signature_abbrev_again: signature_abbrev_seed " ^
      cartouche "3 :: nat" ^ " by unfold_locales") |> Toplevel.context_of
  val replay_entries = Parser_Test_Calls.entries replay "SignatureAbbrevLocale"
  val _ = require "native interpretation replay deduplicates identical complete backends"
    (length replay_entries = 3 andalso forall (fn (entry: Micro_Rust_Names.entry) =>
      #serial entry = source andalso entry_scheme replay entry = expected) replay_entries)
  val _ = List.app (fn (entry: Micro_Rust_Names.entry) =>
    require "interpretation replay preserves candidate results"
      (Types.instantiate_generic_scheme_for_source replay source (#hol_term entry) arguments =
       Types.instantiate_generic_scheme_for_source ctxt source (#hol_term entry) arguments)) entries

  val base = Theory.end_theory thy
  fun branch label header =
    Theory.begin_theory (label, Position.none) [base]
    |> (fn theory => run theory label
      ("urust_fn [abbrev, verbosity = 0] " ^
        cartouche ("fn SignatureMerge" ^ header ^ "(value: T) -> T { value }")))
    |> Toplevel.theory_of |> Theory.end_theory
  val left = branch "SignatureAbbrevMergeLeft" "<T>"
  val right = branch "SignatureAbbrevMergeRight" "<T, U: Ordered>"
  fun merged label parents = Theory.begin_theory (label, Position.none) parents
    |> Proof_Context.init_global
  val merged_ctxt = merged "SignatureAbbrevMerged" [left, right]
  val reverse_ctxt = merged "SignatureAbbrevMergedReverse" [right, left]
  fun sources context = Parser_Test_Calls.dump context
    |> filter (fn (key, _) => key = "SignatureMerge") |> map snd
  fun metadata context = sources context |> map (fn (entry: Micro_Rust_Names.entry) =>
    (#serial entry, entry_scheme context entry)) |> sort (int_ord o apply2 #1)
  val merged_entries = sources merged_ctxt
  val _ = require "native merge retains both equal-RHS named abbreviation sources"
    (length merged_entries = 2 andalso metadata merged_ctxt = metadata reverse_ctxt andalso
     sort int_ord (map (length o entry_scheme merged_ctxt) merged_entries) = [1, 2])
  val _ = List.app (fn (name, rust) =>
    let val identity = Proof_Context.read_const {proper = true, strict = false} merged_ctxt name in
      require "merged native named identity selects its own ordered header"
        (map #rust (scheme merged_ctxt identity) = rust)
    end)
    [("SignatureAbbrevMergeLeft.signature_merge", ["T"]),
     ("SignatureAbbrevMergeRight.signature_merge", ["T", "U"])]
  val _ = ignore (failure "merged-expanded-abbreviation-query" "ambiguous generic scheme query"
    (fn () => Types.generic_scheme merged_ctxt (#hol_term (hd merged_entries))))
  val _ = List.app (fn (entry: Micro_Rust_Names.entry) =>
    let val parameters = entry_scheme merged_ctxt entry
        val arguments = (caller, Position.none) ::
          map (K (@{typ nat}, Position.none)) (tl parameters)
        val instance = the (Types.instantiate_generic_scheme_for_source merged_ctxt
          (#serial entry) (#hol_term entry) arguments)
    in require "native merged source provenance aligns its own full backend/witnesses"
      (hd (binder_types (fastype_of instance)) = caller) end) merged_entries
in val _ = () end
\<close>

section\<open> Positioned navigation, final-sort tooltips and generic manifests \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val original = @{context}
  fun plain chunks = XML.content_of (maps YXML.parse_body chunks)
    |> Symbol.explode |> filter_out Symbol.is_control |> implode
  fun spaces text = space_implode " " (String.tokens Char.isSpace text)
  fun typings range (XML.Elem ((name, props), body)) =
        (if name = Markup.typingN andalso position_range (Position.of_properties props) = range
         then [plain [XML.content_of body]] else []) @ maps (typings range) body
    | typings _ (XML.Text _) = []
  fun parameter_entities property name markup = markup |> map_filter (fn (element, props) =>
    if element = Markup.entityN andalso
      Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
      Properties.get props Markup.nameN = SOME name
    then Properties.get props property else NONE)
  val item = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ " ^
    "fn SignatureMarkup<T: Scale, const N: usize>(value: [T; N]) -> [T; N] where T: Ordered + Scale { value }"
  fun declaration verbosity =
    "urust_fn [verbosity = " ^ string_of_int verbosity ^
    ", hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'element::ord" ^
    "]] signature_markup " ^ cartouche item
  val _ = List.app (fn verbosity =>
    let val label = "signature-markup-" ^ string_of_int verbosity
        val text = declaration verbosity
        val callbacks = saved_callbacks ()
        val report_callback = !Private_Output.report_fn
        val (result, events) = capture (fn () => run thy label text)
        val completed = Exn.release result |> Toplevel.context_of
        val _ = require "signature capture restores exact owned and report callbacks"
          (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
        val markup = fold Parser_Test_Reports.collect_markup (trees "report" events) []
        val parameter_reports = parameter_definitions
          (map (fn (name, props) => (name, position_range (Position.of_properties props), props)) markup)
        val _ = require "generic declaration entities retain their exact positioned Rust headers"
          (length parameter_reports = 2 andalso
           forall (fn (name, occurrence) =>
             exists (fn (_, range, props) => range = range_of text name occurrence andalso
               Properties.get props Markup.nameN = SOME name) parameter_reports)
             [("T", 1), ("N", 0)])
        val _ = List.app (fn (name, occurrences) =>
          let val definitions = parameter_entities Markup.defN name markup
              val references = parameter_entities Markup.refN name markup
              val _ = require "parameter uses navigate to one original declaration entity"
                (length definitions = 1 andalso length references = length occurrences andalso
                 forall (fn identity => identity = hd definitions) references)
              val _ = List.app (fn occurrence =>
                require "generic reference retained its exact source range"
                  (exists (fn (element, props) => element = Markup.entityN andalso
                    Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
                    Properties.get props Markup.nameN = SOME name andalso
                    is_some (Properties.get props Markup.refN) andalso
                    position_range (Position.of_properties props) = range_of text name occurrence) markup))
                occurrences
          in () end) [("T", [2, 3, 4]), ("N", [1, 2])]
        val final = map #hol (entry_scheme completed (entry completed "SignatureMarkup"))
        val _ = require "manifest metadata retains override, bound union and final array length sort"
          (final = [("'element", @{sort "{ord, trait_scale}"}), ("'n", @{sort len})])
        val _ = List.app (fn ((name, occurrence), hol) =>
          require "labelled declaration tooltip retains its Rust name and final strengthened type"
            (Library.member (op =) (maps (typings (range_of text name occurrence)) (trees "report" events))
              (plain [name ^ " = " ^
                Syntax.string_of_typ (Config.put show_sorts true completed) (TFree hol)])))
          ([("T", 1), ("N", 0)] ~~ final)
        val _ = List.app (fn (name, occurrence, descriptor) =>
          require "final declaration typing preserves the separate U2 parameter descriptor"
            (Library.member (op =)
              (maps (typings (range_of text name occurrence)) (trees "report" events)) descriptor))
          [("T", 1, "type parameter T"), ("N", 0, "const parameter N")]
        val _ = List.app (fn (name, occurrences, hol) =>
          List.app (fn occurrence =>
            require "labelled parameter-use tooltip retains the final strengthened type and sort"
              (Library.member (op =)
                (maps (typings (range_of text name occurrence)) (trees "report" events))
                (plain [name ^ " = " ^
                  Syntax.string_of_typ (Config.put show_sorts true completed) (TFree hol)])))
            occurrences) [("T", [2, 3, 4], hd final), ("N", [1, 2], nth final 1)]
        val bounds = URust_AST.function_bounds (parse original label item) |> maps snd
        val ((resolved, bound_events)) = reports (fn () =>
          map (URust_Trait_Mappings.resolve_bound original) bounds)
        val reference_markup = map (fn (name, _, props) => (name, props)) bound_events
        val _ = require "inline/where bounds retain canonical declared Rust mapping keys"
          (map #path resolved = ["Scale", "Ordered", "Scale"])
        val _ = List.app (fn name =>
          require "inline/where bounds navigate through their original native trait entities"
            (Parser_Trait_Test.entities Markup.refN name markup =
             Parser_Trait_Test.entities Markup.refN name reference_markup)) ["Scale", "Ordered"]
        val report_text = plain (chunks "report" events)
        val _ = require "bound tooltips retain declared paths and mapped sorts"
          (String.isSubstring "Scale = trait_scale" report_text andalso
           String.isSubstring "Ordered = ord" report_text)
        val manifest = spaces (plain (ordinary events))
        val expected = spaces (plain ["generics T \<mapsto> " ^
          Syntax.string_of_typ (Config.put show_sorts true completed) (TFree (hd final)) ^
          ", const N \<mapsto> " ^
          Syntax.string_of_typ (Config.put show_sorts true completed) (TFree (nth final 1))])
        val _ = require "generic manifest follows verbosity and final ordered source metadata"
          (String.isSubstring expected manifest = (verbosity > 0))
        val backend = entry completed "SignatureMarkup"
        val (query_result, query_events) = capture (fn () =>
          (URust_Command.generic_scheme completed (#hol_term backend),
           URust_Type_Mappings.generic_scheme_for_source completed (#serial backend)))
        val (term_metadata, source_metadata) = Exn.release query_result
        val _ = require "scheme queries are report/output free and agree on an unambiguous source"
          (null query_events andalso term_metadata = source_metadata andalso
           term_metadata = SOME (entry_scheme completed backend))
        val _ = require_scope_closed label completed
    in () end) [0, 1, 2]
  val unused_text = "urust_fn [verbosity = 1] " ^
    cartouche "fn SignatureUnusedManifest<T: Ordered, const N: usize>() {}"
  val (unused_result, unused_events) = capture (fn () => run thy "signature-unused-manifest" unused_text)
  val unused_ctxt = Exn.release unused_result |> Toplevel.context_of
  val unused_parameters = entry_scheme unused_ctxt (entry unused_ctxt "SignatureUnusedManifest")
  val _ = require "unused manifest metadata retains each positioned source parameter and sort"
    (map #hol unused_parameters = [("'t", @{sort ord}), ("'n", @{sort len0})])
  val unused_manifest = spaces (plain (ordinary unused_events))
  val unused_expected = spaces (plain ["generics T \<mapsto> " ^
    Syntax.string_of_typ (Config.put show_sorts true unused_ctxt) (TFree ("'t", @{sort ord})) ^
    ", const N \<mapsto> " ^
    Syntax.string_of_typ (Config.put show_sorts true unused_ctxt) (TFree ("'n", @{sort len0}))])
  val _ = require "unused parameters retain their ordered generic manifest after HOL erasure"
    (String.isSubstring unused_expected unused_manifest)
  val callbacks = saved_callbacks ()
  val report_callback = !Private_Output.report_fn
  val (failed, _) = capture (fn () => error "signature callback restoration probe")
  val _ = require "capture restores exact callback pointers after an exception"
    ((case failed of Exn.Exn (ERROR _) => true | _ => false) andalso same_callbacks callbacks andalso
     PolyML.pointerEq (report_callback, !Private_Output.report_fn))
in val _ = () end
\<close>

section\<open> Positioned errors, isolation and final scope \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val ctxt = Proof_Context.init_global thy
  val original_snapshot = snapshot ctxt
  val before_schemes = scheme_snapshot ctxt
  fun declaration options item =
    "urust_fn [" ^ options ^ "verbosity = 0] signature_error " ^ cartouche item
  val identity = "fn SignatureError<T>(value: T) -> T { value }"
  val overrides =
    [("unknown-override", "unknown parameter override",
       "hol_type_parameters = [\"Missing\" \<rightarrow> " ^ cartouche "'x" ^ "], ", identity),
     ("duplicate-override", "duplicate parameter override",
       "hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'x" ^
         ", \"T\" \<rightarrow> " ^ cartouche "'y" ^ "], ", identity),
     ("nonvariable-override", "parameter overrides require a HOL type variable",
       "hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "nat" ^ "], ", identity),
     ("duplicate-hol", "HOL parameter names must be distinct",
       "hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'same" ^
         ", \"U\" \<rightarrow> " ^ cartouche "'same" ^ "], ",
       "fn SignatureError<T, U>(value: T) -> T { value }"),
     ("default-hol-collision", "HOL parameter names must be distinct", "",
       "fn SignatureError<T, t>(value: T) -> T { value }"),
     ("unregistered-inline-bound", "unregistered Rust trait", "",
       "fn SignatureError<T: MissingTrait>(value: T) -> T { value }"),
     ("unregistered-where-bound", "unregistered Rust trait", "",
       "fn SignatureError<T>(value: T) -> T where T: MissingTrait { value }"),
     ("body-only-type", "urust: generic parameter T does not occur in the signature", "",
       "fn SignatureError<T>() -> usize { let spare = \<llangle>undefined :: 't\<rrangle>; 0 }"),
     ("body-only-const", "urust: generic parameter N does not occur in the signature", "",
       "fn SignatureError<const N: usize>() -> usize { let spare = \<llangle>undefined :: 'n itself\<rrangle>; 0 }")]
  val _ = List.app (fn (label, expected, options, item) =>
    let
      val text = declaration options item
      val (diagnostic, events) = reports (fn () =>
        failure label expected (fn () => run thy label text))
      val positions = map position_range (message_positions diagnostic)
      val _ = require (label ^ ": positioned diagnostic lost its source")
        (not (null positions) andalso String.isSubstring label diagnostic)
      val _ = if String.isPrefix "unregistered-" label then
        require (label ^ ": exact missing trait range changed")
          (hd positions = range_of text "MissingTrait" 0)
        else if String.isPrefix "body-only-" label then
          (require (label ^ ": O7 did not identify its source header parameter")
             (hd positions = range_of text (if label = "body-only-type" then "T" else "N") 0);
           require (label ^ ": O7 did not preserve the exact user-decided diagnostic")
             (String.isPrefix expected diagnostic))
        else ()
      val _ = if label = "duplicate-override" then
        require (label ^ ": both duplicate override positions missing") (length positions >= 2)
        else ()
      val _ = require (label ^ ": failed declaration installed generic parameter markup")
        (null (parameter_definitions events))
      val _ = require (label ^ ": failure changed all original registries/theory/schemes")
        (snapshot (Proof_Context.init_global thy) = original_snapshot andalso
         scheme_snapshot (Proof_Context.init_global thy) = before_schemes)
      val recovery = run thy (label ^ "-recovery")
        (declaration "" "fn SignatureRecovery(value: u8) -> u8 { value }") |> Toplevel.context_of
      val _ = require (label ^ ": genuine error blocked subsequent declaration")
        (is_some (Parser_Test_Calls.lookup recovery "SignatureRecovery"))
    in () end) overrides
  val ambient = run thy "signature-ambient-model"
    "locale SignatureAmbient = fixes anchor :: 't" |> Toplevel.theory_of
  val _ = ignore (failure "ambient-default-name" "is fixed by the ambient context" (fn () =>
    run ambient "ambient-default-name"
      ("context SignatureAmbient begin\n" ^ declaration "" identity)))
  val _ = ignore (failure "ambient-override-name" "is fixed by the ambient context" (fn () =>
    run ambient "ambient-override-name"
      ("context SignatureAmbient begin\n" ^
        declaration ("hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'t" ^ "], ") identity)))
  val shadowed = run thy "signature-shadow"
    ("urust_type \"SignatureShadow\" = " ^ cartouche "nat" ^ "\n" ^
      declaration "" "fn SignatureShadowFn<SignatureShadow>(value: SignatureShadow) -> SignatureShadow { value }")
    |> Toplevel.context_of
  val shadow_backend = #hol_term (entry shadowed "SignatureShadowFn")
  val _ = require "generic shadows a registry mapping inside its item"
    (map #hol (scheme shadowed shadow_backend) = [("'signatureshadow", @{sort type})] andalso
     hd (binder_types (fastype_of shadow_backend)) <> @{typ nat})
  val _ = require "registry mapping remains after generic scope closes"
    (URust_Type_Mappings.resolve shadowed
      (URust_AST.Path_Type
        ([URust_AST.Rust_Type_Path_Segment ("SignatureShadow", Position.none, NONE,
           URust_AST.Source_Layout (Position.none, []))],
         URust_AST.Source_Layout (Position.none, []))) = @{typ nat})
  val _ = require_scope_closed "mapping shadow" shadowed
  val overridden = run thy "signature-const-minimum"
    (declaration ("hol_type_parameters = [\"N\" \<rightarrow> " ^ cartouche "'size::type" ^ "], ")
      "fn SignatureConstMinimum<const N: usize>(value: [u8; N]) -> usize { 0 }")
    |> Toplevel.context_of
  val _ = require "const override unions minimum and mapping-strengthened sort"
    (map #hol (scheme overridden (#hol_term (entry overridden "SignatureConstMinimum"))) =
      [("'size", @{sort len})])
  val annotated = run thy "signature-member-annotation"
    ("urust [pp_test, verbosity = 0] " ^ cartouche
      ("struct SignatureAnnotated { value: u8 }\nimpl SignatureAnnotated {\n\<omega>" ^
        cartouche ("hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'member::ord" ^ "]") ^
        "\nfn Value<T>(self, value: T) -> T { value }\n}"))
    |> Toplevel.context_of
  val _ = require "member annotation sets one generic signature"
    (map #hol (scheme annotated (#hol_term (entry annotated "SignatureAnnotated::Value"))) =
      [("'member", @{sort ord})])
  (* An impl override addresses only declarations on that impl, not a member's local T. *)
  val _ = ignore (failure "impl-override-option" "unknown parameter override" (fn () =>
    run thy "impl-override-option"
      ("urust [verbosity = 0] " ^ cartouche
        ("struct SignatureAnnotated { value: u8 }\n\<omega>" ^
          cartouche ("hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'member" ^ "]") ^
          "\nimpl SignatureAnnotated { fn Value<T>(self, value: T) -> T { value } }"))))
  val _ = ignore (failure "chunk-override-option" "declaration-specific" (fn () =>
    run thy "chunk-override-option"
      ("urust [hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'member" ^ "]] " ^
        cartouche identity)))
in val _ = () end
\<close>

section\<open> Parameter roles through wrappers and kind-neutral HOL escapes \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val ctxt = @{context}
  val original_snapshot = snapshot ctxt
  val original_schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ "
  fun declaration options item =
    "urust_fn [verbosity = 0" ^ options ^ "] signature_role_error " ^ cartouche (prefix ^ item)
  fun item generic typ = "fn SignatureRole<" ^ generic ^ ">(value: " ^ typ ^ ") -> " ^ typ ^ " { value }"
  val const_rows =
    [("direct", "N"), ("group", "(N)"), ("nested-group", "((N))"),
     ("tuple", "(N, u8)"), ("array-element", "[N; 3]"),
     ("mutable-reference", "&mut N"), ("raw-const-pointer", "*const N"),
     ("raw-mut-pointer", "*mut N"), ("nested-array", "([N; 3], u8)"),
     ("nested-pointer-tuple", "*const (N, u8)"),
     ("mapped-type-slot", "SignatureBag<N>"),
     ("mapped-nested-type-slot", "SignatureBag<(N, u8)>"),
     ("mixed-mapped-type-slot", "SignatureRoleSized<N, 3>")]
    |> map (fn (label, typ) => ("const-type-" ^ label, "const parameters", "N", "",
      item "const N: usize" typ))
  val type_rows =
    [("direct", "[u8; T]"), ("nested-array", "([u8; T], u8)"),
     ("pointer-array", "*const [u8; T]"),
     ("mapped-const-slot", "SignatureRoleSized<u8, T>"),
     ("mapped-grouped-const-slot", "SignatureRoleSized<u8, (T)>"),
     ("mapped-nested-grouped-const-slot", "SignatureRoleSized<u8, ((T))>")]
    |> map (fn (label, typ) => ("type-length-" ^ label, "type parameters", "T", "",
      item "T" typ))
  val sorted_rows =
    [("type-length-final-len", "type parameters", "T",
      ", hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'element::len" ^ "]",
      item "T" "[u8; T]"),
     ("type-mapped-const-final-len", "type parameters", "T",
      ", hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'element::len" ^ "]",
      item "T" "SignatureRoleSized<u8, T>")]
  val _ = List.app (fn (label, expected, token, options, rust) =>
    let
      val text = declaration options rust
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val (result, events) = capture (fn () => failure label expected (fn () => run thy label text))
      val diagnostic = Exn.release result
      val occurrence = if options = "" then 1 else 2
      val _ = require (label ^ ": wrong-kind error must identify the actual parameter leaf")
        (map position_range (message_positions diagnostic) =
          [range_of text token occurrence, range_of text "urust_fn" 0])
      val _ = require (label ^ ": rejected kind use released successful output or declaration entities")
        (null (ordinary events) andalso null (chunks "urgent" events) andalso
          null (declaration_reports events) andalso
          null (parameter_definitions (fold Parser_Test_Reports.collect_markup (trees "report" events) []
            |> map (fn (name, props) => (name, position_range (Position.of_properties props), props)))))
      val _ = require (label ^ ": kind failure changed original theory or generic/ordinary registries")
        (snapshot (Proof_Context.init_global thy) = original_snapshot andalso
          scheme_snapshot (Proof_Context.init_global thy) = original_schemes)
      val _ = require (label ^ ": kind failure changed native output/report callbacks")
        (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
      val recovery = run thy (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche (prefix ^
          "fn SignatureRoleRecovery(value: u8) -> u8 { value }")) |> Toplevel.context_of
      val _ = require (label ^ ": kind error blocked monomorphic recovery")
        (is_some (Parser_Test_Calls.lookup recovery "SignatureRoleRecovery"))
      val _ = require_scope_closed label recovery
    in () end) (const_rows @ type_rows @ sorted_rows)
  val _ = List.app (fn (rust, expected) =>
    require (rust ^ ": valid roles, escaped sorts or declared-HOL bypass lost ordered metadata")
      (map (fn {rust, kind, hol} => (rust, kind, hol))
        (entry_scheme ctxt (entry ctxt rust)) = expected))
    [("SignatureRoleMapped", [("T", URust_AST.Type_Parameter, ("'t", @{sort type})),
       ("N", URust_AST.Const_Parameter, ("'n", @{sort len}))]),
     ("SignatureRoleGroupedLength", [("N", URust_AST.Const_Parameter, ("'n", @{sort len}))]),
     ("SignatureRoleConstEscape", [("N", URust_AST.Const_Parameter, ("'n", @{sort len0}))]),
     ("SignatureRoleTypeEscape", [("T", URust_AST.Type_Parameter, ("'t", @{sort len}))]),
     ("SignatureRoleExplicitEscape", [("T", URust_AST.Type_Parameter, ("'t", @{sort len}))]),
     ("SignatureRoleSharedEscapes", [("T", URust_AST.Type_Parameter, ("'t", @{sort type})),
       ("N", URust_AST.Const_Parameter, ("'n", @{sort len}))]),
     ("SignatureRoleOrderedEscapes", [("T", URust_AST.Type_Parameter, ("'element", @{sort len})),
       ("N", URust_AST.Const_Parameter, ("'length", @{sort len}))]),
     ("SignatureRoleDeclaredConst", [("N", URust_AST.Const_Parameter, ("'n", @{sort len0}))]),
     ("SignatureRoleDeclaredType", [("T", URust_AST.Type_Parameter, ("'t", @{sort type}))])]
  val first = TFree ("'first", @{sort len})
  val second = TFree ("'second", @{sort len})
  val ordered_backend = entry ctxt "SignatureRoleOrderedEscapes"
  val ordered_instance = the (URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt
    (#serial ordered_backend) (#hol_term ordered_backend)
    [(first, Position.none), (second, Position.none)])
  val _ = require "two well-sorted HOL escapes retain the distinct element/length order"
    (hd (binder_types (fastype_of ordered_instance)) = Type (@{type_name array}, [first, second]))
  val shared_backend = entry ctxt "SignatureRoleSharedEscapes"
  val shared_instance = the (URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt
    (#serial shared_backend) (#hol_term shared_backend)
    [(@{typ nat}, Position.none), (@{typ 3}, Position.none)])
  val _ = require "unannotated HOL element/length escapes retain source parameter sharing"
    (hd (binder_types (fastype_of shared_instance)) = @{typ "(nat, 3) array"})
  val _ = require_scope_closed "role positives" ctxt
in val _ = () end
\<close>

section\<open> Candidate freshness, unused sorts, replay and native merge \<close>

ML_val\<open>
local
  open URust_AST
  structure Types = URust_Type_Mappings
  fun assert label condition = if condition then () else error ("U3 lower probe: " ^ label)
  val ctxt = @{context}
  val layout = Source_Layout (Position.none, [])
  fun named name = Path_Type ([Rust_Type_Path_Segment (name, Position.none, NONE, layout)], layout)
  fun escaped text = HOL_Type_Source (Input.string text)
  fun parameter rust kind hol =
    {rust = rust, kind = kind, hol = hol, pos = Position.none,
     bounds = [], report_reference = K ()}: Types.generic_parameter
  val scope = {parameters =
    [parameter "T" Type_Parameter ("'t", @{sort type}),
     parameter "N" Const_Parameter ("'n", @{sort len0})]}
  val scoped = Types.with_generic_scope scope ctxt
  val shared = Types.resolve_signature scoped [named "T", escaped "'t"]
  val _ = assert "Rust and escaped names share" (shared = [TFree ("'t", @{sort type}),
    TFree ("'t", @{sort type})])
  val array_type = Const_Array_Type (escaped "nat", named "N", layout)
  val array = the_single (Types.resolve_signature scoped [array_type])
  val _ = assert "length sort strengthened" (Term.add_tfreesT array [] =
    [("'n", @{sort len})])
  val _ = assert "scope is isolated" (is_none (Types.generic_scope ctxt))
  val pointer = Raw_Pointer_Type (RPM_Mut, named "T", layout)
  val pointer_types = Types.resolve_signature scoped [pointer, named "T"]
  val _ = assert "pointer retains named generic"
    (member (op =) (Term.add_tfreesT (hd pointer_types) []) ("'t", @{sort type}))

  val lthy = Named_Target.theory_init @{theory}
  val source_type = TFree ("'t", @{sort type})
  val source_channel = TFree ("'channel", @{sort type})
  val body_type = Type (@{type_name function_body},
    [source_channel, source_type, @{typ unit}, @{typ unit}, @{typ unit}])
  val backend = Free ("u3_scheme_probe", source_type --> body_type)
  val parameters =
    [{rust = "T", kind = Type_Parameter, hol = ("'t", @{sort type})},
     {rust = "U", kind = Type_Parameter, hol = ("'u", @{sort len0})},
     {rust = "N", kind = Const_Parameter, hol = ("'n", @{sort len0})}]
  val registered = Types.register_generic_scheme
    {identity = backend, backend = backend, sources = [], parameters = parameters, pos = Position.none} lthy
  val _ = assert "ordered scheme including unused parameters"
    (Types.generic_scheme registered backend = SOME parameters)

  val collision = TVar (("caller", 70000), @{sort type})
  val callee_generic = TVar (("callee", 50000), @{sort type})
  val candidate = Free ("u3_scheme_probe", callee_generic -->
    Type (@{type_name function_body},
      [collision, callee_generic, @{typ unit}, @{typ unit}, @{typ unit}]))
  val arguments = [(collision, Position.none), (@{typ 3}, Position.none),
    (@{typ 4}, Position.none)]
  val instantiated = the (Types.instantiate_generic_scheme registered backend candidate arguments)
  val (inputs, result) = strip_type (fastype_of instantiated)
  val Type (_, [channel, value, _, _, _]) = result
  val _ = assert "caller variable preserved exactly" (inputs = [collision] andalso value = collision)
  val _ = assert "overlapping independent channel renamed away" (channel <> collision)
  val _ = assert "unused sort still enforced"
    (is_none (Types.instantiate_generic_scheme registered backend candidate
      [(collision, Position.none), (@{typ nat}, Position.none), (@{typ 4}, Position.none)]))
  val _ = assert "wrong count ineligible"
    (is_none (Types.instantiate_generic_scheme registered backend candidate []))
  val _ = assert "repeated instantiation preserves caller sharing"
    (case Types.instantiate_generic_scheme registered backend candidate arguments of
       SOME term => hd (binder_types (fastype_of term)) = collision
     | NONE => false)

  val shared_backend = Free ("u3_shared_channel_probe", source_type -->
    Type (@{type_name function_body},
      [source_type, source_type, @{typ unit}, @{typ unit}, @{typ unit}]))
  val shared_registered = Types.register_generic_scheme
    {identity = shared_backend, backend = shared_backend, sources = [], parameters = take 1 parameters, pos = Position.none} registered
  val shared_candidate = Free ("u3_shared_channel_probe", callee_generic -->
    Type (@{type_name function_body},
      [callee_generic, callee_generic, @{typ unit}, @{typ unit}, @{typ unit}]))
  val shared_instance = the (Types.instantiate_generic_scheme shared_registered shared_backend
    shared_candidate [(collision, Position.none)])
  val Type (_, [shared_channel, shared_value, _, _, _]) = snd (strip_type (fastype_of shared_instance))
  val _ = assert "intentional generic/channel sharing survives"
    (shared_channel = collision andalso shared_value = collision)

  val seed = Free ("u3_seed", @{typ nat})
  val applied_backend = Free ("u3_applied_probe", @{typ nat} --> fastype_of backend) $ seed
  val applied_registered = Types.register_generic_scheme
    {identity = applied_backend, backend = applied_backend, sources = [], parameters = parameters, pos = Position.none} shared_registered
  val applied_candidate =
    Free ("u3_applied_probe", @{typ nat} --> fastype_of candidate) $ seed
  val applied_instance = the (Types.instantiate_generic_scheme applied_registered applied_backend
    applied_candidate arguments)
  val _ = assert "complete applied backend retained"
    (snd (Term.strip_comb applied_instance) = [seed])
  val _ = assert "applied backend source parameter aligned"
    (hd (binder_types (fastype_of applied_instance)) = collision)
  val replayed = Types.register_generic_scheme
    {identity = backend, backend = backend, sources = [], parameters = parameters, pos = Position.none}
    registered
  val _ = assert "declaration replay is idempotent"
    (Types.generic_scheme replayed backend = SOME parameters)
  val base = Theory.end_theory @{theory}
  fun branch label =
    Named_Target.theory_init (Theory.begin_theory (label, Position.none) [base])
    |> Types.register_generic_scheme
      {identity = backend, backend = backend, sources = [], parameters = parameters, pos = Position.none}
    |> Local_Theory.exit_global |> Theory.end_theory
  val left = branch "SignatureSchemeLeft"
  val right = branch "SignatureSchemeRight"
  val merged = Theory.begin_theory ("SignatureSchemeMerged", Position.none) [left, right]
    |> Proof_Context.init_global
  val _ = assert "native theory merge preserves the ordered scheme"
    (Types.generic_scheme merged backend = SOME parameters)
  val merged_reverse = Theory.begin_theory ("SignatureSchemeMergedReverse", Position.none) [right, left]
    |> Proof_Context.init_global
  val _ = assert "native theory merge is independent of parent order"
    (Types.generic_scheme merged_reverse backend = SOME parameters)
  val conflicting = {rust = "Different", kind = Type_Parameter, hol = ("'t", @{sort type})} :: tl parameters
  val _ = assert "conflicting same-identity metadata does not overwrite a registration"
    (case Exn.capture (fn () => Types.register_generic_scheme
      {identity = backend, backend = backend, sources = [], parameters = conflicting, pos = Position.none}
      registered) () of
       Exn.Exn (ERROR message) => String.isSubstring "conflicting generic schemes" message
     | _ => false)
  val _ = assert "failed replay leaves original metadata intact"
    (Types.generic_scheme registered backend = SOME parameters)

in
  val _ = writeln "U3 lower probes passed: scope/sharing/final sorts/unused sorts/high collisions/channels/applied backend"
end
\<close>

section\<open> Exact generic output positives and durable late failures \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val ctxt = Proof_Context.init_global thy
  val initial_snapshot = snapshot ctxt
  val initial_schemes = scheme_snapshot ctxt
  val prefixes =
    [("member-type-guard", holder ^ "\nimpl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }"),
     ("free-const-guard", holder ^ "\nfn sized<const N: usize>(value: [u8; N]) -> usize { 0 }")]
  val late_failure = "\nfn late_failure(late_value: u8) -> u8 { missing_output_value }"
  fun paired (setting_value, verbosity, (kind, body)) =
    let
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val configured = setting setting_value thy
      val label = "complete-atomicity-" ^ kind ^ "-" ^ string_of_int verbosity ^ "-" ^
        setting_name setting_value
      val positive_text = command verbosity body
      val (success, success_events) = capture (fn () =>
        run_with true configured (label ^ "-positive") positive_text)
      val completed = Exn.release success
      val completed_ctxt = Toplevel.context_of completed
      val key = if kind = "member-type-guard" then "SyntaxOutputHolder::member" else "sized"
      val _ = require (label ^ ": exact original generic prefix did not install its scheme")
        (length (scheme completed_ctxt (#hol_term (entry completed_ctxt key))) = 1)
      val _ = native_artifacts completed_ctxt "SyntaxOutputHolder"
      val _ = require (label ^ ": successful authored verbosity changed")
        ((not (null (ordinary success_events))) = (verbosity > 0) andalso
         callback_count "writeln" success_events =
           (if verbosity = 0 then 0 else if kind = "member-type-guard" then 4 else 3) andalso
         null (chunks "urgent" success_events))
      val _ = require (label ^ ": original successful declaration reports missing")
        (not (null (declaration_reports success_events)))
      val _ = require (label ^ ": original show_results setting changed on success")
        (Config.get_global (Toplevel.theory_of completed) Proof_Display.show_results =
          Config.get_global configured Proof_Display.show_results)
      val _ = require_scope_closed label completed_ctxt
      val text = command verbosity (body ^ late_failure)
      val (result, events) = capture (fn () => run_with true configured label text)
      val message =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": real later failure lost its diagnostic")
        (String.isSubstring "missing_output_value" message)
      val _ = require (label ^ ": real later failure lost its source position")
        (not (null (message_positions message)))
      val _ = require (label ^ ": earlier successful datatype/generic output escaped")
        (null (ordinary events))
      val _ = require (label ^ ": earlier successful definition reports escaped")
        (null (declaration_reports events))
      val _ = exact_binders label text [("late_value", 0)] events
      val _ = require (label ^ ": original registry, schemes or theory artifacts changed")
        (snapshot (Proof_Context.init_global configured) = initial_snapshot andalso
         scheme_snapshot (Proof_Context.init_global configured) = initial_schemes)
      val (recovery, recovery_events) = capture (fn () =>
        run_with true configured (label ^ "-recovery") (command verbosity (holder ^ "\n" ^ member_source)))
      val recovered = Exn.release recovery |> Toplevel.context_of
      val _ = require (label ^ ": failure blocked exact original monomorphic recovery")
        (is_some (Parser_Test_Calls.lookup recovered "SyntaxOutputHolder::member"))
      val _ = native_artifacts recovered "SyntaxOutputHolder"
      val _ = require (label ^ ": recovery lost authored definition reports")
        (not (null (declaration_reports recovery_events)))
      val _ = require (label ^ ": positive/failure/recovery preserves exact native callbacks")
        (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
    in () end
  val _ = List.app paired
    (maps (fn setting_value => maps (fn verbosity =>
      map (fn prefix => (setting_value, verbosity, prefix)) prefixes) [0, 1, 2])
      [NONE, SOME true, SOME false])
  fun standalone declared verbosity =
    let
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val before_global = Config.get_global thy Proof_Display.show_results
      val label = "complete-output-signature-guard-" ^ Bool.toString declared ^ "-" ^ string_of_int verbosity
      val body = "fn SyntaxOutputGeneric<T>(value: T) -> T { value }"
      fun declaration body =
        "urust_fn [verbosity = " ^ string_of_int verbosity ^ "] syntax_output_guard " ^
        (if declared then ":: " ^ cartouche "nat => ('s, nat, 'abort, 'i, 'o) function_body" ^ " "
         else "") ^ cartouche body
      val text = declaration body
      val (success, successful_events) = capture (fn () => run_with true thy (label ^ "-positive") text)
      val completed_ctxt = Exn.release success |> Toplevel.context_of
      val _ = require (label ^ ": original standalone source lost its scheme")
        (map #rust (scheme completed_ctxt (#hol_term (entry completed_ctxt "SyntaxOutputGeneric"))) = ["T"])
      val _ = require (label ^ ": original standalone authored output changed")
        ((not (null (ordinary successful_events))) = (verbosity > 0) andalso
         callback_count "writeln" successful_events = (if verbosity > 0 then 2 else 0) andalso
         null (chunks "urgent" successful_events))
      val _ = require (label ^ ": original standalone definition reports missing")
        (not (null (declaration_reports successful_events)))
      val parameter_reports = fold Parser_Test_Reports.collect_markup (trees "report" successful_events) []
      val _ = require (label ^ ": original first non-lifetime declaration range changed")
        (exists (fn (name, props) => name = Markup.entityN andalso
          Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
          is_some (Properties.get props Markup.defN) andalso
          position_range (Position.of_properties props) = range_of text "T" 0) parameter_reports)
      val failed_text = declaration "fn SyntaxOutputGeneric<T>(value: T) -> T { missing_output_value }"
      val (result, events) = capture (fn () => run_with true thy label failed_text)
      val diagnostic =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => Runtime.exn_message exn)
      val _ = require (label ^ ": real same-mode body failure lost its diagnostic/range")
        (String.isSubstring "missing_output_value" diagnostic andalso
         not (null (message_positions diagnostic)))
      val _ = require (label ^ ": complete output or definition reports escaped")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = exact_binders label failed_text [("value", 0)] events
      val _ = require (label ^ ": standalone failure mutated original namespace/schemes")
        (snapshot (Proof_Context.init_global thy) = initial_snapshot andalso
         scheme_snapshot (Proof_Context.init_global thy) = initial_schemes)
      val _ = require_scope_closed label completed_ctxt
      val _ = require (label ^ ": standalone positive preserves native show_results")
        (Config.get_global (Proof_Context.theory_of completed_ctxt) Proof_Display.show_results = before_global)
      val recovery_text = declaration "fn SyntaxOutputGeneric(value: u8) -> u8 { value }"
      val (recovery, recovery_events) = capture (fn () =>
        run_with true thy (label ^ "-recovery") recovery_text)
      val recovered = Exn.release recovery |> Toplevel.context_of
      val _ = require (label ^ ": same-mode monomorphic recovery restores its ordinary declaration")
        (is_some (Parser_Test_Calls.lookup recovered "SyntaxOutputGeneric") andalso
         not (null (declaration_reports recovery_events)) andalso
         Config.get_global (Proof_Context.theory_of recovered) Proof_Display.show_results = before_global)
      val _ = require (label ^ ": positive/failure/recovery preserves exact native callbacks")
        (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
      val _ = require_scope_closed (label ^ "-recovery") recovered
    in () end
  val _ = List.app (fn verbosity => List.app (fn declared => standalone declared verbosity) [false, true])
    [0, 1, 2]
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val locale = run_with false thy "native-output-locale"
    "locale SyntaxOutputScope = fixes output_seed :: nat"
  val entered = continue false locale "native-output-nested-enter"
    "context SyntaxOutputScope begin\ndeclare [[show_results = true]]\n\
    \context begin\ndeclare [[show_results = false]]"
  val callbacks = saved_callbacks ()
  val report_callback = !Private_Output.report_fn
  val before_context = Toplevel.context_of entered
  val before_settings = target_settings before_context
  val before_global = Config.get_global (Toplevel.theory_of entered) Proof_Display.show_results
  val before_snapshot = snapshot before_context
  val before_schemes = scheme_snapshot before_context
  val member = "impl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }"
  val body = holder ^ "\n" ^ member
  val label = "native-output-nested-failure-member-type-guard"
  val (success, successful_events) = capture (fn () => continue true entered (label ^ "-positive")
    (command 2 body))
  val completed = Exn.release success
  val completed_ctxt = Toplevel.context_of completed
  val _ = require (label ^ ": exact nested generic source lost its scheme")
    (map #rust (scheme completed_ctxt (#hol_term (entry completed_ctxt "SyntaxOutputHolder::member"))) = ["T"])
  val _ = require (label ^ ": nested positive restores every original target/global setting")
    (length before_settings >= 2 andalso target_settings completed_ctxt = before_settings andalso
     Config.get_global (Toplevel.theory_of completed) Proof_Display.show_results = before_global)
  val _ = require (label ^ ": nested positive lost authored output/report controls")
    (callback_count "writeln" successful_events = 4 andalso null (chunks "urgent" successful_events) andalso
     not (null (declaration_reports successful_events)))
  val text = command 2 (body ^ "\nfn late_failure(late_value: u8) -> u8 { missing_output_value }")
  val (failed, events) = capture (fn () => continue true entered label text)
  val _ = require (label ^ ": real later nested failure retains its diagnostic")
    (case failed of Exn.Exn exn => String.isSubstring "missing_output_value" (Runtime.exn_message exn)
     | _ => false)
  val _ = require (label ^ ": earlier successful output or definition markup escaped")
    (null (ordinary events) andalso null (declaration_reports events))
  val _ = exact_binders label text [("late_value", 0)] events
  val _ = require (label ^ ": failure preserves every original target/global setting and registry")
    (target_settings (Toplevel.context_of entered) = before_settings andalso
     Config.get_global (Toplevel.theory_of entered) Proof_Display.show_results = before_global andalso
     snapshot (Toplevel.context_of entered) = before_snapshot andalso
     scheme_snapshot (Toplevel.context_of entered) = before_schemes)
  val (recovery, recovery_events) = capture (fn () => continue true entered (label ^ "-recovery")
    (command 2 (holder ^ "\n" ^ Generic_Syntax_Output_Atomicity.member_source)))
  val recovered = Exn.release recovery |> Toplevel.context_of
  val _ = require (label ^ ": exact monomorphic recovery failed")
    (is_some (Parser_Test_Calls.lookup recovered "SyntaxOutputHolder::member") andalso
     not (null (declaration_reports recovery_events)) andalso target_settings recovered = before_settings)
  val _ = require (label ^ ": nested positive/failure/recovery preserves exact native callbacks")
    (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
in val _ = () end
\<close>

chapter\<open> Bodies \<close>

section\<open> Positioned body errors and complete failure atomicity \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val ctxt = Proof_Context.init_global thy
  val prior_snapshot = snapshot ctxt
  val schemes = scheme_snapshot ctxt
  val traits = map (URust_Trait_Mappings.lookup ctxt) ["Scale", "SlotOne", "SlotTwo", "Marker"]
  val prefix = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ "
  val rows =
    [("type-value", "urust: type parameter T cannot be used as a value",
      "fn BodyError<T>(value: T) -> T { T }", "T", 3),
     ("missing-constant", "urust: no associated constant MISSING in the bounds of T",
      "fn BodyError<T: Marker>(value: T) -> " ^ "\<tau>" ^ cartouche "nat" ^ " { T::MISSING }", "MISSING", 0),
     ("ambiguous-constant", "multiple applicable associated constants SLOT for T: SlotOne, SlotTwo",
      "fn BodyError<T: SlotOne + SlotTwo>(value: T) -> " ^ "\<tau>" ^ cartouche "nat" ^
        " { T::SLOT }", "SLOT", 0),
     ("concrete-missing-sort", "primitive associated-item path",
      "fn BodyError() -> " ^ "\<tau>" ^ cartouche "nat" ^ " { u8::CEILING }", "CEILING", 0),
     ("concrete-ambiguous", "multiple applicable associated constants SLOT for BodyNumber: SlotOne, SlotTwo",
      "fn BodyError() -> BodyNumber { BodyNumber::SLOT }", "SLOT", 0),
     ("body-only-const", "urust: generic parameter N does not occur in the signature",
      "fn BodyError<const N: usize>() -> usize { N }", "N", 0)]
  fun check (label, expected, rust, token, occurrence) =
    let
      val label = "body-" ^ label
      val text = "urust_fn [verbosity = 0] body_error " ^ cartouche (prefix ^ rust)
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val (result, events) = capture (fn () => run thy label text)
      val diagnostic = (case result of
          Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": exact expected diagnostic absent: " ^ diagnostic)
        (String.isSubstring expected diagnostic)
      val ranges = map position_range (message_positions diagnostic)
      val _ = require (label ^ ": wrong leaf/header range: " ^ commas (map (fn (a,b) =>
          string_of_int a ^ "-" ^ string_of_int b) ranges))
        (not (null ranges) andalso hd ranges = range_of text token occurrence)
      val _ = require (label ^ ": failed body leaked ordinary/urgent output or declaration reports")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": exact callback restoration failed")
        (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
      val current = Proof_Context.init_global thy
      val _ = require (label ^ ": failure changed source registries, theory, scopes or trait templates")
        (snapshot current = prior_snapshot andalso scheme_snapshot current = schemes andalso
         map (URust_Trait_Mappings.lookup current) ["Scale", "SlotOne", "SlotTwo", "Marker"] = traits)
      val (recovered, _) = capture (fn () => run thy (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche "fn BodyRecovery(value: u8) -> u8 { value }"))
      val _ = require (label ^ ": failure blocked an ordinary subsequent declaration")
        (is_some (Parser_Test_Calls.lookup (Exn.release recovered |> Toplevel.context_of) "BodyRecovery"))
    in () end
  val _ = List.app check rows
in end
\<close>

section\<open> Associated-constant navigation and final-sort tooltips \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val item = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ " ^
    "fn BodyMarkup<T: Scale, const N: usize>(value: [T; N]) -> \<tau>" ^ cartouche "nat" ^
    " { let count = N; T::CEILING }"
  val text = "urust_fn [verbosity = 0] body_markup " ^ cartouche item
  val callbacks = saved_callbacks ()
  val report_callback = !Private_Output.report_fn
  val (result, events) = capture (fn () => run thy "body-markup" text)
  val completed = Exn.release result |> Toplevel.context_of
  val markup = fold Parser_Test_Reports.collect_markup (trees "report" events) []
  fun at props token occurrence =
    position_range (Position.of_properties props) = range_of text token occurrence
  fun plain chunks = XML.content_of (maps YXML.parse_body chunks)
    |> Symbol.explode |> filter_out Symbol.is_control |> implode
  fun typings range (XML.Elem ((name, props), body)) =
        (if name = Markup.typingN andalso position_range (Position.of_properties props) = range
         then [plain [XML.content_of body]] else []) @ maps (typings range) body
    | typings _ (XML.Text _) = []
  val parameters = entry_scheme completed (entry completed "BodyMarkup")
  val _ = require "body markup retains final source type and const length sorts"
    (map #hol parameters = [("'t", @{sort trait_scale}), ("'n", @{sort len})])
  val _ = List.app (fn (name, header, use, parameter) =>
    let
      val definitions = markup |> map_filter (fn (element, props) =>
        if element = Markup.entityN andalso at props name header andalso
          Properties.get props Markup.kindN = SOME "urust_generic_parameter"
        then Properties.get props Markup.defN else NONE)
      val _ = require "body generic use navigates to its exact declaration after an escaped comment"
        (length definitions = 1 andalso exists (fn (element, props) =>
          element = Markup.entityN andalso at props name use andalso
          Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
          Properties.get props Markup.refN = SOME (hd definitions)) markup)
      val expected = plain [name ^ " = " ^ Syntax.string_of_typ
        (Config.put show_sorts true completed) (TFree (#hol parameter))]
      val _ = List.app (fn occurrence => require "body header/use labelled tooltip retains final sort"
        (Library.member (op =) (maps (typings (range_of text name occurrence)) (trees "report" events)) expected))
        [header, use]
    in () end)
    [("T", 0, 2, hd parameters), ("N", 0, 2, nth parameters 1)]
  val scale = the (URust_Trait_Mappings.lookup completed "Scale")
  val (_, expected_trait_properties) = Position.entity_markup "urust_trait" ("Scale", #pos scale)
  val _ = require "associated constant use retains native bound-trait definition navigation"
    (exists (fn (element, props) => element = Markup.entityN andalso at props "CEILING" 0 andalso
      forall (fn (key, value) => Properties.get props key = SOME value) expected_trait_properties) markup)
  val _ = require "associated constant use navigates to its mapped native constant"
    (exists (fn (element, props) => element = Markup.entityN andalso at props "CEILING" 0 andalso
      Properties.get props Markup.kindN = SOME "constant" andalso
      Properties.get props Markup.nameN = SOME @{const_name trait_ceiling}) markup)
  val _ = require "associated constant tooltip retains the checked native type witness and sort"
    (exists (fn typing => String.isSubstring "trait_ceiling" typing andalso
      String.isSubstring (plain [Syntax.string_of_typ (Config.put show_sorts true completed)
        (TFree (#hol (hd parameters)))]) typing)
      (maps (typings (range_of text "CEILING" 0)) (trees "report" events)))
  val _ = require "body navigation capture restores exact output and report callbacks"
    (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
  val _ = require_scope_closed "body markup" completed
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val text = "micro_rust_notation (literal) " ^ cartouche "23 :: nat" ^ " (\"T::CEILING\")\n" ^
    "urust_fn [verbosity = 0] body_precedence " ^ cartouche
      ("fn BodyPrecedence<T: Scale>(value: T) -> " ^ "\<tau>" ^ cartouche "nat" ^ " { T::CEILING }") ^ "\n" ^
    "urust_fn [verbosity = 0] body_precedence_twin " ^ cartouche
      ("fn BodyPrecedenceTwin(value: " ^ "\<tau>" ^ cartouche "'t::trait_scale" ^ ") -> " ^
       "\<tau>" ^ cartouche "nat" ^ " { \<llangle>trait_ceiling TYPE('t)\<rrangle> }") ^ "\n" ^
    "lemma " ^ cartouche "body_precedence = body_precedence_twin" ^
      " unfolding body_precedence_def body_precedence_twin_def by (rule refl)"
  val (result, _) = capture (fn () => run thy "scope-constant-precedence" text)
  val _ = ignore (Exn.release result)
  val _ = writeln "U4 scoped generic head shadows explicit full-path literal notation kernel twin PASS"
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val ctxt = @{context}
  val prior = snapshot ctxt
  val schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " transaction " ^ Symbol.close ^ " */ "
  val families =
    [("standalone", "urust_fn", "body_transaction", prefix ^
      "fn BodyTransaction<T>(value: T) -> T { SignatureIdentity::<T, u8>(value) }", "::<T, u8>"),
     ("chunk-free", "urust", "", "struct TransactionBox<T> { payload: T }\n" ^
      "fn TransactionFirst<T>(value: T) -> T { value }\n" ^ prefix ^
      "fn TransactionLast<T>(value: T) -> T { SignatureIdentity::<T, u8>(value) }", "::<T, u8>"),
     ("chunk-member", "urust", "", "struct TransactionBox<T> { payload: T }\n" ^
      "fn TransactionFirst<T>(value: T) -> T { value }\nimpl TransactionBox<u8> {\n" ^ prefix ^
      "fn last<T>(value: T) -> T { SignatureIdentity::<T, u8>(value) }\n}", "::<T, u8>")]
  val _ = List.app (fn verbosity => List.app (fn (label, command, name, rust, token) =>
    let
      val text = command ^ " [verbosity = " ^ string_of_int verbosity ^ "] " ^ name ^ " " ^ cartouche rust
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run thy (label ^ "-late-body") text)
      val raw = case result of Exn.Res _ => error (label ^ ": late body unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val _ = require "late generic body failure retains exact diagnostic and full argument source range"
        (String.isSubstring "wrong number of generic arguments" raw andalso
         hd (map position_range (message_positions raw)) = range_of text token 0)
      val _ = require "late body failure after datatype/earlier function leaks no complete ordinary/urgent/report chunks"
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require "late body failure restores exact callbacks, namespace, registrations, native artifacts and closed scope"
        (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn) andalso
         snapshot (Proof_Context.init_global thy) = prior andalso
         scheme_snapshot (Proof_Context.init_global thy) = schemes)
      val _ = require_scope_closed "late body failure" (Proof_Context.init_global thy)
      val recovery = "urust [verbosity = 0] " ^ cartouche
        "struct TransactionBox<T> { payload: T }\nfn TransactionFirst<T>(value: T) -> T { value }"
      val (recovered, _) = capture (fn () => run thy (label ^ "-late-recovery") recovery)
      val current = Exn.release recovered |> Toplevel.context_of
      val _ = require "same-source ordinary datatype/generic function recovery after late body failure"
        (is_some (Parser_Test_Calls.lookup current "TransactionFirst") andalso
         is_some (URust_Type_Mappings.lookup current "TransactionBox"))
    in () end) families) [0, 1, 2]
  val _ = writeln "U4 late body failures after generated artifacts/full streams/source ranges/restoration/recovery all verbosity levels PASS"
in end
\<close>

section\<open> Authored generic uses before native erasure \<close>

text\<open>
An erased callee slot still records the caller's authored generic use. O7 requires that
parameter in the final HOL signature; an entirely unused parameter remains valid.
The native capture controls distinguish real reads from signature seeds and foreign scopes,
retain actual enclosing reads across caught nested failures, and restore invocation state
on both exceptions and interrupts. Exact reviewer sources retain their header ranges and
complete output, namespace, callback and recovery controls.
\<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  fun require label test = if test then () else error ("O7 capture probe: " ^ label)
  val reports = Unsynchronized.ref ([]: string list)
  fun parameter rust hol kind : M.generic_parameter =
    {rust = rust, pos = Position.none, kind = kind, hol = hol, bounds = [],
     report_reference = fn _ => reports := !reports @ [rust]}
  val t = parameter "T" ("'body_capture_t", \<^sort>\<open>type\<close>) URust_AST.Type_Parameter
  val n = parameter "N" ("'body_capture_n", \<^sort>\<open>len0\<close>) URust_AST.Const_Parameter
  val scoped = M.with_generic_scope {parameters = [t, n]} ctxt
  fun read current text =
    ignore (M.resolve_signature current
      [URust_Parser.parse_type_source current (Parser_Lex_Util.text_source text)])
  fun escaped name = "\<tau>" ^ Symbol.open_ ^ name ^ Symbol.close
  fun names label wanted action =
    let val (_, used) = M.capture_generic_uses scoped action
    in require label (sort_strings used = sort_strings wanted) end
  val (same, none) = M.capture_generic_uses ctxt (fn current => pointer_eq (ctxt, current))
  val _ = require "absent scope is the ordinary context" (same andalso null none)
  val empty = M.with_generic_scope {parameters = []} ctxt
  val (same_empty, none_empty) =
    M.capture_generic_uses empty (fn current => pointer_eq (empty, current))
  val _ = require "empty scope is the ordinary context" (same_empty andalso null none_empty)
  val _ = names "all-parameter seed list is not a use" [] (fn current => read current (escaped "nat"))
  val _ = require "seed list emits no scope references" (null (!reports))
  val _ = names "bare/grouped/nested Rust reads" ["'body_capture_t", "'body_capture_n"]
    (fn current => read current "(T, [T; N])")
  val _ = require "original reference callbacks and read order" (!reports = ["T", "T", "N"])
  val _ = names "named type escape" ["'body_capture_t"]
    (fn current => read current (escaped "'body_capture_t"))
  val _ = names "named const escape" ["'body_capture_n"]
    (fn current => read current (escaped "'body_capture_n::len0"))
  val _ = names "independent native escape" []
    (fn current => read current (escaped "'independent_capture"))
  val foreign = parameter "Foreign" (#hol t) URust_AST.Type_Parameter
  val replacement = parameter "T" (#hol t) URust_AST.Type_Parameter
  val _ = names "foreign scope, identical native variable" []
    (fn current => read (M.with_generic_scope {parameters = [foreign]} current)
      (escaped "'body_capture_t"))
  val _ = names "replaced scope, identical names but new callback" []
    (fn current => read (M.with_generic_scope {parameters = [replacement]} current) "T")
  val ((_, inner), outer) = M.capture_generic_uses scoped (fn current =>
    M.capture_generic_uses current (fn nested =>
      read nested (escaped "'body_capture_n::len0")))
  val _ = require "same-scope nested native reads reach both captures"
    (inner = ["'body_capture_n"] andalso outer = inner)
  val ((_, foreign_inner), foreign_outer) = M.capture_generic_uses scoped (fn current =>
    M.capture_generic_uses (M.with_generic_scope {parameters = [foreign]} current)
      (fn nested => read nested (escaped "'body_capture_t")))
  val _ = require "foreign nested reads do not reach the parent"
    (foreign_inner = ["'body_capture_t"] andalso null foreign_outer)
  val failed = Exn.capture (fn () => M.capture_generic_uses scoped
    (fn current => (read current "T"; error "capture failure"))) ()
  val _ = require "failure propagates unchanged"
    (case failed of Exn.Exn (ERROR "capture failure") => true | _ => false)
  val _ = names "failure leaves original context and next capture clean" []
    (fn current => read current (escaped "nat"))
  val (_, caught_trace) = M.capture_generic_uses scoped (fn current =>
    let
      val failed_inner = Exn.capture (fn () => M.capture_generic_uses current
        (fn nested => (read nested (escaped "'body_capture_n::len0");
          error "nested capture failure"))) ()
      val _ = require "caught nested exception unchanged"
        (case failed_inner of Exn.Exn (ERROR "nested capture failure") => true | _ => false)
    in read current "T" end)
  val _ = require "actual same-scope reads survive caught nested failure"
    (sort_strings caught_trace = ["'body_capture_n", "'body_capture_t"])
  val SOME {parameters = after} = M.generic_scope scoped
  val _ = require "original parameter callbacks were never replaced"
    (pointer_eq (#report_reference t, #report_reference (hd after)) andalso
      pointer_eq (#report_reference n, #report_reference (nth after 1)))
in
  val _ = writeln "O7 native capture probes PASS"
end
\<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  fun require label test = if test then () else error ("O7 interruption probe: " ^ label)
  fun parameter rust hol kind : M.generic_parameter =
    {rust = rust, pos = Position.none, kind = kind, hol = hol, bounds = [],
     report_reference = fn _ => ()}
  val t = parameter "T" ("'body_capture_t", \<^sort>\<open>type\<close>) URust_AST.Type_Parameter
  val n = parameter "N" ("'body_capture_n", \<^sort>\<open>len0\<close>) URust_AST.Const_Parameter
  val scoped = M.with_generic_scope {parameters = [t, n]} ctxt
  fun read current text =
    ignore (M.resolve_signature current
      [URust_Parser.parse_type_source current (Parser_Lex_Util.text_source text)])
  fun escaped name = "\<tau>" ^ Symbol.open_ ^ name ^ Symbol.close
  val (_, parent_uses) = M.capture_generic_uses scoped (fn parent =>
    let
      val entered = Single_Assignment.var "O7 capture interrupt entry"
      val blocked = Single_Assignment.var "O7 capture interrupt blocker"
      val finished = Single_Assignment.var "O7 capture interrupt result"
      val thread = Isabelle_Thread.fork
        (Isabelle_Thread.interrupts (Isabelle_Thread.params "O7 capture interruption"))
        (fn () => Single_Assignment.assign finished
          (Exn.capture (fn () => M.capture_generic_uses parent (fn current =>
            let
              val read_result = Exn.capture
                (fn () => read current (escaped "'body_capture_n::len0")) ()
              val _ = Single_Assignment.assign entered ()
              val _ = Exn.release read_result
            in Single_Assignment.await blocked end)) ()))
      val _ = Single_Assignment.await entered
      val _ = Isabelle_Thread.interrupt_thread thread
      val _ = Isabelle_Thread.join thread
      val _ = require "actual nested interrupt propagates unchanged"
        (case Single_Assignment.await finished of
           Exn.Exn exn => Exn.is_interrupt exn | _ => false)
    in read parent "T" end)
  val _ = require "same-scope reads remain in the live parent after caught interrupt"
    (sort_strings parent_uses = ["'body_capture_n", "'body_capture_t"])
  val (_, fresh) = M.capture_generic_uses scoped
    (fn current => read current (escaped "nat"))
  val _ = require "fresh capture has no interrupted state" (null fresh)
  val SOME {parameters = original} = M.generic_scope scoped
  val _ = require "original context/callbacks are unchanged"
    (pointer_eq (#report_reference t, #report_reference (hd original)) andalso
      pointer_eq (#report_reference n, #report_reference (nth original 1)))
in
  val _ = writeln "O7 actual nested interrupt cleanup PASS"
end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure M = URust_Type_Mappings
  val root = \<^theory>
  fun declaration target options declared rust =
    "urust_fn [" ^ options ^ "verbosity = 0] " ^ target ^ " " ^ declared ^ cartouche rust
  fun fn_command target rust = declaration target "" "" rust
  val setup =
    fn_command "r01_erase_type" "fn R01EraseType<T>(value: u8) -> u8 { value }" ^ "\n" ^
    fn_command "r01_erase_const" "fn R01EraseConst<const N: usize>(value: u8) -> u8 { value }" ^ "\n" ^
    fn_command "r01_erase_dual" "fn R01EraseDual<T, const N: usize>(value: u8) -> u8 { value }" ^ "\n" ^
    "urust_type \"R01O7Owner\" = " ^ cartouche "unit"
  val (model_result, _) = capture (fn () => run root "o7-erased-model" setup)
  val thy = Exn.release model_result |> Toplevel.theory_of
  val ctxt = Proof_Context.init_global thy
  val prior = snapshot ctxt
  val prior_schemes = scheme_snapshot ctxt
  val rows =
    [("erased-type", "fn", "T", 0, "",
       "fn R01BodyOnly<T>(value: u8) -> u8 { R01EraseType::<T>(value) }"),
     ("erased-const", "fn", "N", 0, "",
       "fn R01BodyOnly<const N: usize>(value: u8) -> u8 { R01EraseConst::<N>(value) }"),
     ("erased-type-and-const", "fn", "T", 0, "",
       "fn R01BodyOnly<T, const N: usize>(value: u8) -> u8 { R01EraseDual::<T, N>(value) }"),
     ("erased-type-under-value-shadow", "fn", "T", 0, "",
       "fn R01BodyOnly<T>(value: u8) -> u8 { let T = value; R01EraseType::<T>(T) }"),
     ("erased-type-in-closure", "fn", "T", 0, "",
       "fn R01BodyOnly<T>(value: u8) -> u8 {" ^
         " let forward = |input| { R01EraseType::<T>(input) }; forward(value) }"),
     ("erased-const-hol-escape", "fn", "N", 0, "",
       "fn R01BodyOnly<const N: usize>(value: u8) -> u8 { R01EraseConst::<\<tau>" ^
         cartouche "'n::len0" ^ ">(value) }"),
     ("erased-self-forward", "chunk", "T", 1, "",
       "impl R01O7Owner { fn erase<T>(value: u8) -> u8 { value }" ^
         " fn body_only<T>(value: u8) -> u8 { Self::erase::<T>(value) } }"),
     ("erased-only-second-const", "fn", "N", 0, "",
       "fn R01BodyOnly<T, const N: usize>(value: u8) -> u8 { R01EraseConst::<N>(value) }"),
     ("erased-type-hol-escape", "fn", "T", 0, "",
       "fn R01BodyOnly<T>(value: u8) -> u8 { R01EraseType::<\<tau>" ^ cartouche "'t" ^ ">(value) }"),
     ("erased-renamed-type", "fn", "T", 1,
       "hol_type_parameters = [\"T\" \<rightarrow> " ^ cartouche "'renamed" ^ "], ",
       "fn R01BodyOnly<T>(value: u8) -> u8 { R01EraseType::<\<tau>" ^ cartouche "'renamed" ^ ">(value) }"),
     ("erased-renamed-const", "fn", "N", 1,
       "hol_type_parameters = [\"N\" \<rightarrow> " ^ cartouche "'size::len0" ^ "], ",
       "fn R01BodyOnly<const N: usize>(value: u8) -> u8 { R01EraseConst::<\<tau>" ^
         cartouche "'size::len0" ^ ">(value) }"),
     ("erased-type-in-nested-block", "fn", "T", 0, "",
       "fn R01BodyOnly<T>(value: u8) -> u8 { { R01EraseType::<T>(value) } }")]
  fun check (label, wrapper, parameter, occurrence, options, rust) =
    let
      val source = (if wrapper = "fn" then fn_command "r01_body_only"
        else fn text => "urust [verbosity = 0] " ^ cartouche text) ("/* \<alpha> */ " ^ rust)
      val source = if options = "" then source else
        declaration "r01_body_only" options "" ("/* \<alpha> */ " ^ rust)
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run thy label source)
      val raw = (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val plain = XML.content_of (YXML.parse_body raw)
      val expected = "urust: generic parameter " ^ parameter ^ " does not occur in the signature"
      val _ = require (label ^ ": exact settled O7 diagnostic") (String.isPrefix expected plain)
      val _ = require (label ^ ": header leaf and native command positions")
        (map position_range (message_positions raw) =
          [range_of source parameter occurrence, (1, if wrapper = "fn" then 9 else 6)])
      val _ = require (label ^ ": complete ordinary/urgent and declaration report streams suppressed")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": original namespace, artifacts, source registrations, schemes and callbacks")
        (snapshot ctxt = prior andalso scheme_snapshot ctxt = prior_schemes andalso
          same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val _ = require_scope_closed label ctxt
      val (recovery, recovery_events) = capture (fn () => run thy (label ^ "-recovery")
        (fn_command "r01_recovery" "fn R01Recovery(value: u8) -> u8 { value }"))
      val recovered = Exn.release recovery |> Toplevel.context_of
      val _ = require (label ^ ": ordinary recovery and declaration reports")
        (is_some (Parser_Test_Calls.lookup recovered "R01Recovery") andalso
          not (null (declaration_reports recovery_events)))
      val _ = require (label ^ ": recovery preserves exact native callbacks")
        (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val _ = require_scope_closed (label ^ "-recovery") recovered
    in () end
  val _ = List.app check rows
  val declared = ":: " ^ cartouche "8 word => ('s, 8 word, 'abort, 'i, 'o) function_body" ^ " "
  val literal = declaration "r01_body_only" "" declared
    "/* \<alpha> */ fn R01BodyOnly<T>(value: T) -> T { R01EraseType::<T>(value) }"
  val (literal_result, literal_events) = capture (fn () => run thy "erased-declared-literal" literal)
  val literal_raw = case literal_result of Exn.Exn exn => Runtime.exn_message exn
    | _ => error "declared literal lost O7 body-only rejection"
  val _ = require "D175 literal HOL signature bypass retains O7 final-HOL anchoring"
    (String.isPrefix "urust: generic parameter T does not occur in the signature"
      (XML.content_of (YXML.parse_body literal_raw)) andalso
       map position_range (message_positions literal_raw) =
         [range_of literal "T" 4, range_of literal "T" 0, (1, 9)] andalso
      null (ordinary literal_events) andalso null (declaration_reports literal_events))
in
  val _ = writeln "U4 A31 exact seven erased-slot negatives plus named/renamed/dual/nested/D175 controls PASS"
end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure M = URust_Type_Mappings
  val root = \<^theory>
  fun declaration target options declared rust =
    "urust_fn [" ^ options ^ "verbosity = 0] " ^ target ^ " " ^ declared ^ cartouche rust
  fun fn_command target rust = declaration target "" "" rust
  val setup =
    fn_command "r01_erase_type" "fn R01EraseType<T>(value: u8) -> u8 { value }" ^ "\n" ^
    fn_command "r01_erase_const" "fn R01EraseConst<const N: usize>(value: u8) -> u8 { value }" ^ "\n" ^
    fn_command "r01_erase_dual" "fn R01EraseDual<T, const N: usize>(value: u8) -> u8 { value }" ^ "\n" ^
    "urust_type \"R01O7Owner\" = " ^ cartouche "unit"
  val (model_result, _) = capture (fn () => run root "o7-erased-model" setup)
  val thy = Exn.release model_result |> Toplevel.theory_of
  val ctxt = Proof_Context.init_global thy
  val prior = snapshot ctxt
  val prior_schemes = scheme_snapshot ctxt
  fun tau text = "\<tau>" ^ cartouche text
  fun body native = "\<epsilon>" ^ cartouche native ^ "(value)"
  fun override name hol = "hol_type_parameters = [\"" ^ name ^ "\" \<rightarrow> " ^ cartouche hol ^ "], "
  val literal_type = ":: " ^ cartouche "'t => 8 word => ('s, 8 word, 'abort, 'i, 'o) function_body" ^ " "
  val renamed_type = ":: " ^ cartouche "'renamed => 8 word => ('s, 8 word, 'abort, 'i, 'o) function_body" ^ " "
  val rows =
    [("unused-type", "", "", ["'t"],
       "fn R01UnusedType<T>(value: u8) -> u8 { value }",
       "fn R01UnusedTypeControl(value: u8) -> u8 { value }"),
     ("unused-const", "", "", ["'n"],
       "fn R01UnusedConst<const N: usize>(value: u8) -> u8 { value }",
       "fn R01UnusedConstControl(value: u8) -> u8 { value }"),
     ("unused-dual", "", "", ["'t", "'n"],
       "fn R01UnusedDual<T, const N: usize>(value: u8) -> u8 { value }",
       "fn R01UnusedDualControl(value: u8) -> u8 { value }"),
     ("unused-local-value-shadow", "", "", ["'t", "'n"],
       "fn R01UnusedShadow<T, const N: usize>(value: u8) -> u8 { let T = value; let N = T; N }",
       "fn R01UnusedShadowControl(value: u8) -> u8 { let T = value; let N = T; N }"),
     ("unused-independent-escape", "", "", ["'t", "'n"],
       "fn R01UnusedEscape<T, const N: usize>(value: u8) -> u8 { R01EraseType::<" ^ tau "nat" ^ ">(value) }",
       "fn R01UnusedEscapeControl(value: u8) -> u8 { " ^ body "r01_erase_type" ^ " }"),
     ("anchored-type", "", "", ["'t"],
       "fn R01AnchorType<T>(marker: T, value: u8) -> u8 { R01EraseType::<T>(value) }",
       "fn R01AnchorTypeControl(marker: " ^ tau "'t" ^ ", value: u8) -> u8 { " ^ body "r01_erase_type" ^ " }"),
     ("anchored-const", "", "", ["'n"],
       "fn R01AnchorConst<const N: usize>(marker: [u8; N], value: u8) -> u8 { R01EraseConst::<N>(value) }",
       "fn R01AnchorConstControl(marker: [u8; " ^ tau "'n::len" ^ "], value: u8) -> u8 { " ^ body "r01_erase_const" ^ " }"),
     ("anchored-dual", "", "", ["'t", "'n"],
       "fn R01AnchorDual<T, const N: usize>(marker: (T, [u8; N]), value: u8) -> u8 { R01EraseDual::<T, N>(value) }",
       "fn R01AnchorDualControl(marker: (" ^ tau "'t" ^ ", [u8; " ^ tau "'n::len" ^ "]), value: u8) -> u8 { " ^ body "r01_erase_dual" ^ " }"),
     ("anchored-renamed-type", override "T" "'renamed", "", ["'renamed"],
       "fn R01RenamedType<T>(marker: T, value: u8) -> u8 { R01EraseType::<" ^ tau "'renamed" ^ ">(value) }",
       "fn R01RenamedTypeControl(marker: " ^ tau "'renamed" ^ ", value: u8) -> u8 { " ^ body "r01_erase_type" ^ " }"),
     ("anchored-renamed-const", override "N" "'size::len", "", ["'size"],
       "fn R01RenamedConst<const N: usize>(marker: [u8; N], value: u8) -> u8 { R01EraseConst::<" ^ tau "'size::len" ^ ">(value) }",
       "fn R01RenamedConstControl(marker: [u8; " ^ tau "'size::len" ^ "], value: u8) -> u8 { " ^ body "r01_erase_const" ^ " }"),
     ("declared-HOL-anchor-bypass", "", literal_type, ["'t"],
       "fn R01LiteralAnchor<T>(marker: UnknownAnchor, value: UnknownValue) -> UnknownReturn { R01EraseType::<T>(value) }",
       "fn R01LiteralAnchorControl(marker: UnknownAnchor, value: UnknownValue) -> UnknownReturn { " ^ body "r01_erase_type" ^ " }"),
     ("declared-renamed-HOL-anchor-bypass", override "T" "'renamed", renamed_type, ["'renamed"],
       "fn R01LiteralRenamed<T>(marker: UnknownAnchor, value: UnknownValue) -> UnknownReturn { R01EraseType::<" ^ tau "'renamed" ^ ">(value) }",
       "fn R01LiteralRenamedControl(marker: UnknownAnchor, value: UnknownValue) -> UnknownReturn { " ^ body "r01_erase_type" ^ " }")]
  val _ = List.app (fn (label, options, declared, expected_names, actual, twin) =>
    let
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val source = declaration "o7_actual" options declared actual ^ "\n" ^
        declaration "o7_twin" "" declared twin ^ "\nlemma o7_twin_identity: " ^
        cartouche "o7_actual = o7_twin" ^ " unfolding o7_actual_def o7_twin_def by (rule refl)"
      val (result, events) = capture (fn () => run thy label source)
      val completed = Exn.release result |> Toplevel.context_of
      val (rust, _) = URust_AST.function_name (parse completed label actual)
      val actual_entry = entry completed rust
      val parameters = entry_scheme completed actual_entry
      val _ = require (label ^ ": ordered including unused/renamed scheme metadata retained")
        (map (fst o #hol) parameters = expected_names)
      val _ = require (label ^ ": complete authored declaration reports retained")
        (not (null (declaration_reports events)))
      val _ = require (label ^ ": registry isolation and original native callbacks")
        (snapshot ctxt = prior andalso scheme_snapshot ctxt = prior_schemes andalso
          same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val _ = require_scope_closed label completed
    in () end) rows
in
  val _ = writeln "U4 A31 unused/anchored Type Const Dual, local shadow, independent escapes, rename and D175 kernel twins PASS"
end
\<close>

text\<open>
Generic use capture observes the actual current scope records without replacing callbacks.
The retained independent observations distinguish native HOL reads from Rust references;
fresh-context, complete-identity, nested and real-interrupt controls exercise both readers.
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  open URust_AST
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val forwarded = Unsynchronized.ref ([]: string list)
  val original : M.generic_parameter =
    {rust = "T", pos = Position.none, kind = Type_Parameter,
     hol = ("'replaced_t", \<^sort>\<open>type\<close>), bounds = [],
     report_reference = fn _ => forwarded := !forwarded @ ["T"]}
  val scoped = M.with_generic_scope {parameters = [original]} ctxt
  val layout = Source_Layout (Position.none, [])
  fun named name =
    Path_Type ([Rust_Type_Path_Segment (name, Position.none, NONE, layout)], layout)
  fun escaped text = HOL_Type_Source (Input.string text)
  fun replace changed_name changed_hol (current: M.generic_parameter) : M.generic_parameter =
    {rust = changed_name, hol = changed_hol, pos = #pos current, kind = #kind current,
     bounds = #bounds current, report_reference = #report_reference current}
  fun observation (label, changed_name, changed_hol, rust_read) =
    let
      val before = length (!forwarded)
      val (_, used) = M.capture_generic_uses scoped (fn observed =>
        let
          val SOME {parameters = [inherited]} = M.generic_scope observed
          val foreign = replace changed_name changed_hol inherited
          val _ = require (label ^ ": fixture changed the inherited callback object")
            (PolyML.pointerEq (#report_reference inherited, #report_reference foreign))
          val replaced = M.with_generic_scope {parameters = [foreign]} observed
          val operand = if rust_read then named changed_name else escaped (fst changed_hol)
          val resolved = the_single (M.resolve_signature replaced [operand])
        in require (label ^ ": did not actually resolve the replacement HOL identity")
          (resolved = TFree changed_hol) end)
      val calls = length (!forwarded) - before
      val _ = require (label ^ ": suppressed or invented original callback calls")
        (if rust_read then calls > 0 else calls = 0)
      val _ = require (label ^ ": exact original callback count")
        (calls = (if rust_read then 1 else 0))
      val _ = Output.writeln ("U4R02-A31-REPLACED-CALLBACK-OBSERVATION " ^ label ^ "\n" ^
        "CAPTURED " ^ ML_Syntax.print_list ML_Syntax.print_string used ^
        "\nORIGINAL-CALLS " ^ string_of_int calls)
    in (label, used) end
  val rows =
    [("changed-HOL-native-control", "T", ("'foreign_t", \<^sort>\<open>type\<close>), false),
     ("changed-HOL-Rust-reference", "T", ("'foreign_t", \<^sort>\<open>type\<close>), true),
     ("changed-Rust-native-control", "U", ("'replaced_t", \<^sort>\<open>type\<close>), false),
     ("changed-Rust-reference", "U", ("'replaced_t", \<^sort>\<open>type\<close>), true)]
  val outcomes = map observation rows
  val SOME {parameters = [after]} = M.generic_scope scoped
  val _ = require "scope replacement changed original context/callbacks"
    (#hol after = #hol original andalso #rust after = #rust original andalso
     PolyML.pointerEq (#report_reference after, #report_reference original) andalso
     is_none (M.generic_scope ctxt))
  val (_, fresh) = M.capture_generic_uses scoped (fn current =>
    ignore (M.resolve_signature current [escaped "nat"]))
  val _ = require "replacement capture contaminated a fresh invocation" (null fresh)
  val unexpected = map #1 (filter_out (null o #2) outcomes)
  val _ = require ("foreign/replaced records retaining inherited callbacks were attributed " ^
    "to the original parameter: " ^ commas unexpected) (null unexpected)
in val _ = Output.writeln "U4R02-A31-REPLACED-CALLBACK-PASS" end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  open URust_AST
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val calls = Unsynchronized.ref ([]: string list)
  val callback = fn _ => calls := !calls @ ["original"]
  val replacement_callback = fn _ => calls := !calls @ ["replacement"]
  val original: M.generic_parameter =
    {rust = "T", pos = Position.none, kind = Type_Parameter,
     hol = ("'identity_t", \<^sort>\<open>type\<close>), bounds = [], report_reference = callback}
  val scoped = M.with_generic_scope {parameters = [original]} ctxt
  val layout = Source_Layout (Position.none, [])
  fun named name = Path_Type
    ([Rust_Type_Path_Segment (name, Position.none, NONE, layout)], layout)
  fun escaped text = HOL_Type_Source (Input.string text)
  fun read current operand = the_single (M.resolve_signature current [operand])
  fun replace rust pos kind hol bounds report_reference: M.generic_parameter =
    {rust = rust, pos = pos, kind = kind, hol = hol, bounds = bounds,
     report_reference = report_reference}
  val changed =
    [("Rust name", replace "U" (#pos original) (#kind original) (#hol original) [] callback),
     ("HOL name", replace "T" (#pos original) (#kind original)
       ("'identity_foreign", \<^sort>\<open>type\<close>) [] callback),
     ("native sort", replace "T" (#pos original) (#kind original)
       ("'identity_t", \<^sort>\<open>len0\<close>) [] callback),
     ("canonical bounds", replace "T" (#pos original) (#kind original)
       (#hol original) ["Scale"] callback),
     ("complete position", replace "T"
       (Position.of_properties [(Markup.fileN, "a32-identity"), (Markup.offsetN, "9"),
         (Markup.end_offsetN, "10")]) (#kind original) (#hol original) [] callback),
     ("callback pointer", replace "T" (#pos original) (#kind original)
       (#hol original) [] replacement_callback)]
  fun observe fresh rust_read (label, foreign: M.generic_parameter) =
    let
      val prior = length (!calls)
      val (_, used) = M.capture_generic_uses scoped (fn current =>
        let
          val SOME {parameters = [inherited]} = M.generic_scope current
          val _ = require (label ^ ": capture preserves exact original scope/callback")
            (pointer_eq (original, inherited) andalso pointer_eq (callback, #report_reference inherited))
          val context = if fresh then Proof_Context.init_global (Proof_Context.theory_of current)
            else current
          val context = M.with_generic_scope {parameters = [foreign]} context
          val operand = if rust_read then named (#rust foreign)
            else escaped (fst (#hol foreign) ^
              (if snd (#hol foreign) = \<^sort>\<open>len0\<close> then "::len0" else ""))
          val actual = read context operand
        in require (label ^ ": replacement resolves actual native identity")
          (actual = TFree (#hol foreign)) end)
      val count = length (!calls) - prior
      val _ = require (label ^ ": excludes complete foreign identity") (null used)
      val _ = require (label ^ ": exact original callback forwarding")
        (count = (if rust_read then 1 else 0))
    in () end
  val _ = List.app (fn row =>
    (observe false true row; observe false false row;
     observe true true row; observe true false row)) changed
  val detached_before = length (!calls)
  val (_, detached) = M.capture_generic_uses scoped (fn current =>
    let
      val independent = Proof_Context.init_global (Proof_Context.theory_of current)
        |> M.with_generic_scope {parameters = [original]}
      val actual = read independent (named "T")
    in require "fresh context preserves exact copied original native identity"
      (actual = TFree (#hol original)) end)
  val _ = require "fresh context with exact original record/callback cannot reach ancestor"
    (null detached andalso length (!calls) = detached_before + 1)
  val len_original = replace "T" Position.none Type_Parameter
    ("'identity_len", \<^sort>\<open>len\<close>) [] callback
  val len_foreign = replace "T" Position.none Const_Parameter (#hol len_original) [] callback
  val len_scoped = M.with_generic_scope {parameters = [len_original]} ctxt
  val (_, kind_uses) = M.capture_generic_uses len_scoped (fn current =>
    let
      val foreign = M.with_generic_scope {parameters = [len_foreign]} current
      val array = URust_Parser.parse_type_source foreign
        (Parser_Lex_Util.text_source "[u8; T]")
      val actual = read foreign array
    in require "kind-only replacement retains correct const length"
      (actual = Type (\<^type_name>\<open>array\<close>, [\<^typ>\<open>8 word\<close>, TFree (#hol len_foreign)])) end)
  val _ = require "kind-only replacement is excluded" (null kind_uses)
  val (_, native_kind) = M.capture_generic_uses len_scoped (fn current =>
    ignore (read (M.with_generic_scope {parameters = [len_foreign]} current)
      (escaped "'identity_len::len")))
  val _ = require "kind-only native observation excluded" (null native_kind)
  val (_, stale) = M.capture_generic_uses scoped (fn current =>
    M.report_generic_reference
      (M.with_generic_scope {parameters = [hd (map #2 changed)]} current)
      original Position.none)
  val _ = require "stale explicit record cannot bypass actual installed scope" (null stale)
  val foreign = hd (map #2 changed)
  val (_, shared) = M.capture_generic_uses scoped (fn current =>
    let
      val same_hol = M.with_generic_scope {parameters = [original, foreign]} current
      (* The real value reader reports the chosen Rust parameter before rejecting a
         type-as-value; the type inference seed table requires distinct HOL names. *)
      val result = Exn.capture (fn () => URust_Resolution.literal_identifier_value
        same_hol URust_Resolution.empty_environment (#rust foreign, Position.none)) ()
    in require "shared HOL name retains actual Rust type-as-value diagnostic"
      (case result of Exn.Exn (ERROR message) => String.isSubstring
        "type parameter U cannot be used as a value" message | _ => false) end)
  val _ = require "unrelated current record sharing HOL name does not claim Rust reference"
    (null shared)
  val reorder_foreign = replace "U" Position.none Type_Parameter
    ("'identity_foreign", \<^sort>\<open>type\<close>) [] callback
  val (_, legitimate) = M.capture_generic_uses scoped (fn current =>
    ignore (read (M.with_generic_scope {parameters = [reorder_foreign, original]} current) (named "T")))
  val _ = require "reordered unchanged record is a legitimate read" (legitimate = ["'identity_t"])
  val start = length (!calls)
  val _ = M.report_generic_reference ctxt original Position.none
  val _ = require "ordinary report callback forwards exactly once without observer"
    (length (!calls) = start + 1)
  val escaped_context = Unsynchronized.ref (NONE: Proof.context option)
  val (_, used) = M.capture_generic_uses scoped (fn current =>
    (escaped_context := SOME current; ignore (read current (named "T"))))
  val _ = require "same-scope Rust read counts" (used = ["'identity_t"])
  val _ = ignore (read (the (!escaped_context)) (named "T"))
  val (_, clean) = M.capture_generic_uses scoped (fn current => ignore (read current (escaped "nat")))
  val _ = require "deactivated invocation does not contaminate later capture" (null clean)
  val SOME {parameters = [after]} = M.generic_scope scoped
  val _ = require "original scope record/callback remain exact" (pointer_eq (original, after)
    andalso pointer_eq (callback, #report_reference after))
in val _ = writeln "U4 A32 complete identity, fresh contexts, installed membership and exact callbacks PASS" end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  open URust_AST
  structure M = URust_Type_Mappings
  structure R = URust_Resolution
  val base = \<^context>
  val calls = Unsynchronized.ref ([]: (string * Position.T) list)
  fun parameter rust hol kind bounds: M.generic_parameter =
    {rust = rust, pos = Position.none, kind = kind, hol = hol, bounds = bounds,
     report_reference = fn pos => calls := !calls @ [(rust, pos)]}
  val t = parameter "T" ("'a32_t", \<^sort>\<open>trait_scale\<close>) Type_Parameter ["Scale"]
  val n = parameter "N" ("'a32_n", \<^sort>\<open>len\<close>) Const_Parameter []
  val scoped = M.with_generic_scope {parameters = [t, n]} base
  val use_pos = Position.of_properties [(Markup.fileN, "a32-routes"),
    (Markup.offsetN, "20"), (Markup.end_offsetN, "21")]
  val layout = Source_Layout (use_pos, [])
  fun named name = Path_Type
    ([Rust_Type_Path_Segment (name, use_pos, NONE, layout)], layout)
  fun path names = UR_Path (Identifier_Head,
    map (fn name => Path_Segment (name, use_pos, NONE)) names, use_pos)
  val env = R.empty_environment
  fun checked current term = Syntax.check_term current (Term_Position.strip_positions term)
  fun equivalent current label actual wanted = require label
    (checked current actual aconv Syntax.read_term current wanted)
  fun routes current t_hol n_hol =
    let
      val SOME {parameters} = M.generic_scope current
      val current = fold (Variable.declare_typ o TFree o #hol) parameters current
      val start = length (!calls)
      val _ = equivalent current "const value route" (R.literal_path_value current env (path ["N"]))
        ("of_nat LENGTH(" ^ n_hol ^ ") :: 64 word")
      val _ = equivalent current "const ordinary route"
        (R.ordinary_identifier_value current env ("N", use_pos))
        ("of_nat LENGTH(" ^ n_hol ^ ") :: 64 word")
      val _ = equivalent current "const repeat route"
        (R.global_constant_path_value current env (path ["N"]))
        ("of_nat LENGTH(" ^ n_hol ^ ") :: 64 word")
      val _ = equivalent current "associated value route"
        (R.literal_path_value current env (path ["T", "CEILING"]))
        ("trait_ceiling TYPE(" ^ t_hol ^ ")")
      val _ = equivalent current "associated repeat route"
        (R.global_constant_path_value current env (path ["T", "CEILING"]))
        ("trait_ceiling TYPE(" ^ t_hol ^ ")")
      val argument_source = Input.source false "N"
        (Position.of_properties [(Markup.fileN, "a32-routes"), (Markup.offsetN, "20")],
         Position.of_properties [(Markup.fileN, "a32-routes"), (Markup.offsetN, "21")])
      val generic = Generic_Args ([Generic_Arg ("N", argument_source)], use_pos)
      val generic_path = UR_Path (Identifier_Head,
        [Path_Segment ("SignatureArray", use_pos, SOME generic)], use_pos)
      val _ = R.function_path current env generic_path 1
      val seen = drop start (!calls)
      val _ = require "all six private reporter consumers forward original callback once"
        (map #1 seen = ["N", "N", "N", "T", "T", "N"] andalso
          forall (fn (_, pos) => Position.properties_of pos = Position.properties_of use_pos) seen)
    in () end
  val (_, same) = M.capture_generic_uses scoped (fn current => routes current "'a32_t" "'a32_n")
  val _ = require "Resolution actual const, associated and turbofish reads captured"
    (sort_strings same = ["'a32_n", "'a32_t"])
  fun changed hol (p: M.generic_parameter): M.generic_parameter =
    {rust = #rust p, pos = #pos p, kind = #kind p, hol = hol, bounds = #bounds p,
     report_reference = #report_reference p}
  val foreign_t = changed ("'a32_foreign_t", \<^sort>\<open>trait_scale\<close>) t
  val foreign_n = changed ("'a32_foreign_n", \<^sort>\<open>len\<close>) n
  fun foreign current = M.with_generic_scope {parameters = [foreign_t, foreign_n]} current
  val (_, replaced) = M.capture_generic_uses scoped
    (fn current => routes (foreign current) "'a32_foreign_t" "'a32_foreign_n")
  val _ = require "all Resolution reporter routes exclude inherited foreign identities" (null replaced)
  val (_, independent) = M.capture_generic_uses scoped (fn current =>
    routes (foreign (Proof_Context.init_global (Proof_Context.theory_of current)))
      "'a32_foreign_t" "'a32_foreign_n")
  val _ = require "fresh context with copied callbacks cannot reach ancestor" (null independent)
  val ((_, inner), outer) = M.capture_generic_uses scoped (fn parent =>
    M.capture_generic_uses parent (fn child => routes child "'a32_t" "'a32_n"))
  val _ = require "same-scope callback observations reach nested parent once"
    (sort_strings inner = ["'a32_n", "'a32_t"] andalso inner = outer)
  val ((_, foreign_inner), foreign_outer) = M.capture_generic_uses scoped (fn parent =>
    M.capture_generic_uses (foreign parent)
      (fn child => routes child "'a32_foreign_t" "'a32_foreign_n"))
  val _ = require "foreign child captures itself while excluding parent"
    (sort_strings foreign_inner = ["'a32_foreign_n", "'a32_foreign_t"] andalso null foreign_outer)
  val ((_, redeclared_inner), redeclared_outer) = M.capture_generic_uses scoped (fn parent =>
    M.capture_generic_uses (foreign parent) (fn child =>
      routes (M.with_generic_scope {parameters = [t, n]} child) "'a32_t" "'a32_n"))
  val _ = require "bare records re-declare without claiming an ancestor declaration"
    (null redeclared_inner andalso null redeclared_outer)
  val original_scope = the (M.binding_scope scoped)
  val ((_, restored_inner), restored_outer) = M.capture_generic_uses scoped (fn parent =>
    M.capture_generic_uses (foreign parent) (fn child =>
      routes (M.with_binding_scope original_scope child) "'a32_t" "'a32_n"))
  val _ = require "restoring the original declaration scope reaches original parent only"
    (null restored_inner andalso sort_strings restored_outer = ["'a32_n", "'a32_t"])
  val before_error = length (!calls)
  val bad = parameter "Bad" ("'a32_bad", \<^sort>\<open>type\<close>) Type_Parameter []
  val errors = Unsynchronized.ref 0
  val error_callback = fn _ => (errors := !errors + 1; error "A32 exact original callback error")
  val throwing: M.generic_parameter =
    {rust = #rust bad, pos = #pos bad, kind = #kind bad, hol = #hol bad,
     bounds = #bounds bad, report_reference = error_callback}
  val throwing_scope = M.with_generic_scope {parameters = [throwing]} base
  val escaped_context = Unsynchronized.ref (NONE: Proof.context option)
  val (_, error_trace) = M.capture_generic_uses throwing_scope (fn parent =>
    let
      val failed = Exn.capture (fn () => M.capture_generic_uses parent (fn child =>
        (escaped_context := SOME child;
         ignore (M.resolve_signature child [named "Bad"])))) ()
    in require "original callback error propagates unchanged"
      (case failed of Exn.Exn (ERROR "A32 exact original callback error") => true | _ => false) end)
  val _ = require "real reference before caught callback error retained in parent"
    (error_trace = ["'a32_bad"] andalso !errors = 1 andalso length (!calls) = before_error)
  val later_error = Exn.capture (fn () =>
    M.report_generic_reference (the (!escaped_context)) throwing use_pos) ()
  val _ = require "deactivated collector preserves later original callback error"
    (case later_error of Exn.Exn (ERROR "A32 exact original callback error") => !errors = 2 | _ => false)
  val (_, clean) = M.capture_generic_uses throwing_scope (fn current =>
    ignore (M.resolve_signature current [HOL_Type_Source (Input.string "nat")]))
  val _ = require "failure and escaped derived context leave fresh capture clean" (null clean)
  val SOME {parameters = original} = M.generic_scope scoped
  val _ = require "route captures preserve complete original records and callback objects"
    (pointer_eq (t, hd original) andalso pointer_eq (n, nth original 1) andalso
      pointer_eq (#report_reference t, #report_reference (hd original)) andalso
      pointer_eq (#report_reference n, #report_reference (nth original 1)))
in val _ = writeln "U4 A32 actual Resolution routes, fresh contexts, nested identity and callback errors PASS" end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  open URust_AST
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val layout = Source_Layout (Position.none, [])
  fun named name = Path_Type
    ([Rust_Type_Path_Segment (name, Position.none, NONE, layout)], layout)
  fun check foreign_read =
    let
      val entered = Single_Assignment.var "A32 original callback entry"
      val blocked = Single_Assignment.var "A32 original callback blocker"
      val finished = Single_Assignment.var "A32 original callback interruption result"
      val calls = Unsynchronized.ref 0
      val callback = fn _ =>
        (calls := !calls + 1; Single_Assignment.assign entered (); Single_Assignment.await blocked)
      val original: M.generic_parameter =
        {rust = "T", pos = Position.none, kind = Type_Parameter,
         hol = ("'a32_interrupt_t", \<^sort>\<open>type\<close>), bounds = [], report_reference = callback}
      val foreign: M.generic_parameter =
        {rust = "U", pos = #pos original, kind = #kind original,
         hol = ("'a32_interrupt_foreign", \<^sort>\<open>type\<close>),
         bounds = #bounds original, report_reference = #report_reference original}
      val scoped = M.with_generic_scope {parameters = [original]} ctxt
      val (_, parent_trace) = M.capture_generic_uses scoped (fn parent =>
        let
          val current = if foreign_read then M.with_generic_scope {parameters = [foreign]} parent
            else parent
          val parameter = if foreign_read then foreign else original
          val thread = Isabelle_Thread.fork
            (Isabelle_Thread.interrupts (Isabelle_Thread.params "A32 reference interruption"))
            (fn () => Single_Assignment.assign finished
              (Exn.capture (fn () => M.capture_generic_uses current (fn child =>
                let
                  val SOME {parameters = [actual]} = M.generic_scope child
                  val _ = require "interrupt capture preserves actual parameter and callback objects"
                    (pointer_eq (parameter, actual) andalso
                      pointer_eq (#report_reference parameter, #report_reference actual))
                in ignore (M.resolve_signature child [named (#rust parameter)]) end)) ()))
          val _ = Single_Assignment.await entered
          val _ = Isabelle_Thread.interrupt_thread thread
          val _ = Isabelle_Thread.join thread
        in require "actual original callback interrupt propagates unchanged"
          (case Single_Assignment.await finished of Exn.Exn exn => Exn.is_interrupt exn | _ => false) end)
      val _ = require "interrupted actual Rust reference retains only same-scope parent trace"
        (parent_trace = (if foreign_read then [] else ["'a32_interrupt_t"]) andalso !calls = 1)
      val (_, fresh) = M.capture_generic_uses scoped (fn current =>
        ignore (M.resolve_signature current [HOL_Type_Source (Input.string "nat")]))
      val _ = require "interrupted collector deactivates and fresh capture is clean" (null fresh)
      val SOME {parameters = [after]} = M.generic_scope scoped
      val _ = require "actual interrupt preserves original caller scope/callback"
        (pointer_eq (original, after) andalso pointer_eq (callback, #report_reference after))
    in () end
  val _ = check false
  val _ = check true
in val _ = writeln "U4 A32 actual same-scope and inherited foreign callback interrupt cleanup PASS" end
\<close>

chapter\<open> Turbofish \<close>

section\<open> Concrete member composition through all four call forms \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val members =
    "fn route<T>(self, value: T) -> T { value }\n" ^
    "fn mixed<T, const N: usize>(self, value: (T, [u8; N])) -> (T, [u8; N]) { value }\n" ^
    "fn ordered<const N: usize, T, const M: usize, U>(self, value: ([T; N], [U; M])) -> ([T; N], [U; M]) { value }\n" ^
    "fn borrowed<'a, T>(self, value: &'a mut T) -> &'a mut T { value }\n" ^
    "fn bounded<T: Scale>(self, value: T) -> T { value }\n" ^
    "fn unused<T: Scale>(self, value: u8) -> u8 { value }\n" ^
    "fn capacity<const N: usize>(self, value: [u8; N]) -> usize { N }"
  val model_text = "urust [verbosity = 0] " ^ cartouche
    ("struct CallMatrixOwner { measure: u8 }\nstruct CallMatrixHolder<V> { payload: V }\n" ^
      "impl CallMatrixOwner { " ^ members ^ " }\n" ^
      "impl CallMatrixHolder<u16> { " ^ members ^ " }")
  val model_state = run thy "call-matrix-model" model_text
  val model = Toplevel.theory_of model_state
  val rows =
    [("route", "u8", "u8", "u8"),
     ("mixed", "u8, 3", "(u8, [u8; 3])", "(u8, [u8; 3])"),
     ("ordered", "3, u8, 4, u16", "([u8; 3], [u16; 4])", "([u8; 3], [u16; 4])"),
     ("borrowed", "u8", "&mut u8", "&mut u8"),
     ("bounded", "\<tau>" ^ cartouche "nat", "\<tau>" ^ cartouche "nat", "\<tau>" ^ cartouche "nat"),
     ("unused", "\<tau>" ^ cartouche "nat", "u8", "u8"),
     ("capacity", "3", "[u8; 3]", "usize")]
  fun case_source form (member, arguments, parameter_type, result_type) =
    let
      val name = "CallMatrix" ^ form ^ member
      val owner = if form = "Selected" then "CallMatrixHolder<u16>" else "CallMatrixOwner"
      val native = if form = "Selected" then "call_matrix_holder_" ^ member else "call_matrix_owner_" ^ member
      val prefix = if form = "Selected" then "CallMatrixHolder::<u16>::" else "CallMatrixOwner::"
      val call = if form = "Dot" then "owner." ^ member ^ "::<" ^ arguments ^ ">(value)"
        else prefix ^ member ^ "::<" ^ arguments ^ ">(owner, value)"
      val parameter_clause = "(owner: " ^ owner ^ ", value: " ^ parameter_type ^ ") -> " ^ result_type
      (* Explicit HOL names keep the fixture independent of automatic snake-case word splitting. *)
      val actual = "urust_fn [verbosity = 0] matrix_actual " ^ cartouche
        ("fn " ^ name ^ parameter_clause ^ " { " ^ call ^ " }")
      val twin = "urust_fn [verbosity = 0] matrix_twin " ^ cartouche
        ("fn " ^ name ^ "Twin" ^ parameter_clause ^ " { \<epsilon>" ^ cartouche native ^ "(owner, value) }")
    in actual ^ "\n" ^ twin ^ "\nlemma matrix_refl: " ^ cartouche "matrix_actual = matrix_twin" ^
      " unfolding matrix_actual_def matrix_twin_def by (rule refl)" end
  val _ = List.app (fn form => List.app (fn row =>
    ignore (run model ("call-matrix-" ^ form ^ "-" ^ #1 row) (case_source form row))) rows)
    ["Concrete", "Selected", "Dot"]
  val self_rows =
    [("route", "T", "T", "T", "T"),
     ("mixed", "T, const N: usize", "T, N", "(T, [u8; N])", "(T, [u8; N])"),
     ("ordered", "const N: usize, T, const M: usize, U", "N, T, M, U", "([T; N], [U; M])", "([T; N], [U; M])"),
     ("borrowed", "'a, T", "T", "&'a mut T", "&'a mut T"),
     ("bounded", "T: Scale", "T", "T", "T"),
     ("unused", "T: Scale", "T", "u8", "u8"),
     ("capacity", "const N: usize", "N", "[u8; N]", "usize")]
  fun self_source anchored (member, generics, arguments, parameter_type, result_type) =
    let
      val marker = if anchored then "marker: T, " else ""
      val parameter_clause = "<" ^ generics ^ ">(self, " ^ marker ^ "value: " ^ parameter_type ^ ") -> " ^ result_type
      val actual = "urust [verbosity = 0] " ^ cartouche
        ("impl CallMatrixOwner {\n\<omega>" ^ cartouche "name = \"matrix_actual\"" ^
          "\nfn Forward" ^ parameter_clause ^ " { Self::" ^ member ^ "::<" ^ arguments ^ ">(self, value) } }")
      val twin = "urust_fn [verbosity = 0] matrix_twin " ^ cartouche
        ("fn MatrixTwin<" ^ generics ^ ">(self: CallMatrixOwner, " ^ marker ^ "value: " ^ parameter_type ^ ") -> " ^
          result_type ^ " { \<epsilon>" ^ cartouche ("call_matrix_owner_" ^ member) ^ "(self, value) }")
    in (actual, twin, actual ^ "\n" ^ twin ^ "\nlemma matrix_refl: " ^ cartouche "matrix_actual = matrix_twin" ^
        " unfolding matrix_actual_def matrix_twin_def by (rule refl)") end
  val _ = List.app (fn row =>
    ignore (run model ("call-matrix-Self-" ^ #1 row) (#3 (self_source (#1 row = "unused") row)))) self_rows
  (* The original erased-slot caller is preserved in full as a positioned atomic O7 negative.
     Its exact escape declaration remains a successful unused-parameter control. *)
  val original_unused = ("unused", "T: Scale", "T", "u8", "u8")
  val (_, original_twin, original_source) = self_source false original_unused
  val model_ctxt = Proof_Context.init_global model
  val model_snapshot = snapshot model_ctxt
  val model_schemes = scheme_snapshot model_ctxt
  val callbacks = saved_callbacks ()
  val reporter = !Private_Output.report_fn
  val (rejected, failed_events) = capture (fn () =>
    run model "call-matrix-Self-unused-original" original_source)
  val diagnostic = case rejected of Exn.Exn exn => Runtime.exn_message exn
    | _ => error "original body-only Self forwarding unexpectedly accepted"
  val _ = require "exact original Self forwarding has O7 header/native command positions"
    (String.isPrefix "urust: generic parameter T does not occur in the signature"
      (XML.content_of (YXML.parse_body diagnostic)) andalso
      map position_range (message_positions diagnostic) = [range_of original_source "T" 0, (1, 6)])
  val _ = require "original Self failure preserves complete streams, namespace, schemes and callbacks"
    (null (ordinary failed_events) andalso null (declaration_reports failed_events) andalso
      snapshot model_ctxt = model_snapshot andalso scheme_snapshot model_ctxt = model_schemes andalso
      same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
  val (escape_result, escape_events) = capture (fn () => run model "call-matrix-Self-unused-escape"
    (original_twin ^ "\nurust_fn [verbosity = 0] matrix_escape_control " ^ cartouche
      ("fn MatrixEscapeControl(self: CallMatrixOwner, value: u8) -> u8 { \<epsilon>" ^
        cartouche "call_matrix_owner_unused" ^ "(self, value) }") ^
      "\nlemma original_escape_identity: " ^ cartouche "matrix_twin = matrix_escape_control" ^
      " unfolding matrix_twin_def matrix_escape_control_def by (rule refl)"))
  val escape_ctxt = Exn.release escape_result |> Toplevel.context_of
  val _ = require "exact original escape keeps unused T and declaration reports"
    (map #rust (entry_scheme escape_ctxt (entry escape_ctxt "MatrixTwin")) = ["T"] andalso
      not (null (declaration_reports escape_events)))
  val concrete_unused = ("unused", "T: Scale", "\<tau>" ^ cartouche "nat", "u8", "u8")
  val (unused_result, unused_events) = capture (fn () => run model "call-matrix-Self-genuinely-unused"
    (#3 (self_source false concrete_unused)))
  val unused_ctxt = Exn.release unused_result |> Toplevel.context_of
  val _ = require "unused caller T accepts concrete erased-slot forwarding and native twin"
    (map #rust (entry_scheme unused_ctxt (entry unused_ctxt "CallMatrixOwner::Forward")) = ["T"] andalso
      not (null (declaration_reports unused_events)))
  val _ = require "original/anchored/concrete forwarding restores callbacks and closes scope"
    (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
  val _ = List.app (require_scope_closed "Self erased-slot reconciliation") [escape_ctxt, unused_ctxt, model_ctxt]
in end
\<close>

section\<open> Positioned member argument errors and complete recovery controls \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val members =
    "fn route<T>(self, value: T) -> T { value }\n" ^
    "fn mixed<T, const N: usize>(self, value: (T, [u8; N])) -> (T, [u8; N]) { value }\n" ^
    "fn ordered<const N: usize, T, const M: usize, U>(self, value: ([T; N], [U; M])) -> ([T; N], [U; M]) { value }\n" ^
    "fn borrowed<'a, T>(self, value: &'a mut T) -> &'a mut T { value }\n" ^
    "fn bounded<T: Scale>(self, value: T) -> T { value }\n" ^
    "fn unused<T: Scale>(self, value: u8) -> u8 { value }\n" ^
    "fn capacity<const N: usize>(self, value: [u8; N]) -> usize { N }"
  val model_text = "urust [verbosity = 0] " ^ cartouche
    ("struct CallMatrixOwner { measure: u8 }\nstruct CallMatrixHolder<V> { payload: V }\n" ^
      "impl CallMatrixOwner { " ^ members ^ " }\n" ^
      "impl CallMatrixHolder<u16> { " ^ members ^ " }")
  val model_state = run thy "call-matrix-model" model_text
  val model = Toplevel.theory_of model_state
  val prefix = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ "
  val rows =
    [("wrong-count", "route", "u8, u16", "u8", "u8", ""),
     ("const-in-type-slot", "route", "3", "u8", "u8", ""),
     ("type-in-const-slot", "capacity", "bool", "[u8; 3]", "usize", ""),
     ("bool-const-value", "capacity", "true", "[u8; 3]", "usize", ""),
     ("trait-bound", "bounded", "u8", "u8", "u8", ""),
     ("unused-trait-bound", "unused", "u8", "u8", "u8", ""),
     ("propagated-bound", "bounded", "T", "T", "T", "<T: Marker>"),
     ("suffixed-const", "capacity", "3usize", "[u8; 3]", "usize", "")]
  fun case_source form (label, member, arguments, parameter_type, result_type, generics) =
    let
      val owner = if form = "Selected" then "CallMatrixHolder<u16>" else "CallMatrixOwner"
      val path = if form = "Selected" then "CallMatrixHolder::<u16>::" else
        if form = "Self" then "Self::" else "CallMatrixOwner::"
      val call = if form = "Dot" then "owner." ^ member ^ "::<" ^ arguments ^ ">(value)"
        else path ^ member ^ "::<" ^ arguments ^ ">(" ^
          (if form = "Self" then "self" else "owner") ^ ", value)"
      val parameter_clause = generics ^ "(" ^
        (if form = "Self" then "self" else "owner: " ^ owner) ^
        ", value: " ^ parameter_type ^ ") -> " ^ result_type
      val item = "fn MatrixError" ^ parameter_clause ^ " { " ^ call ^ " }"
    in if form = "Self" then "urust [verbosity = 0] " ^ cartouche
        (prefix ^ "impl CallMatrixOwner { " ^ item ^ " }")
       else "urust_fn [verbosity = 0] matrix_error " ^ cartouche (prefix ^ item) end
  val original = Proof_Context.init_global model
  val original_snapshot = snapshot original
  val original_schemes = scheme_snapshot original
  fun expected "wrong-count" = "wrong number of generic arguments"
    | expected "const-in-type-slot" = "wrong type or const kind"
    | expected "type-in-const-slot" = "wrong type or const kind"
    | expected "bool-const-value" = "Parse Error"
    | expected "suffixed-const" = "complete unsuffixed integer literals"
    | expected _ = "does not satisfy sort trait_scale"
  fun expected_range text (label, _, arguments, _, _, _) =
    if label = "wrong-count" then range_of text ("::<" ^ arguments ^ ">") 0
    else if label = "propagated-bound" then range_of text arguments 3
    else if label = "trait-bound" orelse label = "unused-trait-bound"
    then range_of text arguments 2 else range_of text arguments 0
  val _ = List.app (fn form => List.app (fn row =>
    let
      val label = "matrix-error-" ^ form ^ "-" ^ #1 row
      val text = case_source form row
      val callbacks = saved_callbacks ()
      val report_callback = !Private_Output.report_fn
      val (result, events) = capture (fn () => run model label text)
      val diagnostic = (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
      val _ = require (label ^ ": wrong diagnostic: " ^ diagnostic)
        (String.isSubstring (expected (#1 row)) (XML.content_of (YXML.parse_body diagnostic)))
      val ranges = map position_range (message_positions diagnostic)
      val _ = require (label ^ ": exact generic-list/argument leaf range changed")
        (not (null ranges) andalso hd ranges = expected_range text row)
      val _ = require (label ^ ": failed member call leaked complete ordinary/urgent/report streams")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": call error failed to restore exact callbacks")
        (same_callbacks callbacks andalso PolyML.pointerEq (report_callback, !Private_Output.report_fn))
      val _ = require (label ^ ": failed member mutated native source registries/theory/schemes")
        (snapshot (Proof_Context.init_global model) = original_snapshot andalso
         scheme_snapshot (Proof_Context.init_global model) = original_schemes)
      val (recovery, _) = capture (fn () => run model (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche "fn CallMatrixRecovery(value: u8) -> u8 { value }"))
      val _ = require (label ^ ": call error blocked ordinary subsequent declaration")
        (is_some (Parser_Test_Calls.lookup (Exn.release recovery |> Toplevel.context_of) "CallMatrixRecovery"))
    in () end) rows) ["Concrete", "Selected", "Self", "Dot"]
in end
\<close>

section\<open> Typed payloads, caller sharing and immutable callback boundaries \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure D = Micro_Rust_Dispatch
  structure N = Micro_Rust_Names
  val ctxt = @{context}
  val thy = Proof_Context.theory_of ctxt
  val pos = Position.of_properties
    [(Markup.lineN, "3"), (Markup.offsetN, "21"), (Markup.end_offsetN, "26"),
     Markup.fileN |> rpair "typed-occurrence", Markup.idN |> rpair "typed-id",
     ("custom", "position with separators : , ;")]
  val qualifier = Position.of_properties
    [(Markup.offsetN, "11"), (Markup.end_offsetN, "15"), (Markup.fileN, "typed-occurrence")]
  val positions = {terminal_pos = pos, qualifier_positions = [qualifier], backend_only_positions = [pos]}
  val marker = D.mk_marker_positions_with_backend_targets N.NFunction "SignatureIdentity"
    pos [qualifier] [pos]
    (Free ("SignatureIdentity", dummyT))
  val [entry] = N.lookups ctxt N.NFunction "SignatureIdentity"
  val filters = [N.Exclude_Method_Only, N.Only_Sources [#serial entry]]
  val _ = List.app (fn arguments =>
    let
      val metadata: D.generic_arguments = {arguments = arguments, pos = pos}
      val wrapped = D.with_generic_arguments metadata marker
      val actual = the (D.marker_generic_arguments wrapped)
      val _ = require "typed payload preserves exact ordinary marker destructuring"
        (D.dest_marker_untyped marker = D.dest_marker_untyped wrapped)
      val _ = require "typed payload preserves types and every source position property"
        (#arguments actual = arguments andalso #pos actual = pos)
      val _ = require "typed payload and source/method filters compose in both orders"
        (D.restrict_backends filters wrapped aconv
          D.with_generic_arguments metadata (D.restrict_backends filters marker))
      val _ = ignore (failure "duplicate typed payload" "malformed urust_dispatch generic arguments"
        (fn () => D.with_generic_arguments metadata wrapped))
    in () end)
    [[], [(@{typ nat}, pos)], [(@{typ nat}, pos), (@{typ "3"}, qualifier)]]
  val ordinary = D.mk_payload_positions N.NFunction "SignatureIdentity" positions
  val _ = require "unrelated native product payload remains unrelated"
    (is_none (D.dest_payload (HOLogic.mk_prod (ordinary, HOLogic.unit))))
  val _ = ignore (failure "malformed generic positions" "malformed urust_dispatch generic arguments"
    (fn () => D.dest_payload (Free (D.generic_position_name [], dummyT))))
  val _ = List.app (fn index =>
    let
      val caller = TVar (("_urust_function_type", index), @{sort type})
      val metadata: D.generic_arguments = {arguments = [(caller, pos)], pos = pos}
      val expected = the (URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt (#serial entry)
        (#hol_term entry) (#arguments metadata))
      val [candidate] = D.filtered_candidates_with_generics ctxt filters N.NFunction "SignatureIdentity"
        (fastype_of expected) (SOME metadata)
      val _ = require "final native dispatch preserves low/high/overlapping explicit caller indexes"
        (Library.member (op =) (Term.add_tvars (#term candidate) [])
          (("_urust_function_type", index), @{sort type}))
      val _ = require "final native dispatch preserves the selected source serial"
        (#serial (#entry candidate) = #serial entry)
      val typ = fastype_of (#term candidate)
      val argument = hd (binder_types typ)
      val Type (_, channels) = body_type typ
      val _ = require "explicit generic parameter does not capture independent effect channels"
        (argument = caller andalso forall (fn channel => channel <> caller)
          [nth channels 0, nth channels 2, nth channels 3, nth channels 4])
    in () end) [0, 2, 700, 9017]
  val [shared_entry] = N.lookups ctxt N.NFunction "SignatureChannels"
  val caller = TVar (("caller_shared", 9017), @{sort type})
  val metadata: D.generic_arguments = {arguments = [(caller, pos)], pos = pos}
  val expected = the (URust_Type_Mappings.instantiate_generic_scheme_for_source ctxt (#serial shared_entry)
    (#hol_term shared_entry) (#arguments metadata))
  val [shared] = D.filtered_candidates_with_generics ctxt [N.Only_Sources [#serial shared_entry]]
    N.NFunction "SignatureChannels" (fastype_of expected) (SOME metadata)
  val Type (_, channels) = body_type (fastype_of (#term shared))
  val _ = require "intentional generic/effect-channel sharing survives final dispatch"
    (hd (binder_types (fastype_of (#term shared))) = caller andalso hd channels = caller)
  val active = the (D.Generic_Transform.get thy)
  val _ = ignore (failure "callback replacement" "already registered" (fn () =>
    D.register_generic_candidate_transform (Binding.make ("replacement", pos)) (#transform active) thy))
  val empty = D.Generic_Transform.put NONE thy |> Theory.end_theory
  fun fresh label parents = Theory.begin_theory (label, Position.none) parents
  val registered = fresh "U4CallbackRegistered" [empty]
    |> D.register_generic_candidate_transform (Binding.make ("left", pos)) (#transform active)
    |> Theory.end_theory
  val empty_branch = fresh "U4CallbackEmpty" [empty] |> Theory.end_theory
  val identity = #identity (the (D.Generic_Transform.get registered))
  val _ = List.app (fn parents =>
    let val joined = fresh ("U4CallbackJoin" ^ string_of_int (serial ())) parents
    in require "immutable callback empty merge preserves registration identity"
      (#identity (the (D.Generic_Transform.get joined)) = identity) end)
    [[registered, empty_branch], [empty_branch, registered]]
  val replay_left = fresh "U4CallbackReplayLeft" [registered] |> Theory.end_theory
  val replay_right = fresh "U4CallbackReplayRight" [registered] |> Theory.end_theory
  val replay = fresh "U4CallbackReplayJoin" [replay_left, replay_right]
  val _ = require "immutable callback same-identity replay merges idempotently"
    (#identity (the (D.Generic_Transform.get replay)) = identity)
  val other_pos = Position.of_properties
    [(Markup.offsetN, "41"), (Markup.end_offsetN, "47"), (Markup.fileN, "callback-right")]
  val independent = fresh "U4CallbackIndependent" [empty]
    |> D.register_generic_candidate_transform (Binding.make ("right", other_pos)) (#transform active)
    |> Theory.end_theory
  val conflict = failure "callback merge conflict" "Conflicting uRust generic candidate transformations"
    (fn () => fresh "U4CallbackConflict" [registered, independent])
  val _ = require "immutable callback conflict preserves both native declaration positions"
    (map position_range (message_positions conflict) = [position_range pos, position_range other_pos])
in end
\<close>

section\<open> Overloaded generated sources and covered explicit registrations \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val datatype_text = "urust_datatype [verbosity = 0] " ^
    cartouche "struct DispatchOwner<V> { payload: V }"
  val explicit = "micro_rust_notation (call) " ^
    cartouche "\<lambda>(_ :: 8 word dispatch_owner) (value :: (8 word, 'n::len) array). FunctionBody (literal value)" ^
    " (\"DispatchOwner::pick\")"
  val members = "urust [verbosity = 0] " ^ cartouche
    ("impl DispatchOwner<u8> {\n\<omega>" ^ cartouche "abbrev, name = \"dispatch_byte_pick\"" ^
      "\nfn pick<T>(self, value: [u8; \<tau>" ^ cartouche "'t" ^ "]) -> [u8; \<tau>" ^ cartouche "'t" ^ "] { value }\n" ^
      "\<omega>" ^ cartouche "name = \"dispatch_byte_shape\"" ^
      "\nfn shape<T>(self, value: T) -> T { value }\n" ^
      "\<omega>" ^ cartouche "name = \"dispatch_byte_count\"" ^
      "\nfn count<T>(self, value: T) -> T { value }\n}\n" ^
      "impl DispatchOwner<u16> {\n\<omega>" ^ cartouche "abbrev, name = \"dispatch_half_pick\"" ^
      "\nfn pick<const N: usize>(self, value: [u8; N]) -> [u8; N] { value }\n" ^
      "\<omega>" ^ cartouche "name = \"dispatch_half_shape\"" ^
      "\nfn shape<T>(self, value: [T; 3]) -> [T; 3] { value }\n" ^
      "\<omega>" ^ cartouche "name = \"dispatch_half_count\"" ^
      "\nfn count<T, U>(self, value: (T, U)) -> (T, U) { value }\n}")
  fun model with_explicit first =
    let
      val text = datatype_text ^ "\n" ^
        (if with_explicit andalso first then explicit ^ "\n" else "") ^ members ^ "\n" ^
        (if with_explicit andalso not first then explicit ^ "\n" else "") ^
        "urust_type \"DispatchSize\" = " ^ cartouche "3"
      val (result, _) = capture (fn () => run thy "dispatch-model" text)
    in Exn.release result |> Toplevel.theory_of end
  val pristine = model false false
  val ctxt = Proof_Context.init_global pristine
  val sources = Parser_Test_Calls.entries ctxt "DispatchOwner::pick"
  val _ = require "same-count overloads retain distinct type/const sources despite identical len sorts"
    (length sources = 2 andalso
     sort (int_ord) (map (fn source => case #kind (hd (entry_scheme ctxt source)) of
       Type_Parameter => 0 | Const_Parameter => 1) sources) = [0, 1] andalso
     forall (fn source => snd (#hol (hd (entry_scheme ctxt source))) = @{sort len}) sources)
  fun twin model label owner parameter_type result_type arguments member head backend generics =
    let
      val parameter_clause = generics ^ "(owner: " ^ owner ^ ", value: " ^ parameter_type ^ ") -> " ^ result_type
      val call = if head = "owner" then "owner." ^ member ^ "::<" ^ arguments ^ ">(value)"
        else head ^ "::" ^ member ^ "::<" ^ arguments ^ ">(owner, value)"
      val actual = "urust_fn [verbosity = 0] overload_actual " ^ cartouche
        ("fn OverloadActual" ^ parameter_clause ^ " { " ^ call ^ " }")
      val direct = "urust_fn [verbosity = 0] overload_twin " ^ cartouche
        ("fn OverloadTwin" ^ parameter_clause ^ " { \<epsilon>" ^ cartouche backend ^ "(owner, value) }")
      val proof = "lemma overload_refl: " ^ cartouche "overload_actual = overload_twin" ^
        " unfolding overload_actual_def overload_twin_def by (rule refl)"
      val (result, _) = capture (fn () => run model label (actual ^ "\n" ^ direct ^ "\n" ^ proof))
    in ignore (Exn.release result) end
  val _ = twin pristine "overload-type-source" "DispatchOwner<u8>" "[u8; 3]" "[u8; 3]"
    "DispatchSize" "pick" "DispatchOwner::<u8>" "dispatch_byte_pick" ""
  val _ = twin pristine "overload-const-source" "DispatchOwner<u16>" "[u8; 3]" "[u8; 3]"
    "3" "pick" "DispatchOwner::<u16>" "dispatch_half_pick" ""
  val _ = twin pristine "overload-neutral-type" "DispatchOwner<u8>" "[u8; 3]" "[u8; 3]"
    ("\<tau>" ^ cartouche "3") "pick" "owner" "dispatch_byte_pick" ""
  val _ = twin pristine "overload-neutral-const" "DispatchOwner<u16>" "[u8; 3]" "[u8; 3]"
    ("\<tau>" ^ cartouche "3") "pick" "owner" "dispatch_half_pick" ""
  val _ = twin pristine "overload-scoped-type-kind" "DispatchOwner<u8>"
    ("[u8; \<tau>" ^ cartouche "'t" ^ "]") ("[u8; \<tau>" ^ cartouche "'t" ^ "]")
    "T" "pick" "owner" "dispatch_byte_pick" "<T>"
  val _ = twin pristine "overload-scoped-const-kind" "DispatchOwner<u16>" "[u8; N]" "[u8; N]"
    "N" "pick" "owner" "dispatch_half_pick" "<const N: usize>"
  val _ = twin pristine "overload-scalar-shape" "DispatchOwner<u8>" "u8" "u8"
    "u8" "shape" "owner" "dispatch_byte_shape" ""
  val _ = twin pristine "overload-array-shape" "DispatchOwner<u16>" "[u8; 3]" "[u8; 3]"
    "u8" "shape" "owner" "dispatch_half_shape" ""
  val _ = twin pristine "overload-one-count" "DispatchOwner<u8>" "u8" "u8"
    "u8" "count" "owner" "dispatch_byte_count" ""
  val _ = twin pristine "overload-two-count" "DispatchOwner<u16>" "(u8, u16)" "(u8, u16)"
    "u8, u16" "count" "owner" "dispatch_half_count" ""
  val wrong = "urust_fn [verbosity = 0] " ^ cartouche
    "fn OverloadWrong(owner: DispatchOwner<u8>, value: [u8; 3]) -> [u8; 3] { DispatchOwner::<u8>::pick::<3>(owner, value) }"
  val diagnostic = failure "selected source kind" "wrong type or const kind"
    (fn () => run pristine "selected-source-kind" wrong)
  val _ = require "selected source filters intersect argument-kind eligibility at the exact argument"
    (hd (map position_range (message_positions diagnostic)) = range_of wrong "3" 2)
  val _ = List.app (fn first =>
    let
      val model = model true first
      val current = Proof_Context.init_global model
      val entries = Parser_Test_Calls.entries current "DispatchOwner::pick"
      val generated = filter (fn source => Micro_Rust_Names.is_automatic_serial
        (Context.Proof current) (#serial source)) entries
      val _ = require "covered explicit registration retains both original automatic source serials"
        (length generated = 2 andalso length (filter (Micro_Rust_Names.is_automatic current) generated) = 1)
      val text = "urust_fn [verbosity = 0] " ^ cartouche
        "fn CoveredCall(owner: DispatchOwner<u8>, value: [u8; 3]) -> [u8; 3] { DispatchOwner::<u8>::pick::<DispatchSize>(owner, value) }"
      val (result, events) = capture (fn () => run model "covered-explicit" text)
      val diagnostic = case result of Exn.Res _ => error "covered explicit call unexpectedly accepted"
        | Exn.Exn exn => Runtime.exn_message exn
      val _ = require "stored covered explicit provenance rejects a mixed generic key in both insertion orders"
        (String.isSubstring "the key has generated functions and explicit call notations" diagnostic)
      val _ = require "mixed-key rejection is positioned at the exact generic list and emits no definitions"
        (hd (map position_range (message_positions diagnostic)) = range_of text "::<DispatchSize>" 0 andalso
         null (ordinary events) andalso null (declaration_reports events))
      val _ = twin model "source-filter-unrelated-explicit" "DispatchOwner<u16>" "[u8; 3]" "[u8; 3]"
        "3" "pick" "DispatchOwner::<u16>" "dispatch_half_pick" ""
      val ordinary = "urust_fn [verbosity = 0] " ^ cartouche
        "fn CoveredOrdinary(owner: DispatchOwner<u8>, value: [u8; 3]) -> [u8; 3] { DispatchOwner::<u8>::pick(owner, value) }"
      val (ordinary_result, _) = capture (fn () => run model "covered-ordinary" ordinary)
      val _ = ignore (Exn.release ordinary_result)
    in () end) [false, true]
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  val model_text = "urust_datatype [verbosity = 0] " ^ cartouche "struct ControlOwner<V> { payload: V }" ^ "\n" ^
    "urust [verbosity = 0] " ^ cartouche
      "impl ControlOwner<u8> {\n\<omega>\<open>name = \"control_owner_plain_byte\"\<close>\nfn plain(value: u8) -> u8 { value } }\nimpl ControlOwner<u16> {\n\<omega>\<open>name = \"control_owner_plain_half\"\<close>\nfn plain<T>(value: T) -> T { value } }"
  val (prepared, _) = capture (fn () => run thy "extra-call-model" model_text)
  val model = Exn.release prepared |> Toplevel.theory_of
  val ctxt = Proof_Context.init_global model
  val state = snapshot ctxt
  val schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " marker " ^ Symbol.close ^ " */ "
  val rows =
    [("selected-monomorphic", "generic arguments are not supported on generated Rust function paths",
      "fn ExtraCall(value: u8) -> u8 { ControlOwner::<u8>::plain::<1>(value) }", "::<1>", 0),
     ("unused-sort", "does not satisfy sort", "fn ExtraCall(value: u8) -> u8 { CallUnusedScale::<bool>(value) }", "bool", 0),
     ("abbrev-count", "wrong number of generic arguments", "fn ExtraCall(value: u8) -> u8 { SignatureAbbrevOther::<u8>(value) }", "::<u8>", 0),
     ("const-kind", "wrong type or const kind", "fn ExtraCall(value: u8) -> u8 { SignatureIdentity::<3>(value) }", "3", 0),
     ("type-kind", "wrong type or const kind", "fn ExtraCall(value: [u8; 3]) -> [u8; 3] { SignatureArray::<u8>(value) }", "u8", 2),
     ("wrong-concrete-owner", "no associated function preserve in impls of GenericHolder<u8>",
      "fn ExtraCall(value: u8) -> u8 { GenericHolder::<u8>::preserve::<u8>(value) }", "preserve", 0)]
  fun check (label, expected, rust, token, occurrence) =
    let
      val text = "urust_fn [verbosity = 0] " ^ cartouche (prefix ^ rust)
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run model label text)
      val raw = case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val visible = XML.content_of (YXML.parse_body raw)
      val _ = require (label ^ ": unexpected diagnostic " ^ visible) (String.isSubstring expected visible)
      val _ = require (label ^ ": exact argument/member source range")
        (hd (map position_range (message_positions raw)) = range_of text token occurrence)
      val _ = require (label ^ ": complete output/report suppression")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": exact callback restoration")
        (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val current = Proof_Context.init_global model
      val _ = require (label ^ ": immutable namespace/registration/scheme/scope snapshot")
        (snapshot current = state andalso scheme_snapshot current = schemes)
      val (recovered, _) = capture (fn () => run model (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche "fn CallRecovery(value: u8) -> u8 { value }"))
      val _ = require (label ^ ": ordinary recovery")
        (is_some (Parser_Test_Calls.lookup (Exn.release recovered |> Toplevel.context_of) "CallRecovery"))
    in () end
  val _ = List.app check rows
  val _ = List.app (fn (label, expected, call) =>
    ignore (failure label expected (fn () => run thy label ("urust_fn [verbosity = 0] " ^ cartouche
      ("fn CallSyntax(value: u8) -> u8 { " ^ call ^ " }")))))
    [("empty-turbofish", "syntax error", "SignatureIdentity::<>(value)"),
     ("explicit-lifetime", "unexpected input", "SignatureBorrowed::<'a, u8>(value)"),
     ("associated-type-binding", "unexpected input", "SignatureIdentity::<Item = u8>(value)"),
     ("const-expression", "unexpected input", "SignatureArray::<{ 3 }>(value)"),
     ("bare-method", "is a method", "keep::<u8>(value)")]
  val _ = writeln "U4 selected monomorphic/unused/abbrev/kind/owner exact atomic errors and inherited syntax/method controls PASS"
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = @{theory}
  fun collect_order (XML.Text _) = []
    | collect_order (XML.Elem (markup, body)) = markup :: maps collect_order body
  fun markup events = maps collect_order (trees "report" events)
  fun at text token occurrence props = position_range (Position.of_properties props) = range_of text token occurrence
  fun plain text = XML.content_of (YXML.parse_body text)
    |> Symbol.explode |> filter_out Symbol.is_control |> implode
  fun typings range (XML.Text _) = []
    | typings range (XML.Elem ((name, props), body)) =
        (if name = Markup.typingN andalso position_range (Position.of_properties props) = range
         then [plain (XML.content_of body)] else []) @ maps (typings range) body
  val prefix = "/* " ^ Symbol.open_ ^ " navigation " ^ Symbol.close ^ " */ "
  val source = "urust_fn [verbosity = 0] " ^ cartouche (prefix ^
    "fn CallMarkup<T: Scale, const N: usize>(value: (T, [u8; N])) -> (T, [u8; N]) { SignatureMixed::<T, N>(value) }")
  val (result, events) = capture (fn () => run thy "call-argument-markup" source)
  val ctxt = Exn.release result |> Toplevel.context_of
  val parameters = entry_scheme ctxt (entry ctxt "CallMarkup")
  val properties = markup events
  val _ = List.app (fn (rust, occurrence, parameter) =>
    let
      val definitions = properties |> map_filter (fn (element, props) =>
        if element = Markup.entityN andalso at source rust 0 props andalso
          Properties.get props Markup.kindN = SOME "urust_generic_parameter"
        then Properties.get props Markup.defN else NONE)
      val _ = require "turbofish argument navigates to exact generic declaration after escaped comment"
        (length definitions = 1 andalso exists (fn (element, props) =>
          element = Markup.entityN andalso at source rust occurrence props andalso
          Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
          Properties.get props Markup.refN = SOME (hd definitions)) properties)
      val expected = plain (rust ^ " = " ^ Syntax.string_of_typ
        (Config.put show_sorts true ctxt) (TFree (#hol parameter)))
      val _ = List.app (fn index => require "turbofish header/use typing is Rust labelled with final sort"
        (Library.member (op =) (maps (typings (range_of source rust index)) (trees "report" events)) expected))
        [0, occurrence]
    in () end) [("T", 3, hd parameters), ("N", 3, nth parameters 1)]
  val selected = entry ctxt "SignatureMixed"
  val (serial, reg_pos) = Micro_Rust_Names.navigation_target ctxt selected
  val (_, expected) = Position.make_entity_markup {def = false} serial
    Micro_Rust_Names.notationN ("SignatureMixed", reg_pos)
  val _ = require "generic function call preserves native selected notation navigation"
    (exists (fn (element, props) => element = Markup.entityN andalso at source "SignatureMixed" 0 props andalso
      forall (fn (key, value) => Properties.get props key = SOME value) expected) properties)
  val model_text = "urust_datatype [verbosity = 0] " ^ cartouche "struct NavigationBox<V> { payload: V }" ^ "\n" ^
    "urust [verbosity = 0] " ^ cartouche
      "impl NavigationBox<u8> {\n\<omega>\<open>name = \"navigation_byte_keep\"\<close>\nfn nav_keep<T>(self, value: T) -> T { value } }\nimpl NavigationBox<u16> {\n\<omega>\<open>name = \"navigation_half_keep\"\<close>\nfn nav_keep<T>(self, value: T) -> T { value } }"
  val (prepared, _) = capture (fn () => run thy "call-navigation-model" model_text)
  val model = Exn.release prepared |> Toplevel.theory_of
  val base = Proof_Context.init_global model
  val sources = Parser_Test_Calls.entries base "nav_keep"
  val byte_name = dest_Const (Proof_Context.read_const
    {proper = true, strict = false} base "navigation_byte_keep") |> fst
  val selected = the (find_first (fn entry =>
    Micro_Rust_Dispatch.backend_identity_constant base entry = SOME byte_name) sources)
  val (selected_serial, selected_pos) = Micro_Rust_Names.navigation_target base selected
  val (_, selected_props) = Position.make_entity_markup {def = false} selected_serial
    Micro_Rust_Names.notationN ("nav_keep", selected_pos)
  val text = "urust_fn [verbosity = 0] " ^ cartouche (prefix ^
    "fn NavigationUse(owner: NavigationBox<u8>, value: u16) -> u16 { owner.nav_keep::<u16>(value) }")
  val callbacks = saved_callbacks ()
  val reporter = !Private_Output.report_fn
  val (completed, navigation_events) = capture (fn () => run model "selected-call-navigation" text)
  val _ = ignore (Exn.release completed)
  val reports = markup navigation_events
  val references = reports |> map_filter (fn (element, props) =>
    if element = Markup.entityN andalso at text "nav_keep" 0 props andalso
      Properties.get props Markup.kindN = SOME Micro_Rust_Names.notationN
    then SOME props else NONE)
  val _ = require "overloaded generic method retains every original reference with selected source last"
    (length references = length sources andalso
      forall (fn (key, value) => Properties.get (List.last references) key = SOME value) selected_props)
  val _ = require "ordinary native backend entity and style reports remain available"
    (exists (fn (element, props) => element = Markup.entityN andalso at text "nav_keep" 0 props andalso
       Properties.get props Markup.kindN = SOME "constant" andalso
       Properties.get props Markup.nameN = SOME (dest_Const (Proof_Context.read_const
         {proper = true, strict = false} base "navigation_byte_keep") |> fst)) reports andalso
     exists (fn (element, props) => element = #1 Markup.keyword3 andalso at text "nav_keep" 0 props) reports)
  val _ = require "call navigation restores exact callbacks"
    (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
  val _ = writeln "U4 turbofish header/use final-sort labels and native selected overloaded navigation PASS"
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure D = Micro_Rust_Dispatch
  structure N = Micro_Rust_Names
  val thy = @{theory}
  val ctxt = @{context}
  val position = Position.of_properties [(Markup.offsetN, "101"), (Markup.end_offsetN, "109"),
    (Markup.fileN, "locale-occurrence"), ("extra", "caller argument provenance")]
  val caller = TVar (("locale_caller", 9017), @{sort type})
  fun verify context key rusts arguments =
    let
      val sources = Parser_Test_Calls.entries context key
      val serials = map #serial sources |> distinct (op =)
      val _ = require "locale transported entries retain the original source serial"
        (length sources = 3 andalso length serials = 1)
      val parameters = the (URust_Type_Mappings.generic_scheme_for_source context (hd serials))
      val _ = require "locale source-specific metadata retains ordered/unused generic names"
        (map #rust parameters = rusts)
      val _ = require "locale fixed type/value transports retain complete distinct ordinary backends"
        (length (distinct (op aconv) (map #hol_term sources)) = 3 andalso
         forall (is_none o #source_const) sources)
      val selected = the (find_first (fn ({hol_term, ...}: N.entry) =>
        Term.exists_subterm (fn Const (name, _) => name = @{const_name True} | _ => false) hol_term) sources)
      val instantiated = the (URust_Type_Mappings.instantiate_generic_scheme_for_source context
        (#serial selected) (#hol_term selected) arguments)
      val metadata: D.generic_arguments = {arguments = arguments, pos = position}
      val candidates = D.filtered_candidates_with_generics context [] N.NFunction key
        (fastype_of instantiated) (SOME metadata)
      val _ = require "native per-candidate instantiation selects the complete fixed type/value transport"
        (length candidates = 1 andalso #serial (#entry (hd candidates)) = #serial selected andalso
         Term.exists_subterm (fn Const (name, _) => name = @{const_name True} | _ => false)
           (#term (hd candidates)))
      val _ = require "locale final dispatch preserves high caller variable without capturing ambient/channel variables"
        (Library.member (op =) (Term.add_tvars (#term (hd candidates)) [])
          (("locale_caller", 9017), @{sort type}))
      val _ = ignore (failure "ambiguous expanded locale abbreviation metadata"
        "ambiguous generic scheme query for an expanded backend"
        (fn () => URust_Type_Mappings.generic_scheme context (#hol_term selected)))
    in map #hol parameters end
  val first = verify ctxt "LocaleCall" ["T"] [(caller, position)]
  val second = verify ctxt "LocaleOther" ["T", "U"] [(caller, position), (@{typ "16 word"}, position)]
  val _ = require "unused locale parameter retains native final bound sort" (map snd second = [@{sort type}, @{sort ord}])
  val base = Theory.end_theory thy
  fun fresh label parents = Theory.begin_theory (label, Position.none) parents
  val left = fresh "U4LocaleReplayLeft" [base] |> Theory.end_theory
  val right = fresh "U4LocaleReplayRight" [base] |> Theory.end_theory
  val replay = fresh "U4LocaleReplayJoin" [left, right] |> Proof_Context.init_global
  val _ = require "source-specific locale metadata and selected calls survive immutable replay/merge"
    (verify replay "LocaleCall" ["T"] [(caller, position)] = first andalso
     verify replay "LocaleOther" ["T", "U"] [(caller, position), (@{typ "16 word"}, position)] = second)
  val prefix = "/* " ^ Symbol.open_ ^ " ambiguity " ^ Symbol.close ^ " */ "
  val snapshot_before = snapshot ctxt
  val schemes_before = scheme_snapshot ctxt
  val _ = List.app (fn generic =>
    let
      val args = if generic then "::<u8>" else ""
      val text = "urust_fn [verbosity = 2] " ^ cartouche (prefix ^
        ("fn LocaleAmbiguous(value: (" ^ "\<tau>" ^ cartouche "nat" ^ ", u8)) -> (" ^
         "\<tau>" ^ cartouche "nat" ^ ", u8) { LocaleCall" ^ args ^ "(value) }"))
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run thy "locale-native-ambiguity" text)
      val diagnostic = case result of Exn.Res _ => error "native locale ambiguity unexpectedly accepted"
        | Exn.Exn exn => Runtime.exn_message exn
      val visible = XML.content_of (YXML.parse_body diagnostic)
      val _ = require "native ambiguity/selection remains authoritative for ordinary and generic calls"
        (String.isSubstring "Ambiguous uRust notation" visible andalso
         String.isSubstring "candidate backends" visible andalso String.isSubstring "literal 3" visible andalso
         String.isSubstring "literal 4" visible)
      val _ = require "native ambiguity retains exact head source range after escaped comment"
        (hd (map position_range (message_positions diagnostic)) = range_of text "LocaleCall" 0)
      val _ = require "failed locale call retains complete stream/report atomicity and exact restoration"
        (null (ordinary events) andalso null (declaration_reports events) andalso same_callbacks callbacks andalso
         PolyML.pointerEq (reporter, !Private_Output.report_fn) andalso snapshot ctxt = snapshot_before andalso
         scheme_snapshot ctxt = schemes_before)
    in () end) [false, true]
  val _ = writeln "U4 A15/A27 fixed locale transports/caller/unused sorts/source identity/replay/native ambiguity PASS"
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  structure D = Micro_Rust_Dispatch
  structure N = Micro_Rust_Names
  val position = Position.of_properties [(Markup.offsetN, "8"), (Markup.end_offsetN, "13"),
    (Markup.fileN, "generic-wrapper"), ("extra", "all properties retained")]
  val marker = D.mk_marker N.NFunction "SignatureIdentity" position (Free ("SignatureIdentity", dummyT))
  val arguments: D.generic_arguments = {arguments = [(@{typ "8 word"}, position)], pos = position}
  fun typed (Const (name, _) $ payload $ witness) = Const (name, dummyT --> dummyT --> @{typ nat}) $ payload $ witness
    | typed _ = error "typed marker audit shape"
  val ordinary = typed marker
  val wrapped = D.with_generic_arguments arguments ordinary
  val _ = require "typed-aware ordinary marker destructuring remains exactly identical with occurrence metadata"
    (D.dest_marker ordinary = D.dest_marker wrapped andalso
     D.dest_marker_untyped ordinary = D.dest_marker_untyped wrapped andalso
     #arguments (the (D.marker_generic_arguments wrapped)) = #arguments arguments)
  val payload = case ordinary of _ $ payload $ _ => payload | _ => error "ordinary payload audit shape"
  fun malformed metadata witness = HOLogic.mk_prod (payload, HOLogic.mk_prod (metadata, witness))
  val _ = List.app (fn (label, bad) => ignore (failure label "malformed urust_dispatch generic arguments"
    (fn () => D.dest_payload bad)))
    [("recognized wrapper wrong arity", malformed (Free (D.generic_position_name [position, position], dummyT)) HOLogic.unit),
     ("recognized wrapper bad witness", malformed (Free (D.generic_position_name [position, position], dummyT))
       (HOLogic.mk_prod (@{term True}, HOLogic.unit))),
     ("recognized wrapper invalid terminator", malformed (Free (D.generic_position_name [position, position], dummyT))
       (HOLogic.mk_prod (Logic.mk_type @{typ nat}, @{term True})))]
  val literal = D.mk_marker N.NLiteral "ValueLiteral" position (Free ("ValueLiteral", dummyT))
  val _ = ignore (failure "generic payload only applies to generated function markers"
    "malformed urust_dispatch generic arguments" (fn () => D.with_generic_arguments arguments literal))
  val _ = writeln "U4 typed-aware compatibility and recognized malformed typed-wrapper boundaries PASS"
in end
\<close>

subsection\<open> Receiver bounds and generic argument diagnostics \<close>

ML_val\<open>
local
structure Generic_Call_Owner_Test =
struct
  open Generic_Signature_Test
  structure D = Micro_Rust_Dispatch
  structure N = Micro_Rust_Names
  val original = @{theory}
  (* Preserve the complete original different-owner/different-bound fixture. *)
  val fixture = "urust_datatype [verbosity = 0] " ^ cartouche "struct BoundOwner<V> { payload: V }" ^ "\n" ^
    "urust [verbosity = 0] " ^ cartouche
      "impl BoundOwner<u8> {\n\<omega>\<open>name = \"bound_owner_byte_choose\"\<close>\nfn choose<T: Scale>(self, value: T) -> T { value }\n}\nimpl BoundOwner<u16> {\n\<omega>\<open>name = \"bound_owner_half_choose\"\<close>\nfn choose<T: Marker>(self, value: T) -> T { value }\n}"
  val (prepared, _) = capture (fn () => run original "adversarial-bound-model" fixture)
  val original_model = Exn.release prepared |> Toplevel.theory_of
  fun method backend options rust =
    "\<omega>" ^ cartouche ("name = \"" ^ backend ^ "\"" ^ options) ^ "\n" ^ rust ^ "\n"
  val extension = "urust [verbosity = 0] " ^ cartouche
    ("impl BoundOwner<u8> {\n" ^
      method "bound_owner_byte_share" ""
        "fn share<T: Scale, U: Marker>(self, value: (T, U)) -> (T, U) { value }" ^
      method "bound_owner_byte_unused" ""
        "fn unused<T: Scale>(self, value: u8) -> u8 { value }" ^
      method "bound_owner_byte_linked" (", state = " ^ cartouche "'t")
        "fn linked<T: Scale>(self, value: T) -> T { value }" ^
      method "bound_owner_byte_borrowed" (", state = " ^ cartouche "'t")
        "fn borrowed<T: Scale>(&mut self, value: T) -> T { value }" ^
      method "bound_owner_byte_order" ""
        "fn order<T: Scale, const N: usize>(self, value: (T, [u8; N])) -> (T, [u8; N]) { value }" ^
      method "bound_owner_byte_count" ""
        "fn count<T: Scale>(self, value: T) -> T { value }" ^
      "}\nimpl BoundOwner<u16> {\n" ^
      method "bound_owner_half_share" ""
        "fn share<T: Marker, U: Marker>(self, value: (T, U)) -> (T, U) { value }" ^
      method "bound_owner_half_unused" ""
        "fn unused<T: Marker>(self, value: u8) -> u8 { value }" ^
      method "bound_owner_half_linked" (", state = " ^ cartouche "'t")
        "fn linked<T: Marker>(self, value: T) -> T { value }" ^
      method "bound_owner_half_borrowed" (", state = " ^ cartouche "'t")
        "fn borrowed<T: Marker>(&mut self, value: T) -> T { value }" ^
      method "bound_owner_half_order" ""
        "fn order<const N: usize, T: Marker>(self, value: (T, [u8; N])) -> (T, [u8; N]) { value }" ^
      method "bound_owner_half_count" ""
        "fn count<T: Marker, U>(self, value: (T, U)) -> (T, U) { value }" ^ "}")
  val (extended, _) = capture (fn () => run original_model "bound-model-extension" extension)
  val model = Exn.release extended |> Toplevel.theory_of
  val ctxt = Proof_Context.init_global model
  fun sources name = N.lookups ctxt N.NFunction ("BoundOwner::" ^ name)
  fun source name backend =
    the_single (filter (fn entry =>
      Option.map Long_Name.base_name (D.backend_identity_constant ctxt entry) = SOME backend)
      (sources name))
  val _ = List.app (fn name =>
    require (name ^ ": both complete concrete owner sources retained") (length (sources name) = 2))
    ["choose", "share", "unused", "linked", "borrowed", "order", "count"]

end
in
local
  open Generic_Call_Owner_Test
  val state = snapshot ctxt
  val schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " bound " ^ Symbol.close ^ " */ "
  val no_backend = "no backend"
  val rows =
    [("different-owner-bound-dot", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { owner.choose::<bool>(value) }", "bool", 2),
     ("selected-owner-bound", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { BoundOwner::<u8>::choose::<bool>(owner, value) }", "bool", 2),
     ("shared-valid-invalid-bound", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: (bool, bool)) -> (bool, bool) { owner.share::<bool, bool>(value) }", "bool", 4),
     ("unused-owner-bound", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: u8) -> u8 { owner.unused::<bool>(value) }", "bool", 0),
     ("scoped-weak-owner-bound", "", "does not satisfy sort",
      "fn BoundProbe<T: Marker>(owner: BoundOwner<u8>, value: T) -> T { owner.choose::<T>(value) }", "T", 3),
     ("same-count-kind-owner-bound", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: (bool, [u8; 3])) -> (bool, [u8; 3]) { owner.order::<bool, 3>(value) }", "bool", 2),
     ("different-count-owner-bound", "", "does not satisfy sort",
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { owner.count::<bool>(value) }", "bool", 2),
     ("selected-kind-before-bound", "", "wrong type or const kind",
      "fn BoundProbe(owner: BoundOwner<u8>, value: (bool, [u8; 3])) -> (bool, [u8; 3]) { BoundOwner::<u8>::order::<3, bool>(owner, value) }", "3", 2),
     ("wrong-explicit-input-shape", "", no_backend,
      "fn BoundProbe(owner: BoundOwner<u8>, value: u8) -> u8 { owner.choose::<bool>(value) }", "choose", 0),
     ("wrong-explicit-return-shape", "", no_backend,
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> u8 { owner.choose::<bool>(value) }", "choose", 0),
     ("wrong-fixed-owner-shape", "", no_backend,
      "fn BoundProbe(owner: BoundOwner<bool>, value: bool) -> bool { owner.choose::<bool>(value) }", "choose", 0),
     ("wrong-shared-effect-shape", ", state = " ^ cartouche "nat", no_backend,
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { owner.linked::<bool>(value) }", "linked", 0),
     ("borrowed-owner-bound", ", state = " ^ cartouche "bool", "does not satisfy sort",
      "fn BoundProbe(owner: &mut BoundOwner<u8>, value: bool) -> bool { owner.borrowed::<bool>(value) }", "bool", 3)]
  fun check (label, options, expected, rust, token, occurrence) =
    let
      val text = "urust_fn [verbosity = 0" ^ options ^ "] " ^ cartouche (prefix ^ rust)
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run model label text)
      val raw = case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val visible = XML.content_of (YXML.parse_body raw)
      val _ = require (label ^ ": unexpected diagnostic " ^ visible) (String.isSubstring expected visible)
      val _ = require (label ^ ": exact generic argument or native method range")
        (map position_range (message_positions raw) =
          [range_of text token occurrence, range_of text "urust_fn" 0])
      val _ = require (label ^ ": complete output/report suppression")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": exact callback restoration")
        (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val current = Proof_Context.init_global model
      val _ = require (label ^ ": immutable namespace/registration/scheme/scope snapshot")
        (snapshot current = state andalso scheme_snapshot current = schemes)
      val (recovered, _) = capture (fn () => run model (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche "fn BoundRecovery(value: u8) -> u8 { value }"))
      val recovery = Exn.release recovered |> Toplevel.context_of
      val _ = require (label ^ ": ordinary recovery")
        (is_some (Parser_Test_Calls.lookup recovery "BoundRecovery"))
      val _ = require_scope_closed label recovery
    in () end
  val _ = List.app check rows
  val ambiguous_rust = "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { BoundOwner::choose::<bool>(owner, value) }"
  val ambiguous_text = "urust_fn [verbosity = 0] " ^ cartouche (prefix ^ ambiguous_rust)
  val (ambiguous_result, ambiguous_events) = capture (fn () => run model "unselected-owner-ambiguity" ambiguous_text)
  val ambiguous_raw = case ambiguous_result of Exn.Res _ => error "unselected owner ambiguity accepted"
    | Exn.Exn exn => Runtime.exn_message exn
  val declared_owners = N.associated_functions ctxt "BoundOwner::choose"
    |> sort (int_ord o apply2 #identity)
  val _ = require "unselected overloaded associated owner retains native ambiguity and all declaration positions"
    (String.isSubstring "multiple applicable items in scope" ambiguous_raw andalso
     map position_range (message_positions ambiguous_raw) =
      range_of ambiguous_text "choose" 0 ::
        map (position_range o #pos) declared_owners @ [range_of ambiguous_text "urust_fn" 0] andalso
     null (ordinary ambiguous_events) andalso null (declaration_reports ambiguous_events))
  fun twin label options owner parameter_type result_type call backend =
    let
      val clause = "(owner: " ^ owner ^ ", value: " ^ parameter_type ^ ") -> " ^ result_type
      val actual = "urust_fn [verbosity = 0" ^ options ^ "] bound_actual " ^ cartouche
        ("fn BoundActual" ^ clause ^ " { " ^ call ^ " }")
      val direct = "urust_fn [verbosity = 0" ^ options ^ "] bound_twin " ^ cartouche
        ("fn BoundTwin" ^ clause ^ " { \<epsilon>" ^ cartouche backend ^ "(owner, value) }")
      val proof = "lemma bound_refl: " ^ cartouche "bound_actual = bound_twin" ^
        " unfolding bound_actual_def bound_twin_def by (rule refl)"
      val (result, _) = capture (fn () => run model label (actual ^ "\n" ^ direct ^ "\n" ^ proof))
    in ignore (Exn.release result) end
  val nat_type = "\<tau>" ^ cartouche "nat"
  val _ = twin "weak-other-owner-positive" "" "BoundOwner<u16>" "bool" "bool"
    "owner.choose::<bool>(value)" "bound_owner_half_choose"
  val _ = twin "strong-selected-owner-positive" "" "BoundOwner<u8>" nat_type nat_type
    ("BoundOwner::<u8>::choose::<" ^ nat_type ^ ">(owner, value)") "bound_owner_byte_choose"
  val _ = twin "shared-weaker-owner-positive" "" "BoundOwner<u16>" "(bool, bool)" "(bool, bool)"
    "owner.share::<bool, bool>(value)" "bound_owner_half_share"
  val _ = twin "shared-strong-owner-positive" "" "BoundOwner<u8>"
    ("(" ^ nat_type ^ ", " ^ nat_type ^ ")") ("(" ^ nat_type ^ ", " ^ nat_type ^ ")")
    ("owner.share::<" ^ nat_type ^ ", " ^ nat_type ^ ">(value)") "bound_owner_byte_share"
  val _ = twin "reversed-kind-weaker-owner-positive" "" "BoundOwner<u16>"
    "(bool, [u8; 3])" "(bool, [u8; 3])" "owner.order::<3, bool>(value)" "bound_owner_half_order"
  val _ = twin "ordered-strong-owner-positive" "" "BoundOwner<u8>"
    ("(" ^ nat_type ^ ", [u8; 3])") ("(" ^ nat_type ^ ", [u8; 3])")
    ("owner.order::<" ^ nat_type ^ ", 3>(value)") "bound_owner_byte_order"
  val _ = twin "different-count-weaker-owner-positive" "" "BoundOwner<u16>"
    "(bool, u8)" "(bool, u8)" "owner.count::<bool, u8>(value)" "bound_owner_half_count"
  val _ = twin "unused-strong-owner-positive" "" "BoundOwner<u8>" "u8" "u8"
    ("owner.unused::<" ^ nat_type ^ ">(value)") "bound_owner_byte_unused"
  val _ = twin "linked-effect-positive" (", state = " ^ cartouche "nat")
    "BoundOwner<u8>" nat_type nat_type ("owner.linked::<" ^ nat_type ^ ">(value)")
    "bound_owner_byte_linked"
  val _ = twin "borrowed-linked-effect-positive" (", state = " ^ cartouche "nat")
    "&mut BoundOwner<u8>" nat_type nat_type ("owner.borrowed::<" ^ nat_type ^ ">(value)")
    "bound_owner_byte_borrowed"
  val _ = writeln "U4 A29 original/selected owner bounds, actual structure/kind/count/receiver/channel atomic negatives and kernel positives PASS"
in end

local
  open Generic_Call_Owner_Test
  val before_state = snapshot ctxt
  val before_schemes = scheme_snapshot ctxt
  val first_pos = Position.of_properties [(Markup.offsetN, "31"), (Markup.end_offsetN, "37"),
    (Markup.fileN, "shared-witness"), ("caller", "first")]
  val second_pos = Position.of_properties [(Markup.offsetN, "41"), (Markup.end_offsetN, "47"),
    (Markup.fileN, "shared-witness"), ("caller", "second")]
  val list_pos = Position.of_properties [(Markup.offsetN, "21"), (Markup.end_offsetN, "51"),
    (Markup.fileN, "shared-witness")]
  val owner8 = hd (binder_types (fastype_of (#hol_term (source "choose" "bound_owner_byte_choose"))))
  val owner16 = hd (binder_types (fastype_of (#hol_term (source "choose" "bound_owner_half_choose"))))
  fun tuple left right = HOLogic.mk_prodT (left, HOLogic.mk_prodT (right, @{typ tnil}))
  fun body state value = Type (@{type_name function_body},
    [state, value, @{typ nat}, @{typ "unit prompt"}, @{typ "unit prompt_output"}])
  fun occurrence receiver argument result state = receiver --> argument --> body state result
  fun metadata types: D.generic_arguments =
    {arguments = types ~~ take (length types) [first_pos, second_pos], pos = list_pos}
  fun candidates name types T = D.filtered_candidates_with_generics ctxt [] N.NFunction
    ("BoundOwner::" ^ name) T (SOME (metadata types))
  fun rejects label name types T =
    let
      val raw = failure label "does not satisfy sort" (fn () => candidates name types T)
      val _ = require (label ^ ": original first supplied argument position")
        (map position_range (message_positions raw) = [position_range first_pos])
      val _ = require (label ^ ": diagnostic native temporary indexes do not escape")
        (not (String.isSubstring ".9018" raw) andalso
         not (String.isSubstring ".9019" raw))
    in () end
  fun no_match label name types T =
    require (label ^ ": exact actual structure must retain native no-match")
      (null (candidates name types T))
  val _ = List.app (fn index =>
    let
      (* Deliberately use the diagnostic stem and both low/high indexes. *)
      val weak = TVar ((Name.internal "urust_generic_diagnostic", index), @{sort type})
      val shared = tuple weak weak
      val nested = tuple weak (HOLogic.listT weak)
      val _ = rejects ("repeated-weak-" ^ string_of_int index) "share" [weak, weak]
        (occurrence owner8 shared shared @{typ bool})
      val _ = rejects ("nested-weak-" ^ string_of_int index) "share" [weak, HOLogic.listT weak]
        (occurrence owner8 nested nested @{typ bool})
      val _ = rejects ("linked-weak-" ^ string_of_int index) "linked" [weak]
        (occurrence owner8 weak weak weak)
      val receiver = Term.typ_subst_atomic
        [(@{typ "'address"}, @{typ nat}), (@{typ "'global"}, weak), (@{typ "'target"}, owner8)]
        @{typ "('address, 'global, 'target) Global_Store.ref"}
      val _ = rejects ("borrowed-linked-weak-" ^ string_of_int index) "borrowed" [weak]
        (occurrence receiver weak weak weak)
      val strong = TVar ((Name.internal "urust_generic_diagnostic", index), @{sort trait_scale})
      val strong_pair = tuple strong strong
      val [selected] = candidates "share" [strong, strong]
        (occurrence owner8 strong_pair strong_pair @{typ bool})
      val expected_serial = #serial (source "share" "bound_owner_byte_share")
      val _ = require "repeated strong caller identity and selected source survive final native dispatch"
        (#serial (#entry selected) = expected_serial andalso
         Term.add_tvars (#term selected) [] = [((Name.internal "urust_generic_diagnostic", index),
           @{sort trait_scale})])
      val strong_receiver = Term.typ_subst_atomic
        [(@{typ "'address"}, @{typ nat}), (@{typ "'global"}, strong), (@{typ "'target"}, owner8)]
        @{typ "('address, 'global, 'target) Global_Store.ref"}
      val expected = occurrence strong_receiver strong strong strong
      val [borrowed] = candidates "borrowed" [strong] expected
      val _ = require "generic/receiver/global/effect sharing survives final native dispatch without temporary variables"
        (fastype_of (#term borrowed) = expected andalso
         #serial (#entry borrowed) = #serial (source "borrowed" "bound_owner_byte_borrowed") andalso
         Term.add_tvars (#term borrowed) [] = [((Name.internal "urust_generic_diagnostic", index),
           @{sort trait_scale})])
    in () end) [0, 2, 700, 9017]
  val weak = TFree ("'rigid_weak", @{sort type})
  val repeated = tuple weak weak
  val nested = tuple weak (HOLogic.listT weak)
  val _ = rejects "rigid-shared-valid-invalid" "share" [weak, weak]
    (occurrence owner8 repeated repeated @{typ bool})
  val _ = rejects "rigid-nested-sharing" "share" [weak, HOLogic.listT weak]
    (occurrence owner8 nested nested @{typ bool})
  val _ = rejects "concrete-shared-valid-invalid" "share" [@{typ bool}, @{typ bool}]
    (occurrence owner8 (tuple @{typ bool} @{typ bool}) (tuple @{typ bool} @{typ bool}) @{typ bool})
  val _ = rejects "unused-wrong-bound-keeps-witness" "unused" [@{typ bool}]
    (occurrence owner8 @{typ "8 word"} @{typ "8 word"} @{typ bool})
  val _ = no_match "rigid-repeated-input-mismatch" "share" [weak, weak]
    (occurrence owner8 (tuple weak @{typ nat}) repeated @{typ bool})
  val _ = no_match "rigid-repeated-output-mismatch" "share" [weak, weak]
    (occurrence owner8 repeated (tuple weak @{typ nat}) @{typ bool})
  val _ = no_match "rigid-nested-input-mismatch" "share" [weak, HOLogic.listT weak]
    (occurrence owner8 (tuple weak (HOLogic.listT @{typ nat})) nested @{typ bool})
  val _ = no_match "concrete-shared-structure-mismatch" "share" [@{typ bool}, @{typ bool}]
    (occurrence owner8 (tuple @{typ bool} @{typ "8 word"}) (tuple @{typ bool} @{typ bool}) @{typ bool})
  val _ = no_match "linked-effect-structure-mismatch" "linked" [@{typ bool}]
    (occurrence owner8 @{typ bool} @{typ bool} @{typ nat})
  val wrong_receiver = Term.typ_subst_atomic
    [(@{typ "'address"}, @{typ nat}), (@{typ "'global"}, weak), (@{typ "'target"}, owner8)]
    @{typ "('address, 'global, 'target) Global_Store.ref"}
  val _ = no_match "borrowed-return-structure-mismatch" "borrowed" [weak]
    (occurrence wrong_receiver weak @{typ nat} weak)
  val [half] = candidates "share" [@{typ bool}, @{typ bool}]
    (occurrence owner16 (tuple @{typ bool} @{typ bool}) (tuple @{typ bool} @{typ bool}) @{typ bool})
  val _ = require "unrelated strong bound does not reject correctly selected weaker owner"
    (#serial (#entry half) = #serial (source "share" "bound_owner_half_share"))
  val _ = require "diagnostic preflight/final calls preserve all original contexts, schemes and ordinary registrations"
    (snapshot ctxt = before_state andalso scheme_snapshot ctxt = before_schemes)
  val _ = require_scope_closed "A29 diagnostic scopes" ctxt
  val _ = writeln "U4 A29 repeated/nested low-high variables, rigid/concrete sharing, receiver/channels, unused witnesses and native shape controls PASS"
in end

local
  open Generic_Call_Owner_Test
  val plain_text = "urust [verbosity = 0] " ^ cartouche
    ("impl BoundOwner<u8> {\n" ^
      method "bound_owner_byte_plain" "" "fn plain(self, value: u8) -> u8 { value }" ^
      "}\nimpl BoundOwner<u16> {\n" ^
      method "bound_owner_half_plain" "" "fn plain<T>(self, value: T) -> T { value }" ^ "}")
  val (prepared, _) = capture (fn () => run model "owner-monomorphic-model" plain_text)
  val model = Exn.release prepared |> Toplevel.theory_of
  val ctxt = Proof_Context.init_global model
  val state = snapshot ctxt
  val schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " bound " ^ Symbol.close ^ " */ "
  val rows =
    [("owner-count-dot", "wrong number of generic arguments",
      "fn BoundProbe(owner: BoundOwner<u8>, value: bool) -> bool { owner.count::<bool, u8>(value) }", "::<bool, u8>", 0),
     ("owner-kind-dot", "wrong type or const kind",
      "fn BoundProbe(owner: BoundOwner<u8>, value: (bool, [u8; 3])) -> (bool, [u8; 3]) { owner.order::<3, bool>(value) }", "3", 2),
     ("reverse-owner-count-dot", "wrong number of generic arguments",
      "fn BoundProbe(owner: BoundOwner<u16>, value: (bool, u8)) -> (bool, u8) { owner.count::<bool>(value) }", "::<bool>", 0),
     ("reverse-owner-kind-dot", "wrong type or const kind",
      "fn BoundProbe(owner: BoundOwner<u16>, value: (bool, [u8; 3])) -> (bool, [u8; 3]) { owner.order::<bool, 3>(value) }", "bool", 2),
     ("monomorphic-owner-dot", "generic arguments are not supported on generated Rust function paths",
      "fn BoundProbe(owner: BoundOwner<u8>, value: u8) -> u8 { owner.plain::<u8>(value) }", "::<u8>", 0),
     ("count-kind-compatible-shape-mismatch", "no backend matches the use-site type",
      "fn BoundProbe(owner: BoundOwner<u8>, value: u8) -> u8 { owner.count::<bool>(value) }", "count", 0)]
  val _ = List.app (fn (label, expected, rust, token, occurrence) =>
    let
      val text = "urust_fn [verbosity = 0] " ^ cartouche (prefix ^ rust)
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run model label text)
      val raw = case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val visible = XML.content_of (YXML.parse_body raw)
      val _ = require (label ^ ": unexpected diagnostic " ^ visible) (String.isSubstring expected visible)
      val _ = require (label ^ ": exact responsible list/leaf or native shape range")
        (map position_range (message_positions raw) =
          [range_of text token occurrence, range_of text "urust_fn" 0])
      val _ = require (label ^ ": complete ordinary/urgent/report suppression")
        (null (ordinary events) andalso null (chunks "urgent" events) andalso null (declaration_reports events))
      val _ = require (label ^ ": original namespace/scheme/scope snapshots and callbacks")
        (snapshot ctxt = state andalso scheme_snapshot ctxt = schemes andalso
         same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val (recovered, _) = capture (fn () => run model (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche "fn OwnerRecovery(value: u8) -> u8 { value }"))
      val recovery = Exn.release recovered |> Toplevel.context_of
      val _ = require (label ^ ": ordinary recovery")
        (is_some (Parser_Test_Calls.lookup recovery "OwnerRecovery"))
      val _ = require_scope_closed label recovery
    in () end) rows
  fun twin label owner parameter_type result_type call backend =
    let
      val clause = "(owner: " ^ owner ^ ", value: " ^ parameter_type ^ ") -> " ^ result_type
      val actual = "urust_fn [verbosity = 0] owner_actual " ^ cartouche
        ("fn OwnerActual" ^ clause ^ " { " ^ call ^ " }")
      val direct = "urust_fn [verbosity = 0] owner_twin " ^ cartouche
        ("fn OwnerTwin" ^ clause ^ " { \<epsilon>" ^ cartouche backend ^ "(owner, value) }")
      val proof = "lemma owner_refl: " ^ cartouche "owner_actual = owner_twin" ^
        " unfolding owner_actual_def owner_twin_def by (rule refl)"
      val (result, _) = capture (fn () => run model label (actual ^ "\n" ^ direct ^ "\n" ^ proof))
    in ignore (Exn.release result) end
  val _ = twin "alternative-generic-owner" "BoundOwner<u16>" "bool" "bool"
    "owner.plain::<bool>(value)" "bound_owner_half_plain"
  val _ = twin "ordinary-monomorphic-owner" "BoundOwner<u8>" "u8" "u8"
    "owner.plain(value)" "bound_owner_byte_plain"
  val nat_type = "\<tau>" ^ cartouche "nat"
  val size_type = "\<tau>" ^ cartouche "3"
  val _ = twin "neutral-ordered-owner" "BoundOwner<u8>" ("(" ^ nat_type ^ ", [u8; 3])")
    ("(" ^ nat_type ^ ", [u8; 3])")
    ("owner.order::<" ^ nat_type ^ ", " ^ size_type ^ ">(value)") "bound_owner_byte_order"
  val dot_sources = N.lookups ctxt N.NFunction "plain"
  val monomorphic = the_single (filter (fn entry =>
    Option.map Long_Name.base_name (D.backend_identity_constant ctxt entry) = SOME "bound_owner_byte_plain")
    dot_sources)
  val _ = require "monomorphic source retains NONE rather than a fabricated empty generic scheme"
    (is_none (URust_Type_Mappings.generic_scheme_for_source ctxt (#serial monomorphic)))
  val empty_base = Named_Target.theory_init model
  val explicit_empty = URust_Type_Mappings.register_generic_scheme
    {identity = #hol_term monomorphic, backend = #hol_term monomorphic,
     sources = [#serial monomorphic], parameters = [], pos = #reg_pos monomorphic} empty_base
  val _ = require "native empty registration is a no-op and never fabricates SOME [] metadata"
    (PolyML.pointerEq (explicit_empty, empty_base) andalso
     is_none (URust_Type_Mappings.generic_scheme_for_source explicit_empty (#serial monomorphic)) andalso
     is_none (URust_Type_Mappings.generic_scheme_for_source ctxt (#serial monomorphic)))
  val _ = writeln "U4 A30 original/reverse count/kind, monomorphic NONE/empty, shape, alternative/neutral/ordinary controls PASS"
in end

local
  open Generic_Call_Owner_Test
  val original_state = snapshot ctxt
  val original_schemes = scheme_snapshot ctxt
  val pos = Position.of_properties [(Markup.lineN, "7"), (Markup.offsetN, "21"),
    (Markup.end_offsetN, "53"), (Markup.fileN, "source-kind-carrier"),
    ("custom", "all properties : , ;")]
  val first = Position.of_properties [(Markup.offsetN, "31"), (Markup.end_offsetN, "35"),
    (Markup.fileN, "source-kind-carrier")]
  val second = Position.of_properties [(Markup.offsetN, "42"), (Markup.end_offsetN, "48"),
    (Markup.fileN, "source-kind-carrier")]
  val entries = N.lookups ctxt N.NFunction "count"
  fun named backend = the_single (filter (fn entry =>
    Option.map Long_Name.base_name (D.backend_identity_constant ctxt entry) = SOME backend) entries)
  val byte = named "bound_owner_byte_count"
  val half = named "bound_owner_half_count"
  val metadata: D.generic_arguments = {arguments = [(@{typ bool}, first), (@{typ "8 word"}, second)], pos = pos}
  val selection: D.generic_source_selection = {sources = [#serial half], kinds = [SOME true, SOME true]}
  val marker = D.mk_marker N.NFunction "count" pos (Free ("count", dummyT))
  val ordinary = D.with_generic_arguments metadata marker
  val wrapped = D.with_generic_source_arguments selection metadata marker
  val _ = require "ordinary generic wrapper values and API remain unchanged"
    (is_none (D.marker_generic_source_selection marker) andalso
     is_none (D.marker_generic_source_selection ordinary) andalso
     D.marker_generic_arguments ordinary = SOME metadata)
  val _ = require "optional scalar carrier preserves basic arguments, arbitrary positions and ordinary marker/filter values"
    (D.marker_generic_arguments wrapped = SOME metadata andalso
     D.marker_generic_source_selection wrapped = SOME selection andalso
     D.dest_marker_untyped marker = D.dest_marker_untyped wrapped)
  val genuine = [N.Only_Sources [#serial half], N.Exclude_Method_Only]
  val _ = require "syntactic scalar metadata and all genuine filters compose exactly in both orders"
    (D.restrict_backends genuine wrapped aconv
      D.with_generic_source_arguments selection metadata (D.restrict_backends genuine marker))
  val _ = require "syntactic selection never enters the genuine ordinary filter channel"
    (case D.dest_marker_untyped wrapped of SOME ((_, _, _, filters), _) => null filters | _ => false)
  val _ = List.app (fn kinds =>
    let
      val value: D.generic_source_selection = {sources = [#serial half, #serial byte], kinds = kinds}
      val term = D.with_generic_source_arguments value metadata marker
    in require "native scalar carrier keeps type/const/HOL-neutral tags and source serial order"
      (D.marker_generic_source_selection term = SOME value andalso
       D.marker_generic_arguments term = SOME metadata) end)
    [[SOME true, SOME false], [SOME false, SOME true], [NONE, NONE]]
  fun body state result = Type (@{type_name function_body},
    [state, result, @{typ nat}, @{typ "unit prompt"}, @{typ "unit prompt_output"}])
  val owner8 = hd (binder_types (fastype_of (#hol_term byte)))
  val expected = owner8 --> @{typ bool} --> body @{typ bool} @{typ bool}
  fun selected filters = D.filtered_candidates_with_source_generics ctxt filters N.NFunction "count"
    expected (SOME metadata) (SOME selection)
  val wrong_count = failure "source-aware responsible owner count" "wrong number of generic arguments"
    (fn () => selected [])
  val _ = require "source-aware count diagnostic retains the complete generic-list position"
    (map position_range (message_positions wrong_count) = [position_range pos])
  val _ = require "real source exclusion never recovers or diagnoses the excluded responsible owner"
    (null (selected [N.Only_Sources [#serial half]]))
  val _ = require "real empty source selection and method exclusion are never weakened"
    (null (selected [N.Only_Sources []]) andalso null (selected [N.Exclude_Method_Only]))
  val _ = require "basic generic candidate API retains its preexisting behavior without optional source data"
    (null (D.filtered_candidates_with_generics ctxt [] N.NFunction "count" expected (SOME metadata)))
  fun tuple left right = HOLogic.mk_prodT (left, HOLogic.mk_prodT (right, @{typ tnil}))
  val shared_entries = N.lookups ctxt N.NFunction "share"
  val byte_shared = the_single (filter (fn entry =>
    Option.map Long_Name.base_name (D.backend_identity_constant ctxt entry) = SOME "bound_owner_byte_share")
    shared_entries)
  val _ = List.app (fn index =>
    let
      val caller = TVar ((Name.internal "urust_generic_diagnostic", index), @{sort trait_scale})
      val arguments: D.generic_arguments = {arguments = [(caller, first), (caller, second)], pos = pos}
      val source_info: D.generic_source_selection =
        {sources = map #serial shared_entries, kinds = [SOME true, SOME true]}
      val pair = tuple caller caller
      val occurrence = owner8 --> pair --> body @{typ bool} pair
      val [candidate] = D.filtered_candidates_with_source_generics ctxt [] N.NFunction "share"
        occurrence (SOME arguments) (SOME source_info)
      val _ = require "source-aware actual dispatch retains exact repeated low/high caller identity and native selected serial"
        (#serial (#entry candidate) = #serial byte_shared andalso
         Term.add_tvars (#term candidate) [] =
          [((Name.internal "urust_generic_diagnostic", index), @{sort trait_scale})])
      val empty: D.generic_source_selection = {sources = [], kinds = [SOME true, SOME true]}
      val _ = require "an empty syntactic actual selection never reinstalls a backend"
        (null (D.filtered_candidates_with_source_generics ctxt [] N.NFunction "share"
          occurrence (SOME arguments) (SOME empty)))
    in () end) [0, 2, 700, 9017]
  val _ = ignore (failure "source metadata duplicate arguments" "malformed urust_dispatch generic arguments"
    (fn () => D.with_generic_source_arguments selection metadata ordinary))
  val _ = ignore (failure "source metadata kind count" "malformed urust_dispatch generic arguments"
    (fn () => D.with_generic_source_arguments {sources = [#serial half], kinds = [NONE]} metadata marker))
  val payload = case ordinary of _ $ payload $ _ => payload | _ => error "ordinary generic payload shape"
  val (base, positions, types) =
    case payload of _ $ base $ (_ $ positions $ types) => (base, positions, types)
      | _ => error "ordinary generic nested payload shape"
  fun malformed flag rest = HOLogic.mk_prod (base, HOLogic.mk_prod (positions, HOLogic.mk_prod (flag, rest)))
  fun source_flag text = Free (D.generic_source_prefix ^
    Micro_Rust_Semantic_Navigation.escape_payload_name text, dummyT)
  val valid_flag = Free (D.generic_source_name selection, dummyT)
  val _ = List.app (fn (label, bad) =>
    ignore (failure label "malformed urust_dispatch generic arguments" (fn () => D.dest_payload bad)))
    [("invalid scalar source serial", malformed (source_flag ("sources bad" ^ D.payload_sep ^ "tt")) types),
     ("invalid scalar kind tag", malformed (source_flag ("empty_sources" ^ D.payload_sep ^ "tx")) types),
     ("invalid scalar kind cardinality", malformed (source_flag ("empty_sources" ^ D.payload_sep ^ "t")) types),
     ("duplicate scalar source metadata", malformed valid_flag (HOLogic.mk_prod (valid_flag, types))),
     ("scalar source sentinel outside wrapper", HOLogic.mk_prod (valid_flag, HOLogic.unit))]
  val _ = require "all scalar transport/filter/diagnostic probes preserve original registries, schemes and scope"
    (snapshot ctxt = original_state andalso scheme_snapshot ctxt = original_schemes)
  val _ = require_scope_closed "source metadata controls" ctxt
  val _ = writeln "U4 A30 scalar metadata/ordinary APIs/genuine filters/malformed boundaries/caller preservation PASS"
in end
end
\<close>

section\<open> Erased source slots and sparse generic schemes \<close>

ML_val\<open>
local
  open Parser_Trait_Test
  structure M = URust_Type_Mappings
  val ctxt = \<^context>
  val thy = \<^theory>
  val previous = neighboring_snapshot [] ctxt
  fun parsed current label text = URust_Parser.parse_type_source current (source label text)
  fun resolved current label text = M.resolve_type_identity current (parsed current label text)
  fun identity current text =
    resolved current "erasure-identity" text |> #2 |> the |> M.source_identity_name
  fun slots name =
    let val entry = the_single (Parser_Test_Calls.entries ctxt name)
    in (entry, the (M.generic_source_scheme_for_source ctxt (#serial entry))) end
  val (erased, erased_slots) = slots "ErasureIdentity"
  val (mixed, mixed_slots) = slots "ErasureMixedIdentity"
  val (_, unused_slots) = slots "SignatureUnused"
  val _ = require "full source order/kinds persist without fabricated witnesses"
    (map #rust erased_slots = ["T", "N"] andalso
     map #kind erased_slots = [URust_AST.Type_Parameter, URust_AST.Const_Parameter] andalso
     forall (is_none o #hol) erased_slots andalso
     map #source_used erased_slots = [SOME true, SOME true] andalso
     is_none (M.generic_scheme_for_source ctxt (#serial erased)))
  val _ = require "mixed source indexes preserve only the payload witness"
    (map #rust mixed_slots = ["Tag", "P", "N"] andalso
     map (is_some o #hol) mixed_slots = [false, true, false] andalso
     map #source_used mixed_slots = [SOME true, SOME true, SOME true])
  val _ = require "entirely unused legacy parameters keep their original witness view"
    (forall (is_some o #hol) unused_slots andalso
     forall (fn parameter => #source_used parameter = SOME false) unused_slots)
  val legacy = the_single (Parser_Test_Calls.entries ctxt "SignatureIdentity")
  val legacy_parameters: M.generic_scheme_parameter list =
    the (M.generic_scheme_for_source ctxt (#serial legacy))
  val legacy_lthy = Named_Target.theory_init thy
  val replayed_legacy = M.register_generic_scheme
    {identity = #hol_term legacy, backend = #hol_term legacy, sources = [#serial legacy],
     parameters = legacy_parameters, pos = #reg_pos legacy} legacy_lthy
  val _ = require "direct old exact-record registration/lookup preserves witnessed type and known source use"
    (M.generic_scheme_for_source replayed_legacy (#serial legacy) = SOME legacy_parameters andalso
     map #source_used (the (M.generic_source_scheme_for_source replayed_legacy (#serial legacy))) =
       [SOME true])
  val legacy_unused = the_single (Parser_Test_Calls.entries ctxt "SignatureUnused")
  val legacy_unused_parameters: M.generic_scheme_parameter list =
    the (M.generic_scheme_for_source ctxt (#serial legacy_unused))
  val replayed_unused = M.register_generic_scheme
    {identity = #hol_term legacy_unused, backend = #hol_term legacy_unused,
     sources = [#serial legacy_unused], parameters = legacy_unused_parameters,
     pos = #reg_pos legacy_unused} legacy_lthy
  val _ = require "old bound/unused registration retains authoritative source bounds and usage"
    (M.generic_source_scheme_for_source replayed_unused (#serial legacy_unused) = SOME unused_slots)
  val role_bound_declarations =
    "urust_type [implicit = " ^ cartouche " global = 'g " ^ "] \"ErasureWeakRole\" = " ^
      cartouche " 'g " ^ "\n" ^
    "urust_type [implicit = " ^ cartouche " global = 'g " ^ "] \"ErasureStrongRole\" = " ^
      cartouche " 'g::trait_scale "
  val role_bound_ctxt = context (run thy "erasure-role-bound-fixture" role_bound_declarations)
  val (_, bound_slots) = slots "ErasureBound"
  fun role_argument label text = URust_AST.Rust_Type_Argument (parsed role_bound_ctxt label text)
  val weak_argument = role_argument "erasure-weak-role-bound" "ErasureWeakRole"
  val weak_observed = capture (fn () => Reports.capture (fn () =>
    M.resolve_source_arguments role_bound_ctxt bound_slots [weak_argument]))
  val weak_message = error_message "erasure-weak-role-bound" "function argument" (#result weak_observed)
  val weak_positions = Generic_Syntax_Test.message_positions weak_message
  val _ = require "erased bounds do not strengthen discarded implicit roles and preserve leaf positions"
    (not (null weak_positions) andalso
     Generic_Syntax_Test.position_range (hd weak_positions) = (1, 16) andalso
     Position.file_of (hd weak_positions) = SOME "erasure-weak-role-bound" andalso
     null (#markup weak_observed) andalso #reports weak_observed = "" andalso
     M.entry_backend_parameter_sorts (the (M.lookup role_bound_ctxt "ErasureWeakRole")) =
       [\<^sort>\<open>type\<close>])
  val (strong_result, _) = Reports.capture (fn () => M.resolve_source_arguments role_bound_ctxt
    bound_slots [role_argument "erasure-strong-role-bound" "ErasureStrongRole"])
  val (strong_enclosing, _) = Reports.capture (fn () =>
    M.resolve_declaration_roles role_bound_ctxt [] []
      [parsed role_bound_ctxt "erasure-strong-role-enclosing" "ErasureBox<ErasureStrongRole,0>"])
  val _ = require "existing implicit-role bound evidence passes without a witness or semantic allocation"
    (forall (is_none o #1) (#arguments strong_result) andalso
     #types strong_enclosing = [\<^typ>\<open>nat\<close>] andalso
     null (#backend_parameters strong_enclosing))
  val _ = require "source-only aliases count their parameters as used"
    (M.entry_erased_parameters (the (M.lookup ctxt "ErasureAlias")) = [0, 1] andalso
     M.entry_erased_parameters (the (M.lookup ctxt "ErasureArrayAlias")) = [0])
  val _ = List.app (fn argument =>
    require ("supported erased source shape " ^ argument)
      (#1 (resolved ctxt "erasure-positive" ("ErasureBox<" ^ argument ^ ",0>")) = \<^typ>\<open>nat\<close>))
    ["Foreign", "foreign::Tag<u8,0>", "(Foreign)", "outer::Tag<inner::Tag<0x_10>>", "u8"]
  val _ = require "normalized numeric identity retains value rather than spelling"
    (identity ctxt "ErasureBox<Foreign,16>" = identity ctxt "ErasureBox<Foreign,0x_10>" andalso
     identity ctxt "ErasureBox<Foreign,0>" <> identity ctxt "ErasureBox<Foreign,1>" andalso
     identity ctxt "ErasureBox<Alpha,0>" <> identity ctxt "ErasureBox<Beta,0>")
  val _ = require "generic retained array aliases substitute both element and const length identity"
    (identity ctxt "ErasureArrayAlias<Alpha,u8,4>" =
       identity ctxt "ErasurePayload<Alpha,[u8;4]>" andalso
     identity ctxt "ErasureArrayAlias<Alpha,u16,4>" <>
       identity ctxt "ErasureArrayAlias<Alpha,u8,4>" andalso
     identity ctxt "ErasureArrayAlias<Alpha,u8,5>" <>
       identity ctxt "ErasureArrayAlias<Alpha,u8,4>")
  val escaped = "ErasurePayload<Alpha,\<tau>" ^ cartouche "'source_unique" ^ ">"
  val _ = require "authored HOL leaves are finalized before source identity capture"
    (identity ctxt escaped = identity ctxt escaped andalso
     not (String.isSubstring "_urust_inference_" (identity ctxt escaped)))
  val locale_owners = Micro_Rust_Names.associated_source_functions ctxt "ErasurePayload::locale_identity"
  val _ = require "retained HOL source leaves morph independently through repeated native interpretations"
    (length locale_owners = 2 andalso forall (fn owner =>
      #source_identity owner = SOME (identity ctxt
        ("ErasurePayload<Alpha,\<tau>" ^ cartouche
          (if #self_type owner = \<^typ>\<open>nat option\<close> then "nat" else "bool") ^ ">"))) locale_owners)
  val _ = require "sparse instantiation accepts exactly its actual witness mask"
    (is_some (M.instantiate_generic_source_scheme_for_source ctxt (#serial mixed)
       (#hol_term mixed) [(NONE, Position.none), (SOME \<^typ>\<open>8 word\<close>, Position.none),
         (NONE, Position.none)]) andalso
     is_none (M.instantiate_generic_source_scheme_for_source ctxt (#serial mixed)
       (#hol_term mixed) [(SOME \<^typ>\<open>bool\<close>, Position.none),
         (SOME \<^typ>\<open>8 word\<close>, Position.none), (NONE, Position.none)]) andalso
     is_none (M.instantiate_generic_scheme_for_source ctxt (#serial mixed) (#hol_term mixed)
       [(\<^typ>\<open>bool\<close>, Position.none), (\<^typ>\<open>8 word\<close>, Position.none),
         (\<^typ>\<open>0\<close>, Position.none)]))
  fun rejected_source current label expected text =
    let
      val rust_type = parsed current label text
      val observed = capture (fn () => Reports.capture (fn () => M.resolve_type_identity current rust_type))
      val _ = error_message label expected (#result observed)
      val _ = require (label ^ ": failed source read leaked native or navigation reports")
        (null (#markup observed) andalso #reports observed = "" andalso #output observed = "")
    in () end
  val _ = List.app (fn (label, shape) =>
    rejected_source ctxt label "in an erased argument" ("ErasureBox<" ^ shape ^ ",0>"))
    [("erasure-pointer", "*const u8"), ("erasure-reference", "&mut u8"),
     ("erasure-array", "[u8;4]"), ("erasure-slice", "[u8]"),
     ("erasure-callable", "fn(u8)->u8"), ("erasure-impl-trait", "impl Marker"),
     ("erasure-hol", "\<tau>" ^ cartouche "bool"),
     ("erasure-nested-pointer", "foreign::Tag<*const u8>")]
  val _ = rejected_source ctxt "erasure-associated-binding" "associated type bindings"
    "ErasureBox<Foreign<Item=u8>,0>"
  val _ = rejected_source ctxt "erasure-const-expression" "const expression generic arguments"
    "ErasureBox<Foreign<{1+2}>,0>"
  val _ = rejected_source ctxt "erasure-known-arity" "generic arities"
    "ErasureBox<ErasureMixed<Foreign>,0>"
  val _ = rejected_source ctxt "erasure-suffixed-number" "unsuffixed"
    "ErasureBox<Foreign,0usize>"
  fun parameter rust kind hol : M.generic_parameter =
    {rust = rust, pos = start "erasure-scope", kind = kind, hol = hol,
     bounds = [], report_reference = K ()}
  val scoped = M.with_generic_scope {parameters =
    [parameter "T" URust_AST.Type_Parameter ("'erasure_t", \<^sort>\<open>type\<close>),
     parameter "N" URust_AST.Const_Parameter ("'erasure_n", \<^sort>\<open>len0\<close>)]} ctxt
  fun imported_binding alias : URust_Import_Scope.binding =
    {alias = alias, alias_pos = start "erasure-import", namespace = URust_Import_Scope.Type_Namespace,
     key = "ErasureBoundEvidence", roles = [URust_Import_Scope.Mapped_Type], available = true,
     identity = serial (), declaration_pos = start "erasure-import"}
  val imported_scope = URust_Import_Scope.push_frame
    [imported_binding "T", imported_binding "N"] scoped
  fun observed_identity current label text =
    let val rust_type = parsed current label text
        val ((value, _), events) = M.capture_generic_use_events current (fn observed =>
          Reports.capture (fn () => M.resolve_type_identity observed rust_type))
    in (Option.map M.source_identity_name (#2 value), events) end
  val (scoped_identity, scoped_events) =
    observed_identity scoped "erasure-import-expected" "ErasureBox<T,0>"
  val (imported_identity, imported_events) =
    observed_identity imported_scope "erasure-import-actual" "ErasureBox<T,0>"
  val _ = require "source scope precedes same-spelled imports without losing source-only observations"
    (scoped_identity = imported_identity andalso scoped_events = imported_events andalso
     #source_uses imported_events = ["'erasure_t"] andalso null (#witness_uses imported_events))
  val imported_wrong_type = parsed imported_scope "erasure-import-wrong-kind" "ErasureBox<N,0>"
  val imported_failure = capture (fn () => Reports.capture
    (fn () => M.resolve_type_identity imported_scope imported_wrong_type))
  val imported_message = error_message "erasure-import-wrong-kind"
    "const parameters used as type arguments" (#result imported_failure)
  val imported_positions = Generic_Syntax_Test.message_positions imported_message
  val _ = require "same-spelled imports preserve the responsible scoped argument position and rollback"
    (not (null imported_positions) andalso
     Generic_Syntax_Test.position_range (hd imported_positions) = (12, 13) andalso
     Position.file_of (hd imported_positions) = SOME "erasure-import-wrong-kind" andalso
     null (#markup imported_failure) andalso #reports imported_failure = "")
  val _ = rejected_source imported_scope "erasure-import-scoped-projection"
    "associated paths on scoped parameters" "ErasureBox<T::Tag,0>"
  val _ = rejected_source scoped "erasure-type-as-const" "type parameters used as const arguments"
    "ErasureBox<Foreign,T>"
  val _ = rejected_source scoped "erasure-const-as-type" "const parameters used as type arguments"
    "ErasureBox<N,0>"
  val _ = rejected_source scoped "erasure-scoped-projection" "associated paths on scoped parameters"
    "ErasureBox<T::Tag,0>"
  val _ = rejected_source scoped "erasure-nested-scoped-projection" "associated paths on scoped parameters"
    "ErasureBox<Foreign<N::Tag>,0>"
  fun rejected_function label expected item =
    let
      val text = "urust_fn [verbosity = 0] " ^ cartouche item
      val observed = capture (fn () => run thy label text)
      val _ = error_message label expected (#result observed)
      val markup = #markup observed
      (* Keep the owner's established lexical/header/binder diagnostics. Failed candidates must
         publish no positioned semantic entities or semantic types at their source arguments. *)
      val semantic = filter (fn (name, props) => name = Markup.entityN andalso
        Properties.get props Markup.kindN <> SOME "urust_var" andalso
        is_some (Properties.get props Markup.offsetN)) markup
      val _ = require (label ^ ": failed declaration published semantic navigation or output")
        (null semantic andalso #output observed = "")
      val _ = if String.isSubstring "::<" text then
        let
          val first = find_from text "::<" 0 + size "::<"
          val last = find_from text ">" first
          val begin = Position.symbol_explode (String.substring (text, 0, first)) (start label)
          val stop = Position.symbol_explode (String.substring (text, first, last - first)) begin
          fun argument props = case Position.offset_of (Position.of_properties props) of
              SOME offset => offset >= the (Position.offset_of begin) andalso
                offset < the (Position.offset_of stop)
            | NONE => false
          fun lexical props = exists (fn (name, other) =>
            member (op =) [Markup.keyword1N, Markup.keyword2N, Markup.keyword3N,
              Markup.delimiterN, Markup.numeralN] name andalso
            Properties.get props Markup.offsetN = Properties.get other Markup.offsetN andalso
            Properties.get props Markup.end_offsetN = Properties.get other Markup.end_offsetN) markup
          val leaked = filter (fn (name, props) => argument props andalso
            (member (op =) [Markup.entityN, Markup.sortingN, Markup.tfreeN, Markup.tvarN] name orelse
             name = Markup.typingN andalso not (lexical props))) markup
        in require (label ^ ": failed candidate published semantic argument reports") (null leaked) end
        else ()
    in () end
  val _ = rejected_function "erasure-missing-witness" "does not occur in the signature"
    "fn ErasureMissingWitness<T,const N:usize>(value:ErasureBox<T,N>)->ErasureBox<T,N>{let _ = N; value}"
  val _ = rejected_function "erasure-missing-inference" "require explicit source arguments"
    "fn ErasureMissingInference(value:ErasureBox<Foreign,0>)->ErasureBox<Foreign,0>{ErasureIdentity(value)}"
  val _ = rejected_function "erasure-selected-kind" "type parameters used as const arguments"
    "fn ErasureWrongKind<T>(value:ErasureBox<T,0>)->ErasureBox<T,0>{ErasureIdentity::<T,T>(value)}"
  val _ = rejected_function "erasure-selected-unknown-retained" "unknown Rust type"
    "fn ErasureWrongRetained(value:ErasureMixed<Foreign,u8,0>)->ErasureMixed<Foreign,u8,0>{ErasureMixedIdentity::<Foreign,Unknown,0>(value)}"
  val _ = rejected_function "erasure-selected-bound" "no denotation to validate sort"
    "fn ErasureWrongBound(value:ErasureBox<Foreign,0>)->ErasureBox<Foreign,0>{ErasureBound::<Foreign>(value)}"
  val _ = rejected_function "erasure-scoped-bound" "function argument"
    "fn ErasureScopeBound<T>(value:ErasureBox<T,0>)->ErasureBox<T,0>{ErasureBound::<T>(value)}"
  val calls = Unsynchronized.ref 0
  val deferred_parameter: M.generic_parameter =
    {rust = "T", pos = start "erasure-deferred", kind = URust_AST.Type_Parameter,
     hol = ("'erasure_deferred", \<^sort>\<open>type\<close>), bounds = [],
     report_reference = fn _ => calls := !calls + 1}
  val deferred_scope = M.with_generic_scope {parameters = [deferred_parameter]} ctxt
  val ((_, deferred_events), pending) = Reports.capture_isolated (fn () =>
    M.capture_generic_argument_events deferred_scope (fn observed =>
      M.report_generic_source_reference observed deferred_parameter (start "erasure-deferred")))
  val _ = require "speculative scope capture executed an original callback before selection" (!calls = 0)
  val _ = M.replay_generic_argument_events deferred_scope deferred_events
  val _ = Reports.replay deferred_scope pending
  val _ = require "selected scope replay invokes the original callback exactly once" (!calls = 1)
  val failed_scope = Exn.capture (fn () => Reports.capture_isolated (fn () =>
    M.capture_generic_argument_events deferred_scope (fn observed =>
      (M.report_generic_source_reference observed deferred_parameter (start "erasure-discarded");
       error "discarded speculative argument")))) ()
  val _ = error_message "discarded speculative callback" "discarded speculative argument" failed_scope
  val _ = require "failed speculative capture invoked a discarded callback" (!calls = 1)
  val _ = M.report_generic_source_reference deferred_scope deferred_parameter (start "erasure-ordinary")
  val _ = require "speculative failure changed ordinary immediate scope callback behavior" (!calls = 2)
  val _ = require "all failed source and declaration probes preserve the original registries"
    (neighboring_snapshot [] ctxt = previous)
  val _ = writeln "U2 erased kinds/shapes/identity/finalization/availability/legacy/atomicity PASS"
in end
\<close>

section\<open> Combined sparse call schemes \<close>

ML_val\<open>
  local
    open Parser_Trait_Test
    structure M = URust_Type_Mappings
    val ctxt = \<^context>
    val entry = the_single (Parser_Test_Calls.entries ctxt "GenericCombinedIdentity")
    val slots = the (M.generic_source_scheme_for_source ctxt (#serial entry))
    val _ = require "combined source scheme preserves payload, tag, const and witness availability"
      (map #rust slots = ["P", "Tag", "N"] andalso
        map #kind slots = [URust_AST.Type_Parameter, URust_AST.Type_Parameter, URust_AST.Const_Parameter]
        andalso map (is_some o #hol) slots = [true, false, false])
    fun argument text =
      URust_Parser.parse_generic_argument_source ctxt (source "combined-call-argument" text)
    val resolved = M.resolve_source_arguments ctxt slots
      (map argument ["u8", "foreign::Policy<0>", "0"])
    val _ = require "combined explicit call manufactures an erased witness"
      (map fst (#arguments resolved) = [SOME \<^typ>\<open>8 word\<close>, NONE, NONE])
    val instantiated = the (M.instantiate_generic_source_scheme_for_source ctxt
      (#serial entry) (#hol_term entry) (#arguments resolved))
    val _ = require "sparse instantiation adds a semantic argument or changes the complete function arity"
      (length (binder_types (fastype_of instantiated)) = 1 andalso
        #2 (Term.strip_comb instantiated) = [])
    fun principal name =
      let
        val typ = Sign.the_const_type \<^theory> (Proof_Context.intern_const ctxt name)
        val substitutions = Term.add_tvarsT typ [] |> rev
          |> map_index (fn (index, variable as (_, sort)) =>
            (variable, TVar (("combined_type", index), sort))) |> TVars.make
      in Term_Subst.instantiateT substitutions typ end
    val _ = List.app (fn (native, escaped) =>
      require (native ^ ": complete principal type/sorts/sharing/channels differ")
        (principal native = principal escaped))
      [("generic_combined_identity", "generic_combined_escape"),
       ("generic_combined_call", "generic_combined_call_twin")]
    val _ = Generic_Signature_Test.require_scope_closed "combined declarations" ctxt
  in val _ = () end
\<close>

chapter\<open> Rich headers and declared denotation \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  open URust_AST
  val thy = \<^theory>
  val ctxt = \<^context>
  val old_names = snapshot ctxt
  val old_schemes = scheme_snapshot ctxt
  val complete = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun command options target typ rust =
    "urust_fn [" ^ options ^ "verbosity = 0] " ^ target ^ " :: " ^ cartouche typ ^ " " ^ cartouche rust
  fun item parameters predicates =
    "fn RetainedHeader<" ^ parameters ^ ">(value: Unknown) -> Unknown " ^ predicates ^ "{ value }"
  val rows =
    [("generic-trait", "T: outer::Trait<u8>", ""),
     ("generic-trait-bare-const", "const N: usize, T: Marker<N>", ""),
     ("associated-type", "T: outer::Sequence<Item = T>", ""),
     ("nested-associated-type", "'a, T: outer::Sequence<Item = Inner<&'a T>>", ""),
     ("empty-trait-arguments", "T: Trait<>", ""),
     ("callable-zero", "F: Fn()", ""),
     ("callable-unit", "F: Fn(())", ""),
     ("callable-many", "F: std::ops::FnMut(Unknown, (u8, bool),) -> Unknown", ""),
     ("callable-once", "F: FnOnce(Unknown)", ""),
     ("callable-elided-reference", "F: Fn(&Unknown) -> &Unknown", ""),
     ("callable-placeholder-reference", "F: Fn(&'_ Unknown) -> &'_ Unknown", ""),
     ("trait-function-pointer-elision", "T: Marker<fn(&Unknown) -> &Unknown>", ""),
     ("where-function-pointer-elision", "T", "where fn(&Unknown) -> &Unknown: Marker, "),
     ("compat-first-for-identifier", "for", ""),
     ("compat-later-for-identifier", "T, for", ""),
     ("compat-for-where-head", "for", "where for: Marker, "),
     ("compat-for-plain-bound", "T: for", ""),
     ("compat-for-qualified-bound", "T: outer::for", ""),
     ("compat-for-generic-trait", "T: for<u8>", ""),
     ("inline-outlives", "'a: 'b, 'b, T: 'a + 'static", ""),
     ("where-outlives", "'a, 'b, T", "where 'a: 'b, T: 'static, "),
     ("where-qualified", "T", "where outer::Head<T>: outer::Trait<T>, "),
     ("where-tuple", "T", "where (T, u8): Unknown, "),
     ("where-array", "T, const N: usize", "where [T; N]: Unknown, "),
     ("higher-ranked", "F: for<'a,> Fn(&'a Unknown) -> Unknown", ""),
     ("higher-ranked-empty", "F: for<> Fn()", ""),
     ("higher-ranked-where", "F", "where F: for<'a> Fn(&'a Unknown), "),
     ("higher-ranked-head", "T", "where for<'a> &'a T: Unknown, "),
     ("higher-ranked-empty-head", "F", "where for<> F: Fn(), "),
     ("conditional-const", "F: [const] FnOnce(Unknown) -> Unknown + [const] Marker", ""),
     ("higher-ranked-const", "F: for<'a> [const] FnOnce(&'a Unknown)", ""),
     ("trailing-plus", "T: outer::Trait<u8> +", "where T: Marker +, "),
     ("ordinary-mapped-bound", "T: Scale", ""),
     ("const-u8", "const N: u8", ""),
     ("const-u64", "const N: u64", ""),
     ("const-bool", "const N: bool", ""),
     ("const-char", "const N: char", ""),
     ("const-named", "const N: UnmappedLength", "")]
  fun check (label, parameters, predicates) =
    let
      val rust = item parameters predicates
      val _ = roundtrip ctxt (label ^ "-standalone") rust
      val chunk_source = rust ^ "\nimpl UnmappedOwner { " ^ rust ^ " }"
      val parsed = chunk ctxt (label ^ "-placements") chunk_source
      val _ = List.app (fn options =>
        let val printed = URust_Printer.string_of_chunk options parsed
            val again = chunk ctxt (label ^ "-placements-printed") printed
        in require (label ^ ": chunk/member structured roundtrip changed")
          (URust_Printer.tokens_of_chunk options parsed = URust_Printer.tokens_of_chunk options again)
        end) [URust_Printer.serialized_options, URust_Printer.human_options]
      val text = command "pp_test, " "retained_actual" complete rust ^ "\n" ^
        command "" "retained_plain" complete "fn RetainedPlain(value: Unknown) -> Unknown { value }" ^
        "\nlemma retained_twin: " ^ cartouche "retained_actual = retained_plain" ^
        " unfolding retained_actual_def retained_plain_def by (rule refl)"
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => run thy label text)
      val completed = Exn.release result |> Toplevel.context_of
      val actual = entry completed "RetainedHeader"
      val slots = entry_scheme completed actual
      val descriptors = function_type_parameters (parse completed label rust)
      val _ = check_header label descriptors slots
      val _ = require (label ^ ": complete type/sorts/channels changed")
        (Sign.typ_equiv (Proof_Context.theory_of completed)
          (fastype_of (#hol_term actual), Logic.varifyT_global (Syntax.read_typ completed complete)))
      val reports = fold Parser_Test_Reports.collect_markup (trees "report" events) []
      val _ = require (label ^ ": ignored header resolved a Rust trait/type mapping")
        (not (exists (fn (name, props) => name = Markup.entityN andalso
          Library.member (op =) ["urust_trait", "micro_rust_type_mapping"]
            (the_default "" (Properties.get props Markup.kindN))) reports))
      val _ = require (label ^ ": legacy scheme or declaration reports missing")
        (length slots = length descriptors andalso not (null (declaration_reports events)))
      val _ = require (label ^ ": source registries or native callbacks escaped the transaction")
        (snapshot ctxt = old_names andalso scheme_snapshot ctxt = old_schemes andalso
          same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val _ = require_scope_closed label completed
    in () end
  val _ = List.app check rows
  val _ = List.app (fn (label, rust) =>
    let
      val _ = roundtrip ctxt label rust
      val completed = run thy label (command "pp_test, " "compat_for" complete rust)
        |> Toplevel.context_of
      val _ = require_scope_closed label completed
    in () end)
    [("compat-exact-first-for", "fn Compat<for>(value: for) -> for { value }"),
     ("compat-exact-later-for", "fn Compat<T, for>(value: T) -> T { value }"),
     ("compat-exact-for-head", "fn Compat<for>(value: for) -> for where for: Marker { value }"),
     ("compat-exact-for-bound", "fn Compat<T: for>(value: T) -> T { value }")]
  val weak = entry ctxt "DeclaredWeakSort"
  val _ = require "explicit parameter-name sorts and ordinary bounds cannot strengthen a complete type"
    (map #hol (entry_scheme ctxt weak) = [("'payload", \<^sort>\<open>type\<close>)] andalso
      Sign.typ_equiv (Proof_Context.theory_of ctxt)
        (fastype_of (#hol_term weak), Logic.varifyT_global
          \<^typ>\<open>'payload \<Rightarrow> ('s, 'payload, 'abort, 'i, 'o) function_body\<close>))
  val _ = require "ignored bounds cannot populate a declared source scheme's trait keys"
    (forall (null o #bounds)
      (the (URust_Type_Mappings.generic_source_scheme_for_source ctxt (#serial weak))))
  val _ = require "non-usize declared const metadata keeps the old unused witnessed convention"
    (map #hol (entry_scheme ctxt (entry ctxt "DeclaredRichHeader")) =
      [("'t", \<^sort>\<open>type\<close>), ("'n", \<^sort>\<open>len0\<close>)])
in val _ = () end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val complete = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun command typ rust =
    "urust_fn [verbosity = 0] retained_failure :: " ^ cartouche typ ^ " " ^ cartouche rust
  val structural_rows =
    [("missing-associated-type", "syntax error", complete,
       "fn Bad<T: Sequence<Item =>>(value: Unknown) { value }"),
     ("missing-callable-result", "syntax error", complete,
       "fn Bad<F: Fn() ->>(value: Unknown) { value }"),
     ("missing-const-trait", "syntax error", complete,
       "fn Bad<T: [const]>(value: Unknown) { value }"),
     ("empty-local-binder-comma", "syntax error", complete,
       "fn Bad<F: for<,> Fn()>(value: Unknown) { value }"),
     ("duplicate-const-modifier", "syntax error", complete,
       "fn Bad<T: [const] [const] Unknown>(value: Unknown) { value }"),
     ("duplicate-for-modifier", "syntax error", complete,
       "fn Bad<F: for<'a> for<'b> Fn(&'a &'b Unknown)>(value: Unknown) { value }"),
     ("const-before-for", "syntax error", complete,
       "fn Bad<F: [const] for<'a> Fn(&'a Unknown)>(value: Unknown) { value }"),
     ("const-outlives-modifier", "syntax error", complete,
       "fn Bad<'a, T: [const] 'a>(value: Unknown) { value }"),
     ("for-outlives-modifier", "syntax error", complete,
       "fn Bad<T: for<'a> 'a>(value: Unknown) { value }"),
     ("for-lifetime-predicate", "syntax error", complete,
       "fn Bad<'b>(value: Unknown) where for<'a> 'a: 'b { value }"),
     ("duplicate-local-binder", "duplicate lifetime parameter", complete,
       "fn Bad<F: for<'a, 'a> Fn(&'a Unknown)>(value: Unknown) { value }"),
     ("shadow-item-lifetime", "shadows an enclosing lifetime", complete,
       "fn Bad<'a, F: for<'a> Fn(&'a Unknown)>(value: Unknown) { value }"),
     ("undeclared-local-lifetime", "undeclared lifetime \"'b\"", complete,
       "fn Bad<F: for<'a> Fn(&'b Unknown)>(value: Unknown) { value }"),
     ("local-binder-leak", "undeclared lifetime \"'a\"", complete,
       "fn Bad<F: for<'a> Fn(&'a Unknown)>(value: &'a Unknown) { value }"),
     ("undeclared-associated-lifetime", "undeclared lifetime \"'a\"", complete,
       "fn Bad<T: Sequence<Item = &'a Unknown>>(value: Unknown) { value }"),
     ("generic-trait-reference-elision", "reference lifetime must be explicit in a generic trait bound", complete,
       "fn Bad<T: Marker<&Unknown>>(value: Unknown) { value }"),
     ("generic-trait-placeholder-lifetime", "placeholder lifetime", complete,
       "fn Bad<T: Marker<'_>>(value: Unknown) { value }"),
     ("generic-trait-placeholder-reference", "placeholder lifetime", complete,
       "fn Bad<T: Marker<&'_ Unknown>>(value: Unknown) { value }"),
     ("associated-reference-elision", "reference lifetime must be explicit in a generic trait bound", complete,
       "fn Bad<T: Sequence<Item = &Unknown>>(value: Unknown) { value }"),
     ("nested-function-pointer-lifetime", "undeclared lifetime \"'missing\"", complete,
       "fn Bad<T: Marker<fn(&'missing Unknown)>>(value: Unknown) { value }"),
     ("callable-unconstrained-result", "callable result lifetime must be explicit", complete,
       "fn Bad<F: Fn() -> &Unknown>(value: Unknown) { value }"),
     ("callable-ambiguous-result", "callable result lifetime must be explicit", complete,
       "fn Bad<F: Fn(&Unknown, &Unknown) -> &Unknown>(value: Unknown) { value }"),
     ("callable-repeated-named-result", "callable result lifetime must be explicit", complete,
       "fn Bad<'a, F: Fn(&'a Unknown, &'a Unknown) -> &Unknown>(value: Unknown) { value }"),
     ("callable-pointer-result-scope", "callable result lifetime must be explicit", complete,
       "fn Bad<F: Fn(fn(&Unknown) -> &Unknown) -> &Unknown>(value: Unknown) { value }"),
     ("placeholder-outlives", "placeholder lifetime", complete,
       "fn Bad<T: '_>(value: Unknown) { value }"),
     ("where-reference-elision", "reference lifetime must be explicit", complete,
       "fn Bad<T>(value: Unknown) where &T: Unknown { value }"),
     ("where-const-kind", "const parameters cannot be used as type where heads", complete,
       "fn Bad<const N: usize>(value: Unknown) where N: Marker { value }"),
     ("where-grouped-const-kind", "const parameters cannot be used as type where heads", complete,
       "fn Bad<const N: usize>(value: Unknown) where (N): Marker { value }"),
     ("where-type-length-kind", "type parameters cannot be used as const where operands", complete,
       "fn Bad<T>(value: Unknown) where [u8; T]: Marker { value }"),
     ("callable-const-kind", "const parameters cannot be used as callable type operands", complete,
       "fn Bad<const N: usize, F: Fn(N)>(value: Unknown) { value }"),
     ("associated-type-const-kind", "const parameters cannot be used as generic trait type operands", complete,
       "fn Bad<const N: usize, T: Sequence<Item = N>>(value: Unknown) { value }"),
     ("trait-array-type-length-kind", "type parameters cannot be used as const generic trait operands", complete,
       "fn Bad<T, U: Marker<[u8; T]>>(value: Unknown) { value }")]
  val rows = structural_rows @
    [("body-unmapped-type", "unknown Rust type", complete,
       "fn Bad<T: Unknown>(value: Unknown) { SignatureIdentity::<UnmappedBody>(value) }"),
     ("body-absent-type", "generic parameter T does not occur in the signature", complete,
       "fn Bad<T: Unknown>(value: Unknown) { SignatureIdentity::<T>(value) }"),
     ("body-absent-erased-source", "generic parameter T does not occur in the signature", complete,
       "fn Bad<T: Unknown>(value: Unknown) { ErasureIdentity::<T, 0>(value) }"),
     ("body-absent-const", "generic parameter N does not occur in the signature", complete,
       "fn Bad<const N: bool>(value: Unknown) { N }"),
     ("body-weak-trait", "no associated constant CEILING",
       "'t => ('s, nat, 'abort, 'i, 'o) function_body",
       "fn Bad<T: Scale>(marker: Unknown) { T::CEILING }"),
     ("body-weak-const", "does not satisfy sort len0", "'n => ('s, 64 word, 'abort, 'i, 'o) function_body",
       "fn Bad<const N: usize>(marker: Unknown) { N }")]
  val old_names = snapshot ctxt
  val old_schemes = scheme_snapshot ctxt
  val _ = List.app (fn (label, expected, typ, rust) =>
    let
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () =>
        failure label expected (fn () => run thy label (command typ rust)))
      val diagnostic = Exn.release result
      val _ = require (label ^ ": genuine failure has no position")
        (not (null (message_positions diagnostic)))
      val _ = require (label ^ ": failed declaration leaked successful output or definition reports")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": failure changed registries/callbacks")
        (snapshot ctxt = old_names andalso scheme_snapshot ctxt = old_schemes andalso
          same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val _ = if Library.member (op =) (map #1 structural_rows) label then
        let
          val (authoritative, authoritative_events) = capture (fn () =>
            failure (label ^ "-authoritative") expected (fn () =>
              run thy (label ^ "-authoritative")
                ("urust_fn [verbosity = 0] retained_failure " ^ cartouche rust)))
          val _ = require (label ^ ": authoritative structural error has no position")
            (not (null (message_positions (Exn.release authoritative))))
          val _ = require (label ^ ": authoritative failure leaked successful reports/output")
            (null (ordinary authoritative_events) andalso
              null (declaration_reports authoritative_events))
          val _ = if expected = "syntax error" then
            ignore (failure (label ^ "-raw") expected (fn () => parse ctxt (label ^ "-raw") rust))
            else ()
        in () end else ()
      val recovered = run thy (label ^ "-recovery")
        (command complete "fn RetainedRecovery(value: Unknown) { value }") |> Toplevel.context_of
      val _ = require (label ^ ": recovery did not install its ordinary declaration")
        (is_some (Parser_Test_Calls.lookup recovered "RetainedRecovery"))
      val _ = require_scope_closed label recovered
    in () end) rows
in val _ = () end
\<close>

section\<open> Complete callable types and native declaration artifacts \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val callback = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  val complete = "(" ^ callback ^ ") => nat => ('s, nat, 'abort, 'i, 'o) function_body"
  val rich = "fn RetainedArtifact<F: Fn() + Unregistered, T: Scale, const N: char>" ^
    "(callback: Unknown, value: Unknown) -> Unknown { value }"
  val plain = "fn RetainedArtifactPlain(callback: Unknown, value: Unknown) -> Unknown { value }"
  fun command options target rust =
    "urust_fn [" ^ options ^ "pp_test, verbosity = 0] " ^ target ^ " :: " ^
      cartouche complete ^ " " ^ cartouche rust
  val _ = List.app (fn (label, options, abbreviation, registered) =>
    let
      val text = command options "retained_artifact" rich ^ "\n" ^
        command options "retained_artifact_plain" plain ^ "\n" ^
        "lemma retained_artifact_twin: " ^
        cartouche "retained_artifact = retained_artifact_plain" ^
        (if abbreviation then "" else
          " unfolding retained_artifact_def retained_artifact_plain_def") ^ " by (rule refl)"
      val completed = run thy label text |> Toplevel.context_of
      val actual = Proof_Context.read_const {proper = true, strict = false}
        completed "retained_artifact"
      val twin = Proof_Context.read_const {proper = true, strict = false}
        completed "retained_artifact_plain"
      val _ = require (label ^ ": complete callback arity, sorts or channels changed")
        (Sign.typ_equiv (Proof_Context.theory_of completed)
          (fastype_of actual, Logic.varifyT_global (Syntax.read_typ completed complete)) andalso
         Sign.typ_equiv (Proof_Context.theory_of completed) (fastype_of actual, fastype_of twin) andalso
         length (binder_types (fastype_of actual)) = 2 andalso
         length (binder_types (hd (binder_types (fastype_of actual)))) = 1)
      val _ = require (label ^ ": native source scheme lost ordered compatibility slots")
        (map #rust (scheme completed actual) = ["F", "T", "N"])
      val _ = require (label ^ ": automatic registration policy changed")
        (not (null (Parser_Test_Calls.entries completed "RetainedArtifact")) = registered)
      val _ = if abbreviation then () else
        let
          val definition = Proof_Context.get_thm completed "retained_artifact_def"
          val twin_definition = Proof_Context.get_thm completed "retained_artifact_plain_def"
          val _ = require (label ^ ": native definition theorem scheme changed")
            (Sign.typ_equiv (Proof_Context.theory_of completed)
              (fastype_of (snd (Logic.dest_equals (Thm.prop_of definition))),
               fastype_of (snd (Logic.dest_equals (Thm.prop_of twin_definition)))))
        in () end
      val _ = require_scope_closed label completed
    in () end)
    [("retained-definition", "", false, true),
     ("retained-application-definition", "application_def, ", false, true),
     ("retained-abbreviation", "abbrev, ", true, true),
     ("retained-disabled", "register_notation = false, ", false, false)]
  val anonymous = run thy "retained-anonymous" (command "" "_" rich) |> Toplevel.context_of
  val _ = require "anonymous complete rich declaration leaves the native namespace unchanged"
    (snapshot anonymous = snapshot ctxt)
  val _ = require_scope_closed "retained-anonymous" anonymous
in val _ = () end
\<close>

section\<open> Native bound-local lifetime identities and ranges \<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val label = "retained-lifetime-reports"
  val escaped = str (Char.chr 92) ^ "<alpha>"
  val comment = "/* " ^ escaped ^ " nested /* inner */ comment */"
  val rust = comment ^ " fn HeaderReport<'left: 'right, 'right, " ^
    "F: for " ^ comment ^ " <'local> [const] Fn(&'local Unknown) -> &'left Unknown, " ^
    "T: Sequence<" ^ comment ^ " Item = &'right Unknown>>(value: &'left Unknown) -> &'right Unknown " ^
    "where for<'nested> &'nested T: Unknown, 'left: 'right { value }"
  val text = "urust_fn [pp_test, verbosity = 0] retained_lifetime_reports :: " ^
    cartouche "nat => ('state, nat, 'exit, 'input, 'output) function_body" ^ " " ^ cartouche rust
  val (result, events) = capture (fn () => run thy label text)
  val completed = Exn.release result |> Toplevel.context_of
  val all_reports = fold Parser_Test_Reports.collect_markup (trees "report" events) []
  val reports = all_reports
    |> filter (fn (name, props) => name = Markup.entityN andalso
      Properties.get props Markup.kindN = SOME "urust_lifetime")
  fun identity property name occurrence =
    reports |> filter (fn (_, props) =>
      Properties.get props Markup.nameN = SOME name andalso
      Properties.get props Markup.fileN = SOME label andalso
      position_range (Position.of_properties props) = range_of text name occurrence)
    |> map_filter (fn (_, props) => Properties.get props property)
    |> the_single
  val _ = List.app (fn (name, declaration, references) =>
    let
      val declared = identity Markup.defN name declaration
      val _ = List.app (fn occurrence =>
        require (name ^ ": reference lost its actual local declaration identity/range")
          (identity Markup.refN name occurrence = declared)) references
    in () end)
    [("'left", 0, [1, 2, 3]), ("'right", 1, [0, 2, 3, 4]),
     ("'local", 0, [1]), ("'nested", 0, [1])]
  val _ = require "lifetime identity reports contain exactly the retained header declarations and uses"
    (length reports = 13)
  val _ = require "escaped-symbol rich header comment retains its native symbol range"
    (exists (fn (name, props) => name = Markup.comment1N andalso
      position_range (Position.of_properties props) = range_of text comment 0) all_reports)
  val _ = require "comment-separated rich binder retains its native keyword symbol range"
    (exists (fn (name, props) => name = Markup.keyword1N andalso
      position_range (Position.of_properties props) = range_of text "for" 0) all_reports)
  val _ = require "an absent generic in an ignored header retains lexical declaration navigation"
    (exists (fn (name, props) => name = Markup.entityN andalso
      Properties.get props Markup.kindN = SOME "urust_generic_parameter" andalso
      Properties.get props Markup.nameN = SOME "T" andalso
      is_some (Properties.get props Markup.refN) andalso
      position_range (Position.of_properties props) = range_of text "T" 1) all_reports)
  val _ = require "an absent generic header reference receives no HOL typing tooltip"
    (not (exists (fn (name, props) => name = Markup.typingN andalso
      position_range (Position.of_properties props) = range_of text "T" 1) all_reports))
  val parsed = roundtrip ctxt (label ^ "-roundtrip") rust
  val _ = require "rich wrapper and associated payload preserve exact symbol token ranges"
    (case #parameters (URust_AST.function_generics parsed) of
       [_, _, URust_AST.Generic_Type (_, _,
           [URust_AST.Rust_For_Bound (_, URust_AST.Rust_Const_Bound (_, const_layout), for_layout)]),
          URust_AST.Generic_Type (_, _, [URust_AST.Rust_Generic_Trait_Bound
            (URust_AST.Path_Type ([URust_AST.Rust_Type_Path_Segment (_, _, SOME
              [URust_AST.Rust_Associated_Type_Argument (_, item_pos,
                URust_AST.Reference_Type (_, SOME (URust_AST.Rust_Lifetime (_, lifetime_pos)),
                  _, _))], _)], _), _)])] =>
         map position_range (URust_AST.source_token_positions for_layout
           (URust_AST.Keyword_Token "for")) = [range_of rust "for" 0] andalso
         map position_range (URust_AST.source_token_positions const_layout
           (URust_AST.Keyword_Token "const")) = [range_of rust "const" 0] andalso
         position_range item_pos = range_of rust "Item" 0 andalso
         position_range lifetime_pos = range_of rust "'right" 2
     | _ => false)
  val _ = require "rich lifetime report probe leaves the original namespace unchanged"
    (snapshot ctxt = snapshot (Proof_Context.init_global thy))
  val _ = require_scope_closed label completed
in val _ = () end
\<close>

section\<open> Inherited generic declaration identity \<close>

ML_val\<open>
local
  structure M = URust_Type_Mappings
  fun require label condition = if condition then () else error ("inherited generic identity: " ^ label)
  val ctxt = \<^context>
  val calls = Unsynchronized.ref 0
  val callback = fn _ => calls := !calls + 1
  val original: M.generic_parameter = {rust = "T", pos = Position.none,
    kind = URust_AST.Type_Parameter, hol = ("'inherited_identity", \<^sort>\<open>type\<close>),
    bounds = [], report_reference = callback}
  val refined: M.generic_parameter = {rust = #rust original, pos = #pos original,
    kind = #kind original, hol = (fst (#hol original), \<^sort>\<open>ord\<close>),
    bounds = ["identity::Ordered"], report_reference = callback}
  val local_parameter: M.generic_parameter = {rust = "U", pos = Position.none,
    kind = URust_AST.Type_Parameter, hol = ("'local_identity", \<^sort>\<open>type\<close>),
    bounds = [], report_reference = K ()}
  val declaration = M.fresh_generic_declaration_identity ()
  val local_declaration = M.fresh_generic_declaration_identity ()
  val inherited = M.with_identified_generic_scope {parameters = [original]} [declaration] ctxt
  val member_ctxt = M.with_identified_generic_scope {parameters = [refined, local_parameter]}
    [declaration, local_declaration] ctxt
  val _ = require "explicit transport retains inherited identity and ordered local extension"
    (M.generic_scope_identities inherited = SOME [declaration] andalso
      M.generic_scope_identities member_ctxt = SOME [declaration, local_declaration])
  val SOME {parameters = [after, local_after]} = M.generic_scope member_ctxt
  val _ = require "compatible records and exact callback objects survive transport"
    (pointer_eq (refined, after) andalso pointer_eq (local_parameter, local_after) andalso
      pointer_eq (callback, #report_reference after))
  val (_, events) = M.capture_generic_use_events inherited (fn observed =>
    let
      val refined_ctxt = M.with_identified_generic_scope {parameters = [refined, local_parameter]}
        [declaration, local_declaration] observed
      val _ = M.report_generic_reference refined_ctxt refined Position.none
    in () end)
  val _ = require "stable declaration tokens do not relax full-record observer membership"
    (null (#source_uses events) andalso null (#witness_uses events) andalso !calls = 1)
  val (_, original_events) = M.capture_generic_use_events inherited (fn observed =>
    M.report_generic_reference observed original Position.none)
  val _ = require "unchanged inherited record is observed exactly once"
    (#source_uses original_events = [fst (#hol original)] andalso
      #witness_uses original_events = [fst (#hol original)] andalso !calls = 2)
  val _ = require "isolated member refinement leaves parent records and availability unchanged"
    (case M.generic_scope inherited of SOME {parameters = [parameter]} =>
      pointer_eq (parameter, original) andalso M.parameter_available inherited parameter andalso
        M.parameter_has_witness inherited parameter | _ => false)
in end
\<close>


section\<open> Erased outlives scopes, source heads and transactions \<close>

ML_val\<open>
local
  open Generic_Signature_Test URust_AST
  structure M = URust_Type_Mappings
  val thy = \<^theory>
  val ctxt = Context_Position.set_visible true \<^context>
  fun parameters key = the (M.generic_source_scheme_for_source ctxt (#serial (entry ctxt key)))
  val _ = require "mixed outlives preserve the exact trait-only source scheme"
    (parameters "OutlivesMixed" = parameters "OutlivesMixedPlain")
  val _ = require "unused source-only heads preserve the exact legacy witness slots and masks"
    (parameters "OutlivesSourceOnly" = parameters "OutlivesSourceOnlyPlain" andalso
      forall (fn p => is_some (#hol p) andalso #source_used p = SOME false)
        (parameters "OutlivesSourceOnly"))
  val _ = require "declared outlives preserve authored types, source slots and ignored trait keys"
    (parameters "OutlivesDeclared" = parameters "OutlivesDeclaredPlain" andalso
      forall (null o #bounds) (parameters "OutlivesDeclared"))
  fun constant_type name = Sign.the_const_type thy
    (fst (dest_Const (Proof_Context.read_const {proper = true, strict = true} ctxt name)))
  val _ = List.app (fn (actual, plain) =>
    require (actual ^ ": complete constant types/sorts/channels are identical")
      (constant_type actual = constant_type plain))
    [("outlives_mixed", "outlives_mixed_plain"),
     ("outlives_source_only", "outlives_source_only_plain"),
     ("outlives_declared", "outlives_declared_plain")]

  val calls = Unsynchronized.ref ([]: Position.T list)
  val callback = fn pos => calls := pos :: !calls
  val parameter: M.generic_parameter = {rust = "T", pos = start "outlives-T",
    kind = Type_Parameter, hol = ("'outlives_t", \<^sort>\<open>ord\<close>),
    bounds = ["plain::Ordered"], report_reference = callback}
  val count: M.generic_parameter = {rust = "N", pos = start "outlives-N",
    kind = Const_Parameter, hol = ("'outlives_n", \<^sort>\<open>len0\<close>),
    bounds = [], report_reference = K ()}
  val identities = map (fn _ => M.fresh_generic_declaration_identity ()) [parameter, count]
  val installed = ctxt
    |> M.with_identified_generic_scope {parameters = [parameter, count]} identities
    |> M.with_source_only_parameters ["'outlives_t"]
    |> M.with_declared_body_parameters ["'outlives_t", "'outlives_n"]
  val before_state = snapshot installed
  val schemes = scheme_snapshot installed
  fun head text =
    let val f = parse installed "outlives-head" ("fn Head<'a>() where " ^ text ^ ": 'a {}")
    in case #where_clause (function_generics f) of [Rust_Type_Predicate (head, _, _)] => head
      | _ => error "outlives head fixture did not produce a positioned predicate" end
  val opaque = "\<tau>" ^ cartouche "_ 'unresolved_model"
  val heads = map head ["T", "Unmapped<T, N>", "qualified::Unmapped<T, N, 3, { 1 + 2 }>",
    "([T; N], *const T, fn(&u8) -> &u8)", "$Unexpanded", "$T", opaque]
  val (((), nested), outer) = M.capture_generic_use_events installed (fn observed =>
    M.capture_generic_use_events observed (fn nested =>
      List.app (M.check_outlives_head nested) heads))
  val _ = require "pure-head validation emits no nested or parent source/witness event"
    (null (#source_uses nested) andalso null (#witness_uses nested) andalso
      null (#source_uses outer) andalso null (#witness_uses outer) andalso null (!calls))
  val _ = require "pure-head validation preserves full records, callback objects, IDs and availability"
    (snapshot installed = before_state andalso scheme_snapshot installed = schemes andalso
      M.generic_scope_identities installed = SOME identities andalso
      (case M.generic_scope installed of SOME {parameters = [after, after_count]} =>
        #rust after = #rust parameter andalso #kind after = #kind parameter andalso
        #hol after = #hol parameter andalso #bounds after = #bounds parameter andalso
        Position.properties_of (#pos after) = Position.properties_of (#pos parameter) andalso
        PolyML.pointerEq (#report_reference after, callback) andalso
        #hol after_count = #hol count andalso
        not (M.parameter_available installed after) andalso
        not (M.parameter_has_witness installed after) andalso
        not (M.parameter_available installed after_count) andalso
        M.parameter_has_witness installed after_count | _ => false))

  fun collect (XML.Text _) = []
    | collect (XML.Elem (markup, body)) = markup :: maps collect body
  fun markup events = maps collect (trees "report" events)
  fun at text token occurrence props =
    position_range (Position.of_properties props) = range_of text token occurrence
  fun ids kind field text token occurrence properties =
    properties |> map_filter (fn (element, props) =>
      if element = Markup.entityN andalso Properties.get props Markup.kindN = SOME kind andalso
        at text token occurrence props then Properties.get props field else NONE)
  val prefix = "/* " ^ Symbol.open_ ^ " positioned " ^ Symbol.close ^ " */ "
  val retained = "\<tau>" ^ cartouche "T 'a '_"
  val rust = prefix ^
    "fn OutlivesNavigation<'a: 'b, 'b: 'a, T: 'b>(value: u8) -> u8 " ^
    "where 'a: 'a + 'b, u8: 'a, qualified::Opaque<&'a T>: 'b, T: 'static, " ^
    "$T: 'static, " ^ retained ^ ": 'static { value }"
  val text = "urust_fn [verbosity = 0] " ^ cartouche rust
  val callbacks = saved_callbacks ()
  val reporter = !Private_Output.report_fn
  val (result, events) = capture (fn () => run thy "outlives-navigation" text)
  val completed = Exn.release result |> Toplevel.context_of
  val properties = markup events
  val _ = List.app (fn (name, declaration, references) =>
    let val identity = the_single (ids "urust_lifetime" Markup.defN text name declaration properties)
    in List.app (fn occurrence => require "outlives lifetime uses navigate at exact symbol ranges"
      (ids "urust_lifetime" Markup.refN text name occurrence properties = [identity])) references
    end) [("'a", 0, [1, 2, 3, 4, 5]), ("'b", 1, [0, 2, 3, 4])]
  val identity = the_single (ids "urust_generic_parameter" Markup.defN text "T" 0 properties)
  val _ = List.app (fn occurrence =>
    require "pure-head generic navigation uses the original declaration at each visible token"
      (ids "urust_generic_parameter" Markup.refN text "T" occurrence properties = [identity]))
    [1, 2]
  val _ = require "opaque macro/model text invents no generic or lifetime navigation"
    (null (ids "urust_generic_parameter" Markup.refN text "T" 3 properties) andalso
      null (ids "urust_generic_parameter" Markup.refN text "T" 4 properties) andalso
      null (ids "urust_lifetime" Markup.refN text "'a" 6 properties) andalso
      null (ids "urust_lifetime" Markup.refN text "'_" 0 properties))
  val head_ranges = map (range_of text "T") [1, 2]
  val _ = require "source-only head references have lexical markup and no fabricated HOL typing"
    (forall (fn range => exists (fn (name, props) => name = Markup.tfreeN andalso
      position_range (Position.of_properties props) = range) properties andalso
      not (exists (fn (name, props) => name = Markup.typingN andalso
        position_range (Position.of_properties props) = range) properties)) head_ranges)
  val _ = require "pure-head navigation does not resolve nominal or trait mappings"
    (not (exists (fn (name, props) => name = Markup.entityN andalso
      Library.member (op =) ["urust_trait", "micro_rust_type_mapping"]
        (the_default "" (Properties.get props Markup.kindN)) andalso
      Library.member (op =)
        (range_of text "u8" 2 :: range_of text "qualified" 0 ::
          range_of text "Opaque" 0 :: head_ranges)
        (position_range (Position.of_properties props))) properties))
  val _ = require "header navigation preserves callbacks and closes scopes"
    (same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
  val _ = require_scope_closed "outlives navigation" completed
  val _ = writeln "S3 complete types/sorts/channels, source masks, full-record zero-event validation and exact native navigation PASS"
in end
\<close>

ML_val\<open>
local
  open Generic_Signature_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val old_names = snapshot ctxt
  val old_schemes = scheme_snapshot ctxt
  val prefix = "/* " ^ Symbol.open_ ^ " failure " ^ Symbol.close ^ " */ "
  val complete = "nat => ('state, nat, 'abort, 'input, 'output) function_body"
  fun command declared rust = "urust_fn [verbosity = 0] outlives_failure " ^
    (if declared then ":: " ^ cartouche complete ^ " " else "") ^ cartouche (prefix ^ rust)
  val structural =
    [("unknown-inline", "undeclared lifetime", "fn Bad<T: 'missing>(value: u8) -> u8 { value }", "'missing", 0),
     ("unknown-forward", "undeclared lifetime", "fn Bad<'a: 'missing>(value: u8) -> u8 { value }", "'missing", 0),
     ("unknown-where-head", "undeclared lifetime", "fn Bad<'a>(value: u8) -> u8 where 'missing: 'a { value }", "'missing", 0),
     ("unknown-where-bound", "undeclared lifetime", "fn Bad<'a>(value: u8) -> u8 where 'a: 'missing { value }", "'missing", 0),
     ("unknown-nominal-lifetime", "undeclared lifetime", "fn Bad<'a>(value: u8) -> u8 where Unknown<'missing>: 'a { value }", "'missing", 0),
     ("unknown-nested-reference", "undeclared lifetime", "fn Bad<'a>(value: u8) -> u8 where (&'missing u8): 'a { value }", "'missing", 0),
     ("placeholder-inline", "placeholder lifetime", "fn Bad<T: '_>(value: u8) -> u8 { value }", "'_", 0),
     ("placeholder-head", "placeholder lifetime", "fn Bad<'a>(value: u8) -> u8 where '_: 'a { value }", "'_", 0),
     ("placeholder-bound", "placeholder lifetime", "fn Bad<'a>(value: u8) -> u8 where 'a: '_ { value }", "'_", 0),
     ("placeholder-reference", "placeholder lifetime", "fn Bad<'a>(value: u8) -> u8 where &'_ u8: 'a { value }", "'_", 0),
     ("static-declaration", "cannot be declared as a lifetime parameter", "fn Bad<'static>(value: u8) -> u8 { value }", "'static", 0),
     ("placeholder-declaration", "cannot be declared as a lifetime parameter", "fn Bad<'_>(value: u8) -> u8 { value }", "'_", 0),
     ("head-elision", "reference lifetime must be explicit", "fn Bad<'a, T>(value: u8) -> u8 where &T: 'a { value }", "&", 0),
     ("const-head", "const parameters cannot be used as type where heads", "fn Bad<'a, const N: usize>(value: u8) -> u8 where (N): 'a { value }", "N", 1),
     ("type-length", "type parameters cannot be used as const where operands", "fn Bad<'a, T>(value: u8) -> u8 where [u8; T]: 'a { value }", "T", 1)]
  val shapes =
    [("bare-hole", "Rust inference holes", "fn Bad<'a>(value: u8) -> u8 where _: 'a { value }", "_", 2),
     ("nested-hole", "Rust inference holes", "fn Bad<'a>(value: u8) -> u8 where Unknown<(_, u8)>: 'a { value }", "_", 2),
     ("applied-generic", "takes no generic arguments", "fn Bad<'a, T>(value: u8) -> u8 where T<u8>: 'a { value }", "T", 1),
     ("applied-const-argument", "takes no generic arguments", "fn Bad<'a, const N: usize>(value: u8) -> u8 where Unknown<N<u8>>: 'a { value }", "N", 1),
     ("scoped-projection", "associated paths on scoped parameters", "fn Bad<'a, T>(value: u8) -> u8 where T::Item: 'a { value }", "T", 1),
     ("nested-scoped-projection", "associated paths on scoped parameters", "fn Bad<'a, T>(value: u8) -> u8 where Unknown<T::Item>: 'a { value }", "T", 1),
     ("associated-binding", "associated type bindings", "fn Bad<'a, T>(value: u8) -> u8 where Unknown<Item = T>: 'a { value }", "Item", 0),
     ("impl-trait", "impl Trait", "fn Bad<'a>(value: u8) -> u8 where impl Marker: 'a { value }", "impl Marker", 0)]
  fun check declared (label, expected, rust, token, occurrence) =
    let val text = command declared rust
      val callbacks = saved_callbacks ()
      val reporter = !Private_Output.report_fn
      val (result, events) = capture (fn () => failure label expected (fn () => run thy label text))
      val diagnostic = Exn.release result
      val _ = require (label ^ ": smallest positioned diagnostic changed")
        (map position_range (message_positions diagnostic) =
          [range_of text token occurrence, range_of text "urust_fn" 0])
      val _ = require (label ^ ": failed outlives leaked successful output/declaration reports")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = require (label ^ ": failure changed namespace, schemes or callbacks")
        (snapshot ctxt = old_names andalso scheme_snapshot ctxt = old_schemes andalso
          same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
      val (recovery, _) = capture (fn () => run thy (label ^ "-recovery")
        ("urust_fn [verbosity = 0] " ^ cartouche
          "fn OutlivesRecovery<'a: 'a>(value: u8) -> u8 where 'a: 'static { value }"))
      val completed = Exn.release recovery |> Toplevel.context_of
      val _ = require "outlives failure recovers with a checked ordinary declaration"
        (is_some (Parser_Test_Calls.lookup completed "OutlivesRecovery"))
      val _ = require_scope_closed label completed
    in () end
  val _ = List.app (check false) (structural @ shapes)
  val _ = List.app (check true) structural
  val _ = List.app (fn (label, _, rust, _, _) =>
    let val (result, _) = capture (fn () => run thy (label ^ "-declared") (command true rust))
    in require_scope_closed label (Exn.release result |> Toplevel.context_of) end) shapes
  val _ = List.app (fn (label, expected, rust) =>
    ignore (failure label expected (fn () => run thy label (command false rust))))
    [("mixed-concrete-trait", "where clauses may only bound", "fn Bad<'a>(value: u8) -> u8 where Unknown: 'a + Marker { value }"),
     ("mixed-callable-wrapper", "conditional-const trait bounds are not supported", "fn Bad<'a, T: 'a + [const] Fn(u8) -> u8>(value: u8) -> u8 { value }"),
     ("mixed-conditional-const", "conditional-const trait bounds are not supported", "fn Bad<'a, T: 'a + [const] Marker>(value: u8) -> u8 { value }"),
     ("mixed-higher-ranked", "higher-ranked trait bounds are not supported", "fn Bad<'a, T: 'a + for<'b> Fn(&'b u8)>(value: u8) -> u8 { value }"),
     ("mixed-generic-trait", "generic trait bounds are not supported", "fn Bad<'a, T: 'a + Unknown<u8>>(value: u8) -> u8 { value }"),
     ("wrapped-where-outlives", "higher-ranked where predicates are not supported", "fn Bad<T>(value: u8) -> u8 where for<'a> T: 'a { value }"),
     ("bound-local-leak", "undeclared lifetime", "fn Bad<T: for<'b> Unknown<&'b u8>>(value: u8) -> u8 where T: 'b { value }")]
  val body_type = "\<llangle>undefined :: 't\<rrangle>"
  val body_const = "\<llangle>undefined :: 'n itself\<rrangle>"
  val body_rows =
    [("source-only-call-shape", "no backend matches",
       "fn Body<'a, T>(value: u8) -> u8 where Unknown<T>: 'a { SignatureIdentity::<T>(value) }",
       "fn Body<T>(value: u8) -> u8 { SignatureIdentity::<T>(value) }"),
     ("source-only-body-type", "generic parameter T does not occur in the signature",
       "fn Body<'a, T>(value: u8) -> usize where Unknown<T>: 'a { let spare = " ^ body_type ^ "; 0 }",
       "fn Body<T>(value: u8) -> usize { let spare = " ^ body_type ^ "; 0 }"),
     ("source-only-body-const", "generic parameter N does not occur in the signature",
       "fn Body<'a, const N: usize>(value: u8) -> usize where [u8; N]: 'a { let spare = " ^ body_const ^ "; 0 }",
       "fn Body<const N: usize>(value: u8) -> usize { let spare = " ^ body_const ^ "; 0 }")]
  val _ = List.app (fn (label, expected, bounded, plain) =>
    List.app (fn rust =>
      let val (result, events) = capture (fn () =>
          failure label expected (fn () => run thy label (command false rust)))
        val _ = Exn.release result
      in require "plain and bounded body failures retain atomic output and unchanged registries"
        (null (ordinary events) andalso null (declaration_reports events) andalso
          snapshot ctxt = old_names andalso scheme_snapshot ctxt = old_schemes)
      end) [bounded, plain]) body_rows
  val _ = List.app (fn (label, expected, bounded, plain) =>
    List.app (fn rust => ignore (failure (label ^ "-declared") expected
      (fn () => run thy label (command true rust)))) [bounded, plain])
    (tl body_rows)
  val _ = writeln "S3 smallest-token authoritative/declared scope and shape failures, rich wrappers, body availability, rollback and recovery PASS"
in end
\<close>



chapter\<open> Canonical callable binding audits \<close>

ML\<open>
structure Callable_Signature_Test =
struct
  open Generic_Signature_Test
  structure Types = URust_Type_Mappings
  structure Traits = URust_Trait_Mappings
  fun scheme_entry ctxt name =
    Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction name
    |> filter (fn entry => is_some (Types.binding_generic_scheme_for_source ctxt (#serial entry)))
    |> the_single
  fun scheme ctxt name =
    let val entry = scheme_entry ctxt name
    in (#serial entry, the (Types.binding_generic_scheme_for_source ctxt (#serial entry))) end
  fun callable_bound ctxt label path =
    let val function = parse ctxt label
          ("fn Probe<F: " ^ path ^ "(bool) -> bool>(callback: F, value: bool) -> bool { callback(value) }")
    in case #parameters (URust_AST.function_generics function) of
        [URust_AST.Generic_Type (_, _, [bound])] => (function, bound)
      | _ => error "callable audit: malformed probe header" end
  fun recipe ctxt bound = case Traits.classify_bound ctxt bound of
      Traits.Callable_Bound recipe => recipe
    | _ => error "callable audit: bound lost registered classification"
  fun parameters function = map (fn URust_AST.Function_Parameter (_, _, typ, _) => typ
      | _ => error "callable audit: expected explicit formal type")
    (URust_AST.function_parameters function)
  fun scopes_closed label ctxt =
    require (label ^ ": canonical binding scope escaped") (is_none (Types.binding_scope ctxt))
end
\<close>

ML_val\<open>
local
  open Callable_Signature_Test
  val ctxt = \<^context>
  val variants = ["Fn", "FnMut", "FnOnce"]
  fun aliases variant = [variant, "core::ops::" ^ variant, "std::ops::" ^ variant]
  fun origins variant = map (fn path =>
    let val (_, bound) = callable_bound ctxt ("callable-identity-" ^ path) path
        val {origin, ...} = recipe ctxt bound
        val _ = require "callable alias lost its exact entry path" (#path origin = path)
        val _ = require "callable entity has no declaration provenance"
          (not (null (Position.properties_of (#declaration_pos origin))))
    in #identity origin end) (aliases variant)
  val identities = map origins variants
  val _ = require "each standard variant must share one canonical alias identity"
    (forall (fn ids => length (distinct (op =) ids) = 1) identities)
  val _ = require "three callable variants collapsed their registered identities"
    (length (distinct (op =) (map hd identities)) = 3)
  val _ = require "arbitrary suffix was registered as a standard callable"
    (is_none (Traits.lookup ctxt "custom::Fn") andalso is_none (Traits.lookup ctxt "other::ops::Fn"))
  val _ = List.app (fn path => ignore (failure ("callable-conflict-" ^ path)
    "conflicting mappings" (fn () => run \<^theory> "callable-classification-conflict"
      ("urust_trait " ^ quote path ^ " = " ^ cartouche "type")))) (maps aliases variants)
  val ordinary = run \<^theory> "callable-custom-ordinary"
    ("urust_trait \"custom::Fn\" = " ^ cartouche "type") |> Toplevel.context_of
  val (_, custom) = callable_bound ordinary "callable-custom-parenthesized" "custom::Fn"
  val _ = ignore (failure "callable-custom-classification" "no standard callable classification"
    (fn () => Traits.classify_bound ordinary custom))
  val _ = writeln "S4 nine trait keys / three real canonical entities, exact paths and classification conflicts PASS"
in end
\<close>

ML_val\<open>
local
  open Callable_Signature_Test
  val ctxt = \<^context>
  val (function, bound) = callable_bound ctxt "callable-owned-frame" "Fn"
  val reference_count = Unsynchronized.ref 0
  fun reference _ = reference_count := !reference_count + 1
  val [URust_AST.Generic_Type (_, pos, _)] = #parameters (URust_AST.function_generics function)
  val declaration = Types.fresh_generic_declaration_identity ()
  val parameter: Types.generic_parameter =
    {rust = "F", kind = URust_AST.Type_Parameter, pos = pos, hol = ("'f", \<^sort>\<open>type\<close>),
     bounds = [], report_reference = reference}
  val specification: Types.binding_spec =
    {parameter = parameter, declaration = declaration, callables = [recipe ctxt bound]}
  val pending = Types.prepare_binding_scope [specification] ctxt
  val _ = ignore (failure "callable-pending-receipts" "finalized Rust signature"
    (fn () => Types.binding_signature_events pending))
  val resolved = Types.resolve_function_signature_with_bindings (Types.with_binding_scope pending ctxt)
    {state = NONE, abort = NONE, input = NONE, output = NONE} [] (parameters function)
    (the (URust_AST.function_return_type function))
  val scope = #scope resolved
  val [binding] = Types.scope_bindings scope
  val owned = Types.with_binding_scope scope ctxt
  val relation = the (Types.binding_callable_relation binding)
  val template = the (Types.binding_template binding)
  val {state, abort, input, output} = #channels relation
  val _ = require "callable template lost the checked input/result/four-channel relation"
    (template = (map #1 (#inputs relation) ---> Type (\<^type_name>\<open>function_body\<close>,
      [state, #1 (#result relation), abort, input, output])))
  val _ = require "callable produced a fictitious independent F type variable"
    (not (member (op =) (map fst (Term.add_tfreesT template [])) "'f"))
  val _ = require "legacy generic getter lied about a structured scope"
    (is_none (Types.generic_scope owned))
  val final_events = Types.binding_event_declarations (Types.binding_signature_events scope)
  val _ = require "final signature scope lost its actual callable occurrence"
    (#source_uses final_events = [declaration] andalso #witness_uses final_events = [declaration])
  val (_, observed) = Types.capture_binding_events owned (fn outer =>
    let val (_, inner) = Types.capture_binding_events outer (fn inner =>
          Types.report_binding_reference inner binding {witness = true, pos = pos})
        val _ = require "nested canonical capture lost the installed record"
          (#witness_uses (Types.binding_event_declarations inner) = [declaration])
    in () end)
  val _ = require "canonical outer capture was gated by the partial legacy getter"
    (#witness_uses (Types.binding_event_declarations observed) = [declaration])
  val foreign_count = Unsynchronized.ref 0
  fun foreign_reference _ = foreign_count := !foreign_count + 1
  val foreign_parameter: Types.generic_parameter =
    {rust = "F", kind = URust_AST.Type_Parameter, pos = pos, hol = #hol parameter,
     bounds = [], report_reference = foreign_reference}
  val foreign_scope = Types.prepare_binding_scope
    [{parameter = foreign_parameter, declaration = declaration, callables = [recipe ctxt bound]}] ctxt
  val foreign = hd (Types.scope_bindings foreign_scope)
  val before = !reference_count
  val (_, rejected) = Types.capture_binding_events owned (fn observed =>
    (Types.report_binding_reference observed foreign {witness = true, pos = pos};
     Types.report_generic_reference observed foreign_parameter pos;
     Types.report_generic_source_reference observed foreign_parameter pos))
  val _ = require "foreign callback/unfinished record passed canonical membership"
    (!reference_count = before andalso !foreign_count = 0 andalso
      #source_uses (Types.binding_event_declarations rejected) = [])
  val source_only = Types.with_binding_availability
    {unavailable = [], source_only = [declaration], declared_body = false} owned
  val (_, source_events) = Types.capture_binding_events source_only (fn observed =>
    Types.report_binding_reference observed binding {witness = false, pos = pos})
  val masks = Types.binding_event_declarations source_events
  val _ = require "source-only callable demand manufactured a witness"
    (#source_uses masks = [declaration] andalso null (#witness_uses masks) andalso
      not (Types.binding_has_witness source_only binding))
  val _ = ignore (failure "callable-source-only-witness" "no available HOL witness" (fn () =>
    Types.report_binding_reference source_only binding {witness = true, pos = pos}))
  val (escaped, inactive) = Types.capture_binding_events owned I
  val _ = Types.report_binding_reference escaped binding {witness = true, pos = pos}
  val _ = require "completed canonical capture remained mutable through an escaped context"
    (null (#source_uses (Types.binding_event_declarations inactive)))
  val failed_observer = Unsynchronized.ref NONE
  val _ = ignore (failure "callable-capture-failure" "expected callable capture failure" (fn () =>
    Types.capture_binding_events owned (fn observed =>
      (failed_observer := SOME observed; error "expected callable capture failure"))))
  val _ = Types.report_binding_reference (the (!failed_observer)) binding {witness = true, pos = pos}
  val (_, recovered) = Types.capture_binding_events owned (fn observed =>
    Types.report_binding_reference observed binding {witness = false, pos = pos})
  val _ = require "failed canonical capture poisoned the next operation"
    (#source_uses (Types.binding_event_declarations recovered) = [declaration] andalso
      null (#witness_uses (Types.binding_event_declarations recovered)))
  val _ = writeln "S4 finalized whole binding/relation, strict callback identity, nested capture, masks and failure deactivation PASS"
in end
\<close>

ML_val\<open>
local
  open Callable_Signature_Test
  val thy = \<^theory>
  val ctxt = \<^context>
  val names_before = snapshot ctxt
  val schemes_before = scheme_snapshot ctxt
  val paths = ["Fn", "core::ops::Fn", "std::ops::Fn", "FnMut", "core::ops::FnMut",
    "std::ops::FnMut", "FnOnce", "core::ops::FnOnce", "std::ops::FnOnce"]
  fun accepted (index, path) =
    let val name = "CallableAccepted" ^ string_of_int index
        val text = "urust_fn " ^ cartouche
          ("fn " ^ name ^ "<T, F: " ^ path ^ "(T) -> T>(callback: F, value: T) -> T { callback(value) }")
        val completed = run thy name text |> Toplevel.context_of
        val (source, scheme) = scheme completed name
        val slots = Types.binding_scoped_parameters scheme
        val _ = require "ordered ordinary/callable source slots changed"
          (map #rust slots = ["T", "F"] andalso
            map #kind slots = [URust_AST.Type_Parameter, URust_AST.Type_Parameter])
        val _ = require "whole callable witness was shortened to an atomic slot"
          (is_some (#callable_relation (nth slots 1)) andalso
            (case #witness (nth slots 1) of SOME (Type ("fun", _)) => true | _ => false))
        val _ = require "old scheme getter silently dropped or fabricated F"
          (is_none (Types.generic_scheme_for_source completed source) andalso
            is_none (Types.generic_source_scheme_for_source completed source) andalso
            is_none (Types.scoped_generic_scheme_for_source completed source))
    in scopes_closed name completed end
  val _ = List.app accepted (map_index I paths)
  val accepted_rows =
    [("compatible-bounds", "fn CallableCompatible<T, F: Fn(T) -> T + FnMut(T) -> T + FnOnce(T) -> T>(callback: F, value: T) -> T { callback(value) }"),
     ("nested-dependencies", "fn CallableDependencies<T, G: Fn(T) -> T, F: Fn(G, T) -> T>(outer: F, inner: G, value: T) -> T { outer(inner, value) }"),
     ("zero-terminal", "fn CallableTerminal<F: FnOnce()>(callback: F) { callback() }"),
     ("call-count-abstraction", "fn CallableRepeated<F: FnOnce(bool) -> bool>(callback: F, value: bool) -> bool { callback(value); callback(value) }"),
     ("mutable-reference-input", "fn CallableReference<'a, F: Fn(&'a mut bool) -> bool>(callback: F, value: &'a mut bool) -> bool { callback(value) }")]
  val _ = List.app (fn (label, rust) => scopes_closed label
    (run thy label ("urust_fn " ^ cartouche rust) |> Toplevel.context_of)) accepted_rows
  val rejected_rows =
    [("rigid-declarations", "incompatible callable bounds", "fn CallableRigid<T, U, F: Fn(T) -> T + Fn(U) -> U>(callback: F, value: T) -> T { callback(value) }"),
     ("different-results", "incompatible callable bounds", "fn CallableResults<F: Fn(bool) -> bool + Fn(bool) -> u8>(callback: F) -> bool { false }"),
     ("self-cycle", "recursive callable dependency", "fn CallableRecursive<F: Fn(F) -> bool>(callback: F) -> bool { false }"),
     ("mutual-cycle", "recursive callable dependency", "fn CallableMutual<F: Fn(G) -> bool, G: Fn(F) -> bool>(callback: F) -> bool { false }"),
     ("body-only", "does not occur in the signature", "fn CallableBodyOnly<F: Fn(bool) -> bool>() { let value = " ^ "\<llangle>undefined :: 'f\<rrangle>" ^ "; () }"),
     ("recipe-only-ordinary", "does not occur in the signature", "fn CallableRecipeOnly<T, F: Fn(T) -> T>(callback: F) { let value = " ^ "\<llangle>undefined :: 't\<rrangle>" ^ "; () }"),
     ("whole-sort", "does not satisfy", "fn CallableSort<F: Fn(bool) -> bool>(callback: " ^ "\<tau>" ^ cartouche "'f::len0" ^ ") -> bool { callback(false) }"),
     ("shared-reference-limit", "shared", "fn CallableShared<F: Fn(&bool) -> bool>(callback: F) -> bool { false }"),
     ("custom-suffix", "unregistered callable trait", "fn CallableCustom<F: custom::Fn(bool) -> bool>(callback: F) -> bool { false }"),
     ("higher-ranked-limit", "higher-ranked trait bounds", "fn CallableHigher<F: for<'a> Fn(&'a bool) -> bool>(callback: F) -> bool { false }"),
     ("conditional-const-limit", "conditional-const trait bounds", "fn CallableConst<F: [const] Fn(bool) -> bool>(callback: F) -> bool { false }")]
  val _ = List.app (fn (label, expected, rust) =>
    let val callbacks = saved_callbacks ()
        val reporter = !Private_Output.report_fn
        val (result, events) = capture (fn () => failure label expected
          (fn () => run thy label ("urust_fn " ^ cartouche rust)))
        val _ = Exn.release result
        val _ = require "failed callable header/body leaked declarations or ordinary output"
          (null (declaration_reports events) andalso null (ordinary events))
        val _ = require "failed callable operation changed registries or callback ownership"
          (snapshot ctxt = names_before andalso scheme_snapshot ctxt = schemes_before andalso
            same_callbacks callbacks andalso PolyML.pointerEq (reporter, !Private_Output.report_fn))
    in scopes_closed label (run thy (label ^ "-recovery") ("urust_fn " ^ cartouche
      "fn CallableRecovery(value: bool) -> bool { value }") |> Toplevel.context_of) end) rejected_rows
  val _ = writeln "S4 callable aliases, zero/multiple inputs, rigid dependencies/cycles, body availability, sort limits and atomic recovery PASS"
in end
\<close>


section\<open> Candidate-owned erased callable evidence \<close>

ML_val\<open>
local
  open Callable_Signature_Test
  val thy = \<^theory>
  val options = "[state = " ^ cartouche "nat" ^ ", abort = " ^ cartouche "unit" ^
    ", input = " ^ cartouche "unit" ^ ", output = " ^ cartouche "unit" ^ "] "
  fun function rust = "urust_fn " ^ options ^ cartouche rust ^ "\n"
  val prefix =
    "urust_type [erase = " ^ cartouche "'callback" ^ "] \"CallableErased<'callback>\" = " ^ cartouche "unit" ^ "\n" ^
    "urust_type [erase = " ^ cartouche "'element, 'callback" ^ "] \"CallableErasedPair<'element, 'callback>\" = " ^ cartouche "unit" ^ "\n" ^
    "urust_type [erase = " ^ cartouche "'element, 'capacity, 'callback" ^
      "] \"CallableErasedArray<'element, const 'capacity, 'callback>\" = " ^ cartouche "unit" ^ "\n" ^
    "urust_type \"BoolStateCallable\" = " ^ cartouche "bool => (bool, bool, unit, unit, unit) function_body" ^ "\n" ^
    "urust_type \"NatStateCallable\" = " ^ cartouche "bool => (nat, bool, unit, unit, unit) function_body" ^ "\n" ^
    "urust_type \"NatArrayThreeCallable\" = " ^
      cartouche "(bool, 3) array => (nat, bool, unit, unit, unit) function_body" ^ "\n" ^
    "urust_type [implicit = " ^ cartouche "address = 'address" ^ "] \"UnfixedCallableState\" = " ^
      cartouche "bool => ('address, bool, unit, unit, unit) function_body" ^ "\n" ^
    function "fn ErasedCallable<F: Fn(bool) -> bool>(tag: CallableErased<F>) -> bool { false }" ^
    function "fn ErasedCallablePair<T, F: Fn(T) -> T>(tag: CallableErasedPair<T, F>) -> bool { false }" ^
    function "fn ErasedCallableArray<T, const N: usize, F: Fn([T; N]) -> T>(tag: CallableErasedArray<T, N, F>) -> bool { false }" ^
    function "fn UnrelatedErasedTag<Tag, F: Fn(bool) -> bool>(tag: CallableErased<Tag>, callback: F) -> bool { callback(false) }"
  val initialized = run thy "callable-erased-evidence-prefix" prefix
  val model = Toplevel.context_of initialized
  val (_, erased_scheme) = scheme model "ErasedCallable"
  val [erased_slot] = Types.binding_scoped_parameters erased_scheme
  val _ = require "erased callable registration changed its execution availability"
    (is_none (#witness erased_slot) andalso is_some (#callable_relation erased_slot) andalso
      #source_used erased_slot = SOME true)
  fun client label expected rust =
    let
      val result = Exn.capture0 (fn () => Parser_Trait_Test.run_from initialized label (function rust)) ()
      val _ = case expected of NONE => scopes_closed label (Exn.release result |> Toplevel.context_of)
        | SOME message => ignore (failure label message (fn () => Exn.release result))
      val (_, scheme_after) = scheme model "ErasedCallable"
    in require "candidate comparison manufactured an erased witness or mutated its entry"
      (map #witness (Types.binding_scoped_parameters scheme_after) = [NONE]) end
  val _ = List.app (fn (label, expected, rust) => client label expected rust)
    [("erased-nat-state-accept", NONE,
       "fn ErasedNatClient(tag: CallableErased<NatStateCallable>) -> bool { ErasedCallable::<NatStateCallable>(tag) }"),
     ("erased-bool-state-reject", SOME "no backend matches",
       "fn ErasedBoolClient(tag: CallableErased<BoolStateCallable>) -> bool { ErasedCallable::<BoolStateCallable>(tag) }"),
     ("erased-shared-ordinary-accept", NONE,
       "fn ErasedPairClient(tag: CallableErasedPair<bool, NatStateCallable>) -> bool { ErasedCallablePair::<bool, NatStateCallable>(tag) }"),
     ("erased-shared-ordinary-reject", SOME "no backend matches",
       "fn ErasedPairMismatch(tag: CallableErasedPair<u8, NatStateCallable>) -> bool { ErasedCallablePair::<u8, NatStateCallable>(tag) }"),
     ("erased-length-accept", NONE,
       "fn ErasedArrayClient(tag: CallableErasedArray<bool, 3, NatArrayThreeCallable>) -> bool { ErasedCallableArray::<bool, 3, NatArrayThreeCallable>(tag) }"),
     ("erased-length-reject", SOME "no backend matches",
       "fn ErasedArrayMismatch(tag: CallableErasedArray<bool, 4, NatArrayThreeCallable>) -> bool { ErasedCallableArray::<bool, 4, NatArrayThreeCallable>(tag) }"),
     ("erased-ordinary-opaque-reject", SOME "no checked denotation",
       "fn ErasedOpaqueOrdinary(tag: CallableErasedPair<unmapped::Tag, NatStateCallable>) -> bool { ErasedCallablePair::<unmapped::Tag, NatStateCallable>(tag) }"),
     ("erased-callable-opaque-reject", SOME "no checked denotation",
       "fn ErasedOpaqueCallable(tag: CallableErased<unmapped::Tag>) -> bool { ErasedCallable::<unmapped::Tag>(tag) }"),
     ("erased-role-evidence-rigid", SOME "unavailable implicit backend role",
       "fn ErasedRigidRole(tag: CallableErased<UnfixedCallableState>) -> bool { ErasedCallable::<UnfixedCallableState>(tag) }"),
     ("unrelated-erased-opaque-accept", NONE,
       "fn ErasedUnrelated<F: Fn(bool) -> bool>(tag: CallableErased<unmapped::Tag>, callback: F) -> bool { UnrelatedErasedTag::<unmapped::Tag, F>(tag, callback) }"),
     ("erased-inference-reject", SOME "erased generic arguments require explicit",
       "fn ErasedUnspecified(tag: CallableErased<NatStateCallable>) -> bool { ErasedCallable(tag) }")]
  val _ = scopes_closed "standalone callable inference" (run thy "callable-free-inferred"
    (function "fn CallableInferenceBase<F: Fn(bool) -> bool>(callback: F, value: bool) -> bool { callback(value) }" ^
     function "fn CallableInferenceClient<F: Fn(bool) -> bool>(callback: F, value: bool) -> bool { CallableInferenceBase(callback, value) }")
    |> Toplevel.context_of)
  val holes = "urust_fn [state = " ^ cartouche "_" ^ ", abort = " ^ cartouche "unit" ^
      ", input = " ^ cartouche "unit" ^ ", output = " ^ cartouche "unit" ^ "] " ^ cartouche
      "fn CallableAuthoredHole<F: Fn(bool) -> bool>(callback: F, value: bool) -> bool { callback(value) }"
  val _ = scopes_closed "authored channel hole" (run thy "callable-genuine-authored-hole" holes |> Toplevel.context_of)
  val _ = writeln "S4 one native candidate environment, erased source templates/kinds/lengths, opaque and role boundaries, masks and ordinary inference PASS"
in end
\<close>

end
