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
Generic headers parse and print before signature elaboration. Type and const parameters currently
reach the temporary guard in both signature modes; these audits preserve the delivered lifetime,
receiver, datatype and retained literal-type behavior until signature support removes that guard.
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
    (map #1 (#where_clause (function_generics projected)) = ["U", "T", "T"])
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
     ("lifetime-inline-bound", "lifetime bounds are not supported", "fn Bad<'a, T: 'a>() {}", "'a", 1),
     ("lifetime-inline-plus-bound", "lifetime bounds are not supported", "fn Bad<'a, T: Marker + 'a>() {}", "'a", 1),
     ("lifetime-where-bound", "lifetime bounds are not supported", "fn Bad<'a, T>() where T: 'a {}", "'a", 1),
     ("fn-inline-bound", "Fn trait bounds are not supported", "fn Bad<T: Fn(u8) -> u8>() {}", "(", 0),
     ("fn-where-bound", "Fn trait bounds are not supported", "fn Bad<T>() where T: Fn(u8) -> u8 {}", "(", 1),
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
  val _ = List.app (rejects ctxt) tests
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

section\<open> Temporary guards and delivered compatibility \<close>

ML_val\<open>
local
  open Generic_Syntax_Test
  val thy = @{theory}
  val hol_type = "nat => ('s, nat, 'abort, 'i, 'o) function_body"
  fun declaration declared item =
    "urust_fn [pp_test, verbosity = 0] generic_syntax_failure " ^
    (if declared then ":: " ^ cartouche hol_type ^ " " else "") ^ cartouche item
  fun guard (label, declared, item, token) =
    let
      val text = declaration declared item
      val (message, events) = reports (fn () => failure label
        "urust_fn: type generics are not supported" (fn () => run thy label text))
      val positions = map position_range (message_positions message)
      val _ = require (label ^ ": stub did not identify first non-lifetime parameter")
        (not (null positions) andalso hd positions = range_of text token 0)
      val _ = require (label ^ ": premature declaration markup")
        (not (exists (fn (name, _, props) => name = Markup.entityN andalso
          is_some (Properties.get props Markup.defN)) events))
      val recovered = run thy (label ^ "-recovery")
        (declaration false "fn Generic(value: u8) -> u8 { value }") |> Toplevel.context_of
      val _ = require (label ^ ": command did not recover")
        (is_some (Parser_Test_Calls.lookup recovered "Generic"))
    in () end
  val _ = List.app guard
    [("guard-inferred-type", false, "fn Generic<T>(x: T) -> T { x }", "T"),
     ("guard-declared-type", true, "fn Generic<T>(value: impl Marker) -> impl Marker { value }", "T"),
     ("guard-inferred-const", false, "fn Sized<const N: usize>(value: [u8; N]) -> usize { 0 }", "N"),
     ("guard-declared-const", true, "fn Sized<const N: usize>(value: Unknown) -> Unknown { value }", "N"),
     ("guard-inferred-mixed", false, "fn Mix<'a, const N: usize, T>(value: T) -> T { value }", "N"),
     ("guard-declared-mixed", true, "fn Mix<'a, T, const N: usize>(value: Unknown) -> Unknown { value }", "T"),
     ("legacy-reference-mixed-generics", false, "fn BadReference<'a, T>(value: &'a mut u8) -> u8 { 0 }", "T")]
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
    let val text = "urust [pp_test, verbosity = 0] " ^ cartouche item
        val diagnostic = failure label "urust_fn: type generics are not supported"
          (fn () => run model label text)
    in require (label ^ ": chunk/member stub range")
      (hd (map position_range (message_positions diagnostic)) = range_of text token 0) end) chunks
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
and nested targets retain each original setting. Generic guards remain temporary until U3;
the malformed nongeneric body supplies an independent durable failure and recovery control.
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
  val member = "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { value } }"

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
    [("member-type-guard", holder ^ "\nimpl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }",
       "urust_fn: type generics are not supported"),
     ("free-const-guard", holder ^ "\nfn sized<const N: usize>(value: [u8; N]) -> usize { 0 }",
       "urust_fn: type generics are not supported"),
     ("nongeneric-body", holder ^ "\nimpl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
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
        run_with true configured (label ^ "-recovery") (command verbosity (holder ^ "\n" ^ member)))
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
  fun guard declared verbosity =
    let
      val label = "complete-output-signature-guard-" ^ Bool.toString declared ^ "-" ^ string_of_int verbosity
      val body = "fn SyntaxOutputGeneric<T>(value: T) -> T { value }"
      val text = "urust_fn [verbosity = " ^ string_of_int verbosity ^ "] syntax_output_guard " ^
        (if declared then ":: " ^ cartouche "nat => ('s, nat, 'abort, 'i, 'o) function_body" ^ " "
         else "") ^ cartouche body
      val (result, events) = capture (fn () => run_with true thy label text)
      val diagnostic =
        (case result of Exn.Res _ => error (label ^ ": unexpectedly accepted")
         | Exn.Exn exn => Runtime.exn_message exn)
      val _ = require (label ^ ": wrong temporary generic diagnostic")
        (String.isSubstring "urust_fn: type generics are not supported" diagnostic)
      val _ = require (label ^ ": complete output or definition reports escaped")
        (null (ordinary events) andalso null (declaration_reports events))
      val _ = exact_binders label text [] events
      val _ = require (label ^ ": first non-lifetime declaration range changed")
        (hd (map position_range (message_positions diagnostic)) = range_of text "T" 0)
    in () end
  val _ = List.app (fn verbosity => List.app (fn declared => guard declared verbosity) [false, true])
    [0, 1, 2]
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
    [("member-type-guard", "impl SyntaxOutputHolder { fn member<T>(self, value: T) -> T { value } }",
       "urust_fn: type generics are not supported", []),
     ("nongeneric-body", "impl SyntaxOutputHolder { fn member(self, value: u8) -> u8 { missing_output_value } }",
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

text\<open> Reserved for U3 generic signature audits. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body audits. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call audits. \<close>

end
