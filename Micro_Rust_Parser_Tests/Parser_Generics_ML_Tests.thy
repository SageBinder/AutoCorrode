(* ML audits for trait mappings and generic function items.
   The readable examples are in Parser_Generics_Examples. *)

theory Parser_Generics_ML_Tests
  imports
    Parser_Generics_Examples
    Parser_Test_Fixtures_Left
    Parser_Test_Fixtures_Right
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

chapter\<open> Syntax \<close>

text\<open> Reserved for U2 generic syntax audits. \<close>

chapter\<open> Signatures \<close>

text\<open> Reserved for U3 generic signature audits. \<close>

chapter\<open> Bodies \<close>

text\<open> Reserved for U4 generic body audits. \<close>

chapter\<open> Turbofish \<close>

text\<open> Reserved for U4 generic call audits. \<close>

end
