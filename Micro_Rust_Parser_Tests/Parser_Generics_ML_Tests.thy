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

  fun capture action =
    let
      val reports = Synchronized.var "trait_test_reports" ([]: string list)
      val output = Synchronized.var "trait_test_output" ([]: string list)
      fun collect target chunks = Synchronized.change target (append chunks)
      val result = Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn (collect reports) (fn () =>
          Unsynchronized.setmp Private_Output.writeln_fn (collect output) (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE] (fn () => Exn.capture action ()) ()) ()) ())
      val chunks = Synchronized.value reports
      val markup = fold Parser_Test_Reports.collect_markup (maps YXML.parse_body chunks) []
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
      val _ = require (label ^ ": failure emitted trait definition reports")
        (not (exists (fn (name, props) => name = Markup.entityN andalso
          Properties.get props Markup.kindN = SOME "urust_trait" andalso
          is_some (Properties.get props Markup.defN)) (#markup observed)))
      val _ = require (label ^ ": failure printed successful output") (#output observed = "")
      val _ = require (label ^ ": original theory changed")
        (Context.eq_thy (thy, Toplevel.theory_of base))
      val after = mapping (context base) "Scale"
      val _ = require (label ^ ": existing mapping changed")
        (#sort original = #sort after andalso #constants original = #constants after)
      val _ = require (label ^ ": failing declaration changed its registry")
        (forall (fn (key, entry) => Traits.lookup (context base) key = entry) original_entries)
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
