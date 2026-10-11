(* Rust use imports as members of urust chunks: the composition of Parser_Chunk_Tests and
   Parser_Use_Tests. Internal audits reuse the support structures of both feature theories. *)

theory Parser_Chunk_Use_Tests
  imports
    Parser_Chunk_Regression_Tests
    Parser_Use_Fixtures
begin

declare [[urust_pp_test = true, urust_pretty = false, urust_verbosity = 0]]

chapter\<open> Imports in source-ordered chunks \<close>

text\<open>
A \<open>urust\<close> chunk may contain complete \<open>use\<close> items with the grammar of \<open>urust_use\<close>. The
imports of one chunk form one batch: it is validated before the first declaration, its aliases are
visible to every declaration of the chunk, including declarations written before the \<open>use\<close>
item, and no alias survives the command. Every declaration elaborates with the batch prepared for
its own member context, so a target that the chunk declares is available only to the members after
it. After the last declaration every target must resolve. Every generated definition below is
compared by kernel reflexivity with a fully qualified single-item control.
\<close>

section\<open> Aliases visible to earlier and later members \<close>

urust \<open>
  fn ChunkImportEarly(x: u32) -> u32 { step(x) }

  use demo::{increment as step, value as fetch, WIDTH as Width_Value};

  fn ChunkImportLate() -> u32 { step(fetch()) + Width_Value }
\<close>

urust_fn \<open> fn ChunkImportEarlyControl(x: u32) -> u32 { demo::increment(x) } \<close>
urust_fn \<open> fn ChunkImportLateControl() -> u32 { demo::increment(demo::value()) + demo::WIDTH } \<close>

lemma \<open> chunk_import_early = chunk_import_early_control \<close>
  unfolding chunk_import_early_def chunk_import_early_control_def by (rule refl)
lemma \<open> chunk_import_late = chunk_import_late_control \<close>
  unfolding chunk_import_late_def chunk_import_late_control_def by (rule refl)

section\<open> Importing an item declared earlier in the same chunk \<close>

text\<open>
A member declared by the chunk can be imported; the alias resolves for the members after that
declaration. The rejections in the audit section show the same alias unavailable before it.
\<close>

urust \<open>
  fn ChunkImportHelper(x: u32) -> u32 { x + 1 }

  use ChunkImportHelper as helper;

  fn ChunkImportCaller(x: u32) -> u32 { helper(helper(x)) }
\<close>

urust_fn \<open>
  fn ChunkImportCallerControl(x: u32) -> u32 { ChunkImportHelper(ChunkImportHelper(x)) }
\<close>

lemma \<open> chunk_import_caller = chunk_import_caller_control \<close>
  unfolding chunk_import_caller_def chunk_import_caller_control_def by (rule refl)

section\<open> Shadowing among persistent, chunk and body imports \<close>

text\<open>
A chunk alias shadows a persistent \<open>urust_use\<close> alias inside the chunk; a body import shadows the
chunk alias throughout its block, including before the body import, and only there. After the
command the persistent alias is visible again.
\<close>

urust_use \<open> use demo::value as chunk_import_pick; \<close>

urust \<open>
  fn ChunkImportShadowed(x: u32) -> u32 { chunk_import_pick(x) }

  fn ChunkImportBodyShadow() -> u32 {
    let outer = chunk_import_pick(1);
    let inner = { let early = chunk_import_pick(2); use use_increment as chunk_import_pick; early };
    outer + inner + chunk_import_pick(3)
  }

  use demo::increment as chunk_import_pick;
\<close>

urust_fn \<open> fn ChunkImportShadowedControl(x: u32) -> u32 { demo::increment(x) } \<close>
urust_fn \<open>
  fn ChunkImportBodyShadowControl() -> u32 {
    let outer = demo::increment(1);
    let inner = { let early = use_increment(2); early };
    outer + inner + demo::increment(3)
  }
\<close>

lemma \<open> chunk_import_shadowed = chunk_import_shadowed_control \<close>
  unfolding chunk_import_shadowed_def chunk_import_shadowed_control_def by (rule refl)
lemma \<open> chunk_import_body_shadow = chunk_import_body_shadow_control \<close>
  unfolding chunk_import_body_shadow_def chunk_import_body_shadow_control_def by (rule refl)

urust_expr chunk_import_persistent_again \<open> chunk_import_pick() \<close>
urust_expr chunk_import_persistent_again_control \<open> demo::value() \<close>

lemma \<open> chunk_import_persistent_again = chunk_import_persistent_again_control \<close>
  unfolding chunk_import_persistent_again_def chunk_import_persistent_again_control_def
  by (rule refl)

section\<open> Same-spelling type and value aliases \<close>

urust \<open>
  use {UsePacket as ChunkImportPair, demo::value as ChunkImportPair};

  fn ChunkImportSpelling(packet: ChunkImportPair) -> u32 { ChunkImportPair() + packet.sample }
\<close>

urust_fn \<open>
  fn ChunkImportSpellingControl(packet: UsePacket) -> u32 { demo::value() + packet.sample }
\<close>

lemma \<open> chunk_import_spelling = chunk_import_spelling_control \<close>
  unfolding chunk_import_spelling_def chunk_import_spelling_control_def by (rule refl)

section\<open> Signatures, fields, calls, construction and patterns \<close>

urust \<open>
  struct ChunkImportHolder { choice: Choice, word: Word, tuple: Tuple1 }

  fn ChunkImportBuild(n: u32) -> ChunkImportHolder {
    ChunkImportHolder { choice: Present(n), word: n, tuple: Tuple1(n) }
  }

  use UseChoice::{self as Choice, Value as Present, Empty as Absent};
  use {UseTuple as Tuple1, demo::Width as Word};

  fn ChunkImportInspect(holder: ChunkImportHolder, fallback: Word) -> u32 {
    match holder.choice {
      Present(n) => n,
      Absent => fallback,
      Choice::Named { sample } => sample,
    }
  }

  fn ChunkImportUnwrap(tuple: Tuple1) -> u32 {
    match tuple { Tuple1(n) => n }
  }
\<close>

urust_datatype \<open>
  struct ChunkImportHolderControl { choice: UseChoice, word: demo::Width, tuple: UseTuple }
\<close>
urust_fn \<open>
  fn ChunkImportBuildControl(n: u32) -> ChunkImportHolder {
    ChunkImportHolder { choice: UseChoice::Value(n), word: n, tuple: UseTuple(n) }
  }
\<close>
urust_fn \<open>
  fn ChunkImportInspectControl(holder: ChunkImportHolder, fallback: demo::Width) -> u32 {
    match holder.choice {
      UseChoice::Value(n) => n,
      UseChoice::Empty => fallback,
      UseChoice::Named { sample } => sample,
    }
  }
\<close>
urust_fn \<open> fn ChunkImportUnwrapControl(tuple: UseTuple) -> u32 { match tuple { UseTuple(n) => n } } \<close>

lemma \<open> chunk_import_build = chunk_import_build_control \<close>
  unfolding chunk_import_build_def chunk_import_build_control_def by (rule refl)
lemma \<open> chunk_import_inspect = chunk_import_inspect_control \<close>
  unfolding chunk_import_inspect_def chunk_import_inspect_control_def by (rule refl)
lemma \<open> chunk_import_unwrap = chunk_import_unwrap_control \<close>
  unfolding chunk_import_unwrap_def chunk_import_unwrap_control_def by (rule refl)

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun selector_type name = fastype_of (Syntax.read_term ctxt name) |> range_type
in
  val _ = require "chunk alias field types"
    (map selector_type
       ["chunk_import_holder_choice", "chunk_import_holder_word", "chunk_import_holder_tuple"] =
     map selector_type
       ["chunk_import_holder_control_choice", "chunk_import_holder_control_word",
        "chunk_import_holder_control_tuple"])
end
\<close>

section\<open> Imports in a locale target \<close>

locale chunk_import_locale =
  fixes chunk_import_param :: nat
begin

urust \<open>
  use demo::increment as local_step;
  fn ChunkImportLocal(x: u32) -> u32 { local_step(x) }
\<close>

urust_fn \<open> fn ChunkImportLocalControl(x: u32) -> u32 { demo::increment(x) } \<close>

lemma \<open> chunk_import_local = chunk_import_local_control \<close>
  unfolding chunk_import_local_def chunk_import_local_control_def by (rule refl)

end

section\<open> Alias absence after the command \<close>

text\<open> An import-only chunk validates and resolves its imports and declares nothing. \<close>

urust \<open> use demo::{value as only_value, increment}; \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val aliases =
    ["step", "fetch", "Width_Value", "helper", "ChunkImportPair", "Choice", "Present",
     "Absent", "Tuple1", "Word", "local_step", "only_value", "increment"]
in
  val _ = require "no block frame survives a chunk" (S.frame_depth ctxt = 0)
  val _ = require "no chunk alias survives its chunk"
    (forall (fn alias =>
        is_none (S.lookup ctxt S.Type_Namespace alias) andalso
        is_none (S.lookup ctxt S.Value_Namespace alias)) aliases)
  val _ = require "the persistent alias shadowed by a chunk alias is unchanged"
    (lookup_key ctxt S.Value_Namespace "chunk_import_pick" = SOME "demo::value")
  val _ = require "chunk aliases are not persistent bindings"
    (forall (fn binding => not (member (op =) aliases (#alias binding))) (S.dump_persistent ctxt))
  (* A later command reads the former alias as an unresolved HOL name. *)
  val later =
    Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source "step(fetch())")
  val _ = require "a later command does not resolve a chunk alias"
    (forall (fn alias => exists_subterm (fn Free (name, _) => name = alias | _ => false) later)
      ["step", "fetch"])
end
\<close>

section\<open> Audits \<close>

text\<open>
Command-level audits run synthetic theory text in a private toplevel state with the support of
\<^ML_structure>\<open>Chunk_Test\<close>; their positions carry symbol offsets and a synthetic identity.
\<close>

urust_use \<open> use demo::value as chunk_import_fallback; \<close>

ML\<open>
structure Chunk_Use_Audit =
struct
  open Chunk_Test
  val quiet = quiet_prefix ""
  val loud = "declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2]]\n"
  fun chunk body = "urust " ^ command_source body

  (* A rejected chunk: the diagnostic, its first range and the captured command effects. *)
  fun rejected label expected text =
    let
      val {result, output, warnings, reports} = capture true label \<^theory> text
      val message = failure_message label expected result
    in {message = message, output = output, warnings = warnings, reports = reports} end

  fun rejects label expected body = #message (rejected label expected (quiet ^ chunk body))

  (* The diagnostic is positioned at the nth occurrence of needle in the command text. *)
  fun rejects_at label expected body needle occurrence =
    let
      val text = quiet ^ chunk body
      val message = #message (rejected label expected text)
    in
      require (label ^ " positioned at " ^ quote needle ^ ": " ^ plain message)
        (message_range message = range_of text needle occurrence)
    end

  fun import_entities reports =
    report_events reports
    |> filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_import")

  fun run_success label text =
    let val {result, output, warnings, reports} = capture true label \<^theory> text
    in {ctxt = result_context result, output = output, warnings = warnings, reports = reports} end
end
\<close>

subsection\<open> Targets declared later or never \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
in
  (* The alias is unavailable before its target is declared and does not fall back to the
     persistent alias of the same name. *)
  val _ = rejects_at "later target"
    ["import target \"ChunkImportSecond\" of \"chunk_import_fallback\" is not yet available"]
    ("  fn ChunkImportFirst() -> u32 { chunk_import_fallback() }\n" ^
     "  use ChunkImportSecond as chunk_import_fallback;\n" ^
     "  fn ChunkImportSecond() -> u32 { 2 }\n")
    "chunk_import_fallback" 0
  val _ = rejects_at "member declared after its user"
    ["import target \"ChunkImportHelperTwo\" of \"helper_two\" is not yet available"]
    ("  fn ChunkImportTooEarly(x: u32) -> u32 { helper_two(x) }\n" ^
     "  fn ChunkImportHelperTwo(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportHelperTwo as helper_two;\n")
    "helper_two" 0
  val _ = rejects_at "member importing itself"
    ["import target \"ChunkImportItself\" of \"itself\" is not yet available"]
    ("  fn ChunkImportItself(x: u32) -> u32 { itself(x) }\n" ^
     "  use ChunkImportItself as itself;\n")
    "itself" 0
  val _ = rejects_at "later datatype field type"
    ["import target \"ChunkImportLaterStruct\" of \"LaterType\" is not yet available"]
    ("  struct ChunkImportEarlyField { field: LaterType }\n" ^
     "  use ChunkImportLaterStruct as LaterType;\n" ^
     "  struct ChunkImportLaterStruct { value: u32 }\n")
    "LaterType" 0
  val _ = rejects_at "later signature type"
    ["import target \"ChunkImportLaterSignature\" of \"LaterSignature\" is not yet available"]
    ("  fn ChunkImportEarlySignature(value: LaterSignature) -> u32 { 1 }\n" ^
     "  use ChunkImportLaterSignature as LaterSignature;\n" ^
     "  struct ChunkImportLaterSignature { value: u32 }\n")
    "LaterSignature" 0
  val _ = rejects_at "body import depending on a later target"
    ["import target \"ChunkImportLaterBody\" of \"later_body\" is not yet available"]
    ("  fn ChunkImportBodyEarly() -> u32 { use later_body as inner_body; inner_body() }\n" ^
     "  use ChunkImportLaterBody as later_body;\n" ^
     "  fn ChunkImportLaterBody() -> u32 { 3 }\n")
    "later_body" 0
  val _ = rejects_at "never-declared target"
    ["unknown import target \"ChunkImportNever\""]
    ("  fn ChunkImportOrphanUser() -> u32 { 1 }\n" ^
     "  use ChunkImportNever as never;\n")
    "ChunkImportNever" 0
end
\<close>

text\<open> Reordered, the chunk whose first member was rejected above succeeds. \<close>

urust \<open>
  fn ChunkImportSecond() -> u32 { 2 }

  use ChunkImportSecond as chunk_import_fallback;

  fn ChunkImportFirst() -> u32 { chunk_import_fallback() }
\<close>

urust_fn \<open> fn ChunkImportFirstControl() -> u32 { ChunkImportSecond() } \<close>

lemma \<open> chunk_import_first = chunk_import_first_control \<close>
  unfolding chunk_import_first_def chunk_import_first_control_def by (rule refl)

subsection\<open> Validation before the first declaration \<close>

text\<open>
Each chunk below starts with a member whose body fails typing. The import diagnostic is reported
instead, because the batch is validated, and prepared for the first member, before that member is
declared.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  val _ = rejects_at "duplicate import" ["duplicate import \"value\""]
    (broken ^ "  use demo::value;\n  use demo::value;\n") "value" 1
  val _ = rejects "cyclic imports" ["cyclic imports"]
    (broken ^ "  use chunk_left as chunk_right;\n  use chunk_right as chunk_left;\n")
  val _ = rejects_at "duplicate value import" ["duplicate value import \"dup\""]
    (broken ^ "  use demo::value as dup;\n  use UseTuple as dup;\n") "dup" 1
  val _ = rejects "unusable target" ["field notation \"sample\""]
    (broken ^ "  use sample;\n")
  val _ = rejects_at "glob import" ["glob imports (`*`) are not supported"]
    (broken ^ "  use demo::*;\n") "*" 0
  val _ = rejects_at "visibility" ["visibility qualifiers (`pub use`) are not supported"]
    (broken ^ "  pub use demo::value;\n") "pub" 0
  val _ = rejects_at "rooted path" ["`crate`"]
    (broken ^ "  use crate::value;\n") "crate" 0
  val _ =
    let
      val body = broken ^ "  " ^ annotation "pretty" ^ "\n  use demo::value;\n"
      val text = quiet ^ chunk body
      val message =
        #message (rejected "annotated use" ["an \<omega> annotation cannot precede a use item"] text)
      val (start, _) = range_of text omega 0
      val (_, stop) = range_of text (Symbol.close ^ "\n  use") 0
    in
      require ("annotated use positioned at the annotation: " ^ plain message)
        (message_range message = (start, stop - 6))
    end
end
\<close>

subsection\<open> Imports and items of one chunk \<close>

text\<open>
An import and an item that the same chunk declares cannot share a name in one namespace, in
either order, as in a Rust module. Distinct namespaces may share a spelling, and an item declared
before the chunk may be shadowed inside it.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val value_clash =
    ["value import \"ChunkImportClash\" collides with the same-scope generated Rust function"]
in
  val _ = rejects_at "import before item" value_clash
    ("  use demo::value as ChunkImportClash;\n  fn ChunkImportClash() -> u32 { 1 }\n")
    "ChunkImportClash" 0
  val _ = rejects_at "import after item" value_clash
    ("  fn ChunkImportClash() -> u32 { 1 }\n  use demo::value as ChunkImportClash;\n")
    "ChunkImportClash" 1
  val _ = rejects_at "type import and struct"
    ["type import \"ChunkImportClashType\" collides with the same-scope generated Rust item"]
    ("  use UsePacket as ChunkImportClashType;\n  struct ChunkImportClashType { value: u32 }\n")
    "ChunkImportClashType" 0
  val _ = rejects_at "value import and unit struct"
    ["value import \"ChunkImportClashUnit\" collides with the same-scope generated Rust constructor"]
    ("  struct ChunkImportClashUnit;\n  use demo::value as ChunkImportClashUnit;\n")
    "ChunkImportClashUnit" 1
end
\<close>

urust \<open>
  use demo::value as ChunkImportNamed;

  struct ChunkImportNamed { sample: u32 }

  fn ChunkImportNamedUse(packet: ChunkImportNamed) -> u32 { ChunkImportNamed() + packet.sample }
\<close>

urust \<open>
  use demo::value as ChunkImportHelper;

  fn ChunkImportOuterShadow() -> u32 { ChunkImportHelper() }
\<close>

urust_fn \<open>
  fn ChunkImportNamedUseControl(packet: ChunkImportNamed) -> u32 { demo::value() + packet.sample }
\<close>
urust_fn \<open> fn ChunkImportOuterShadowControl() -> u32 { demo::value() } \<close>

lemma \<open> chunk_import_named_use = chunk_import_named_use_control \<close>
  unfolding chunk_import_named_use_def chunk_import_named_use_control_def by (rule refl)
lemma \<open> chunk_import_outer_shadow = chunk_import_outer_shadow_control \<close>
  unfolding chunk_import_outer_shadow_def chunk_import_outer_shadow_control_def by (rule refl)

subsection\<open> Whole-command atomicity \<close>

text\<open>
A failure anywhere in a chunk with imports, including the final target check, leaves no
declaration, registry entry, import binding, semantic report, warning or successful output, in
theory, locale and nested context targets. The same names are then available to a successful
chunk.
\<close>

ML\<open>
structure Chunk_Use_Atomicity =
struct
  open Chunk_Use_Audit
  val earlier =
    "  use demo::{increment as atomic_step, value as atomic_fetch};\n" ^
    "  use UseChoice::{self as AtomicChoiceAlias, Value as AtomicPresent};\n" ^
    "  struct ChunkImportAtomicRecord { value: u32, choice: AtomicChoiceAlias }\n" ^
    "  fn ChunkImportAtomicFirst(record: ChunkImportAtomicRecord) -> u32 {\n" ^
    "    match record.choice { AtomicPresent(n) => atomic_step(n), _ => atomic_fetch() }\n" ^
    "  }\n" ^
    "  use ChunkImportAtomicFirst as atomic_first;\n" ^
    "  fn ChunkImportAtomicSecond(record: ChunkImportAtomicRecord) -> u32 {\n" ^
    "    atomic_first(record) + record.value\n" ^
    "  }\n"
  val failures =
    [("typing", "  fn ChunkImportAtomicBroken() -> bool { atomic_step(1) }\n",
       ["no backend matches the use-site type"]),
     ("unavailable",
       "  fn ChunkImportAtomicEarly() -> u32 { atomic_later() }\n" ^
       "  use ChunkImportAtomicLater as atomic_later;\n" ^
       "  fn ChunkImportAtomicLater() -> u32 { 1 }\n",
       ["is not yet available"]),
     ("never-declared", "  use ChunkImportAtomicNever as atomic_never;\n",
       ["unknown import target \"ChunkImportAtomicNever\""]),
     ("collision",
       "  use demo::value as ChunkImportAtomicClash;\n" ^
       "  fn ChunkImportAtomicClash() -> u32 { 1 }\n",
       ["collides with the same-scope generated Rust function"]),
     ("body-import",
       "  fn ChunkImportAtomicBody() -> u32 { use ChunkImportAtomicMissing as missing; missing() }\n",
       ["unknown import target \"ChunkImportAtomicMissing\""]),
     ("datatype-field",
       "  struct ChunkImportAtomicField { field: AtomicLaterType }\n" ^
       "  use ChunkImportAtomicLaterStruct as AtomicLaterType;\n" ^
       "  struct ChunkImportAtomicLaterStruct { value: u32 }\n",
       ["is not yet available"])]

  fun failing_case target wrap (label, failing, expected) =
    let
      val label = "chunk-import-atomic-" ^ target ^ "-" ^ label
      val text = loud ^ wrap (chunk (earlier ^ failing))
      val {output, warnings, reports, ...} = rejected label expected text
      val chunk_output =
        filter_out (String.isPrefix "locale chunk_import_atomic_loc") (authored_output output)
      val _ =
        require ("failed " ^ label ^ " chunk printed successful output:\n" ^ cat_lines chunk_output)
          (null chunk_output)
      val command_start = #1 (range_of text "urust " 0)
      fun after_start events = filter (fn event => #1 (report_range event) >= command_start) events
      val _ =
        require ("failed " ^ label ^ " chunk replayed semantic reports")
          (null (after_start (semantic_entities reports)) andalso
            null (after_start (import_entities reports)))
      val _ =
        require ("failed " ^ label ^ " chunk emitted warnings:\n" ^ cat_lines warnings)
          (null warnings)
      val failing_start = #1 (range_of text failing 0)
      fun key_start key =
        (case space_explode "|" key of
           _ :: _ :: start :: _ => the_default 0 (Int.fromString start)
         | _ => 0)
      val leaked =
        non_lexical_reports label \<^theory> text command_start reports
        |> filter (fn key => key_start key < failing_start)
      val _ =
        require ("failed " ^ label ^ " chunk left non-lexical reports of earlier members:\n" ^
            cat_lines leaked)
          (null leaked)
    in () end

  fun in_locale body =
    "locale chunk_import_atomic_loc =\n  fixes atomic_param :: nat\nbegin\n" ^ body ^ "\nend\n"
  fun in_context body =
    "context\n  fixes atomic_fixed :: nat\nbegin\n" ^ body ^ "\nend\n"

  val functions = ["ChunkImportAtomicFirst", "ChunkImportAtomicSecond"]
  fun declared ctxt =
    {functions = filter (is_some o URust_Item_Scope.lookup_function ctxt) functions,
     types =
       filter (is_some o URust_Item_Scope.lookup_type ctxt)
         ["ChunkImportAtomicRecord", "ChunkImportAtomicLater", "ChunkImportAtomicLaterStruct"],
     constants = filter (const_declared ctxt) ["chunk_import_atomic_first"],
     registries = registry_snapshot ctxt,
     persistent = URust_Import_Scope.dump_persistent ctxt,
     frames = URust_Import_Scope.frame_depth ctxt}
end
\<close>

ML\<open>
local
  open Chunk_Use_Atomicity
  val _ = List.app (failing_case "theory" I) failures
  val base = declared (Proof_Context.init_global \<^theory>)
  val _ = require "atomicity fixtures already exist"
    (null (#functions base) andalso null (#types base) andalso null (#constants base))
  (* Each failing chunk in one document sequence leaves the state unchanged; the corrected chunk
     then declares the same names. *)
  val sequence =
    loud ^
    implode (map (fn (_, failing, _) => chunk (earlier ^ failing) ^ "\n") failures) ^
    chunk earlier
  val transitions =
    Outer_Syntax.parse_text \<^theory> (K \<^theory>) (start_position "chunk-import-sequence") sequence
  fun step transition (state, failed) =
    (case Exn.result (Toplevel.command_exception true transition) state of
       Exn.Res state' => (state', failed)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else (state, failed @ [declared (Toplevel.context_of state)]))
  val (final_state, failed) =
    Parser_Test_Report_Lock.run (fn () =>
      Unsynchronized.setmp Private_Output.writeln_fn (K ()) (fn () =>
        Unsynchronized.setmp Private_Output.warning_fn (K ()) (fn () =>
          Unsynchronized.setmp Private_Output.report_fn (K ()) (fn () =>
            fold step transitions (Toplevel.make_state (SOME \<^theory>), [])) ()) ()) ())
  val after_declare = declared (Proof_Context.init_global \<^theory>)
  val _ = require "every failing chunk was rejected" (length failed = length failures)
  val _ = require "a failed chunk changed declarations, registries or import bindings"
    (forall (fn state => state = after_declare) failed)
  val final = declared (Toplevel.context_of final_state)
  val _ = require "the corrected chunk did not reuse the names of the failed chunks"
    (#functions final = functions andalso
      #types final = ["ChunkImportAtomicRecord"] andalso
      #constants final = ["chunk_import_atomic_first"] andalso
      #persistent final = #persistent after_declare andalso #frames final = 0)
in
  val _ = writeln "failing chunks with imports leave no declarations, bindings, reports or output"
end
\<close>

ML\<open>
  List.app (Chunk_Use_Atomicity.failing_case "locale" Chunk_Use_Atomicity.in_locale)
    Chunk_Use_Atomicity.failures
\<close>

ML\<open>
  List.app (Chunk_Use_Atomicity.failing_case "context" Chunk_Use_Atomicity.in_context)
    Chunk_Use_Atomicity.failures
\<close>

subsection\<open> Navigation \<close>

text\<open>
Each alias of a chunk is reported once, at its use item, with its tooltip and target references.
Every occurrence in any member keeps its backend navigation and ends at that import declaration,
exactly as an occurrence of a persistent alias in a single-item declaration does.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val text =
    quiet ^
    chunk
      ("  fn ChunkImportNavEarly(x: u32) -> u32 { nav_step(x) }\n" ^
       "  use demo::increment as nav_step;\n" ^
       "  fn ChunkImportNavLate(x: u32) -> u32 { nav_step(nav_step(x)) }\n") ^
    "\nurust_use " ^ cartouche " use demo::increment as nav_control; " ^
    "\nurust_fn " ^ cartouche " fn ChunkImportNavControl(x: u32) -> u32 { nav_control(x) } "
  val {reports, warnings, ...} = run_success "chunk-import-navigation" text
  val events = report_events reports
  fun at range = filter (fn event => report_range event = range) events
  fun import_at range =
    filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_import")
      (at range)
  val alias = range_of text "nav_step" 1
  val definitions =
    filter (fn (_, properties) => is_some (Properties.get properties Markup.defN)) (import_at alias)
  val _ = require "one import definition at the chunk alias" (length definitions = 1)
  val identity = the (Properties.get (#2 (hd definitions)) Markup.defN)
  val _ = require "one alias tooltip"
    (length (filter (fn (name, _) => name = Markup.typingN) (at alias)) = 1)
  val _ = require "one target reference at the use path"
    (length (filter (fn (name, _) => name = Markup.entityN)
      (at (range_of text "increment" 0))) = 1)
  fun ends_at_import occurrence =
    let
      val range = range_of text "nav_step" occurrence
      val kinds = entity_kinds_at range reports
      val references =
        map (fn (_, properties) => Properties.get properties Markup.refN) (import_at range)
    in
      require ("occurrence " ^ string_of_int occurrence ^ " ends at the import: " ^ commas kinds)
        (try List.last kinds = SOME "urust_import" andalso references = [SOME identity] andalso
          kinds = entity_kinds_at (range_of text "nav_control" 1) reports)
    end
  val _ = List.app ends_at_import [0, 2, 3]
  val _ = require "navigation emitted warnings" (null warnings)
in
  val _ = ()
end
\<close>

subsection\<open> Printing, roundtrips and read-only pretty replay \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val ctxt = \<^context>
  val text =
    "fn ChunkImportPrintEarly(x: u32) -> u32 { print_step(x) }\n" ^
    "use demo::{increment as print_step, value};\n" ^
    "struct ChunkImportPrintPacket { sample: u32 }\n" ^
    "use {UsePacket as PrintPacket};\n" ^
    "fn ChunkImportPrintLate(packet: PrintPacket) -> u32 { print_step(packet.sample) }\n"
  val parsed = the_chunk ctxt "chunk-import-print" text
  fun kind (URust_AST.Use_Item_Node _) = "use"
    | kind (URust_AST.Function_Item_Node _) = "fn"
    | kind _ = "datatype"
  val kinds = map (kind o URust_AST.annotated_item_item) (URust_AST.chunk_items parsed)
  val _ = require "use members keep their source order" (kinds = ["fn", "use", "datatype", "use", "fn"])
  val printed = URust_Printer.string_of_chunk URust_Printer.serialized_options parsed
  val reparsed = the_chunk ctxt "chunk-import-reprint" printed
  val _ = require "serialized chunk roundtrip with use members"
    (URust_Printer.tokens_of_chunk URust_Printer.serialized_options parsed =
      URust_Printer.tokens_of_chunk URust_Printer.serialized_options reparsed)
  fun index needle = raw_index printed needle 0
  val _ = require "printed members in source order"
    (index "ChunkImportPrintEarly" < index "use demo" andalso
      index "use demo" < index "ChunkImportPrintPacket" andalso
      index "ChunkImportPrintPacket" < index "PrintPacket}" andalso
      index "PrintPacket}" < index "ChunkImportPrintLate")

  (* Pretty replay of members that use chunk aliases resolves them as their declarations did
     and is read-only. *)
  val body =
    "  use demo::increment as pretty_step;\n" ^
    "  struct ChunkImportPrettyHolder { choice: PrettyChoice }\n" ^
    "  use UseChoice as PrettyChoice;\n" ^
    "  fn ChunkImportPretty(x: u32) -> u32 { pretty_step(x) }\n"
  val pretty = run_success "chunk-import-pretty" ("urust [pretty, verbosity = 2, pp_test] " ^
    command_source body)
  val plain_run = run_success "chunk-import-plain" ("urust [verbosity = 2] " ^ command_source body)
  val _ = require ("pretty output shows the aliases:\n" ^ cat_lines (authored_output (#output pretty)))
    (exists (String.isSubstring "pretty_step(x)") (authored_output (#output pretty)) andalso
      exists (String.isSubstring "choice: PrettyChoice") (authored_output (#output pretty)))
  val _ = require "pretty replay is read-only"
    (registry_snapshot (#ctxt pretty) = registry_snapshot (#ctxt plain_run) andalso
      URust_Import_Scope.dump_persistent (#ctxt pretty) =
        URust_Import_Scope.dump_persistent (#ctxt plain_run))
in
  val _ = ()
end
\<close>

subsection\<open> Complete input \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val ctxt = \<^context>
  fun parse_rejects label expected text =
    ignore (expect_failure label expected (fn () => parse ctxt label text))
in
  val _ = parse_rejects "missing semicolon" ["syntax error"] "use demo::value"
  val _ = parse_rejects "trailing input after a use member" ["syntax error"]
    "use demo::value; 1"
  val _ = parse_rejects "dangling use keyword" ["syntax error"] "fn A() -> u32 { 1 }\nuse"
  val _ = parse_rejects "path prefix before use" ["unexpected `value` before a use item"]
    "fn A() -> u32 { 1 }\nvalue use demo::value;"
  val _ = require "an import-only chunk parses"
    (length (URust_AST.chunk_items (the_chunk ctxt "import-only" "use demo::value;")) = 1)
end
\<close>

end
