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

text\<open>
As for Rust module-level imports, member parameters shadow chunk and persistent aliases, while a
body import shadows the parameters of its member. The controls use unimported parameter names.
\<close>

urust \<open>
  use demo::increment as chunk_shadow_pick;
  fn ChunkShadowParameter(chunk_shadow_pick: u32) -> u32 { chunk_shadow_pick }
  fn ChunkShadowBody(chunk_shadow_pick: u32) -> u32 {
    use use_increment as chunk_shadow_pick;
    chunk_shadow_pick(1)
  }
  fn ChunkShadowPersistent(chunk_import_pick: u32) -> u32 { chunk_import_pick }
  // A parameter also wins against a chunk alias whose target is declared later.
  fn ChunkShadowUnavailable(chunk_shadow_later: u32) -> u32 { chunk_shadow_later }
  use ChunkShadowLater as chunk_shadow_later;
  fn ChunkShadowLater(value: u32) -> u32 { value }
\<close>

urust_fn \<open> fn ChunkShadowParameterControl(other: u32) -> u32 { other } \<close>
urust_fn \<open> fn ChunkShadowBodyControl(other: u32) -> u32 { use_increment(1) } \<close>

lemma \<open> chunk_shadow_parameter = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_parameter_def chunk_shadow_parameter_control_def by (rule refl)
lemma \<open> chunk_shadow_body = chunk_shadow_body_control \<close>
  unfolding chunk_shadow_body_def chunk_shadow_body_control_def by (rule refl)
lemma \<open> chunk_shadow_persistent = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_persistent_def chunk_shadow_parameter_control_def by (rule refl)
lemma \<open> chunk_shadow_unavailable = chunk_shadow_parameter_control \<close>
  unfolding chunk_shadow_unavailable_def chunk_shadow_parameter_control_def by (rule refl)

text\<open>
A body binding that is unavailable in the value namespace, because its chunk alias names a value
declared later, never rejects when a local bound inside its block shadows it; a local bound at the
member level wins through an unrelated body import frame.
\<close>

urust_type "ChunkShadowPending" = \<open> nat \<close>

urust \<open>
  use ChunkShadowPending as chunk_shadow_pending;
  use demo::increment as chunk_shadow_pick;
  fn ChunkShadowPendingUser(x: u32) -> u32 {
    use chunk_shadow_pending as chunk_shadow_inner;
    let chunk_shadow_inner = x;
    chunk_shadow_inner
  }
  fn ChunkShadowPending(value: u32) -> u32 { value }
  fn ChunkShadowThrough(x: u32) -> u32 {
    let chunk_shadow_pick = x;
    { use demo::value as chunk_shadow_unrelated; chunk_shadow_pick }
  }
\<close>

urust_fn \<open> fn ChunkShadowLocalControl(x: u32) -> u32 { let y = x; y } \<close>
urust_fn \<open> fn ChunkShadowThroughControl(x: u32) -> u32 { let y = x; { y } } \<close>

lemma \<open> chunk_shadow_pending_user = chunk_shadow_local_control \<close>
  unfolding chunk_shadow_pending_user_def chunk_shadow_local_control_def by (rule refl)
lemma \<open> chunk_shadow_through = chunk_shadow_through_control \<close>
  unfolding chunk_shadow_through_def chunk_shadow_through_control_def by (rule refl)

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

  (* A rejected chunk run in the given theory: the diagnostic and the captured command effects.
     Callers pass the theory of their own position, so later fixtures are visible. *)
  fun rejected thy label expected text =
    let
      val {result, output, warnings, reports} = capture true label thy text
      val message = failure_message label expected result
    in {message = message, output = output, warnings = warnings, reports = reports} end

  fun rejects thy label expected body = #message (rejected thy label expected (quiet ^ chunk body))

  (* The diagnostic is positioned at the nth occurrence of needle in the command text. *)
  fun rejects_at thy label expected body needle occurrence =
    let
      val text = quiet ^ chunk body
      val message = #message (rejected thy label expected text)
    in
      require (label ^ " positioned at " ^ quote needle ^ ": " ^ plain message)
        (message_range message = range_of text needle occurrence)
    end

  fun import_entities reports =
    report_events reports
    |> filter (fn (name, properties) =>
        name = Markup.entityN andalso Properties.get properties Markup.kindN = SOME "urust_import")

  fun run_success thy label text =
    let val {result, output, warnings, reports} = capture true label thy text
    in {ctxt = result_context result, output = output, warnings = warnings, reports = reports} end
end
\<close>

subsection\<open> Targets declared later or never \<close>

urust_type "ChunkShadowSplit" = \<open> nat \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
in
  (* The alias is unavailable before its target is declared and does not fall back to the
     persistent alias of the same name. *)
  val _ = rejects_at \<^theory> "later target"
    ["import target \"ChunkImportSecond\" of \"chunk_import_fallback\" is not yet available"]
    ("  fn ChunkImportFirst() -> u32 { chunk_import_fallback() }\n" ^
     "  use ChunkImportSecond as chunk_import_fallback;\n" ^
     "  fn ChunkImportSecond() -> u32 { 2 }\n")
    "chunk_import_fallback" 0
  val _ = rejects_at \<^theory> "member declared after its user"
    ["import target \"ChunkImportHelperTwo\" of \"helper_two\" is not yet available"]
    ("  fn ChunkImportTooEarly(x: u32) -> u32 { helper_two(x) }\n" ^
     "  fn ChunkImportHelperTwo(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportHelperTwo as helper_two;\n")
    "helper_two" 0
  val _ = rejects_at \<^theory> "member importing itself"
    ["import target \"ChunkImportItself\" of \"itself\" is not yet available"]
    ("  fn ChunkImportItself(x: u32) -> u32 { itself(x) }\n" ^
     "  use ChunkImportItself as itself;\n")
    "itself" 0
  val _ = rejects_at \<^theory> "later datatype field type"
    ["import target \"ChunkImportLaterStruct\" of \"LaterType\" is not yet available"]
    ("  struct ChunkImportEarlyField { field: LaterType }\n" ^
     "  use ChunkImportLaterStruct as LaterType;\n" ^
     "  struct ChunkImportLaterStruct { value: u32 }\n")
    "LaterType" 0
  val _ = rejects_at \<^theory> "later signature type"
    ["import target \"ChunkImportLaterSignature\" of \"LaterSignature\" is not yet available"]
    ("  fn ChunkImportEarlySignature(value: LaterSignature) -> u32 { 1 }\n" ^
     "  use ChunkImportLaterSignature as LaterSignature;\n" ^
     "  struct ChunkImportLaterSignature { value: u32 }\n")
    "LaterSignature" 0
  (* A body import of a chunk alias whose value is declared later shadows a same-named parameter in
     the value namespace and rejects without falling back to the parameter. *)
  val _ = rejects_at \<^theory> "body import shadowing a parameter"
    ["is not yet available"]
    ("  use ChunkShadowSplit as chunk_shadow_split;\n" ^
     "  fn ChunkShadowSplitUser(chunk_split_param: u32) -> u32 {\n" ^
     "    use chunk_shadow_split as chunk_split_param;\n" ^
     "    chunk_split_param(1)\n" ^
     "  }\n" ^
     "  fn ChunkShadowSplit(value: u32) -> u32 { value }\n")
    "chunk_split_param" 2
  val _ = rejects_at \<^theory> "body import depending on a later target"
    ["import target \"ChunkImportLaterBody\" of \"later_body\" is not yet available"]
    ("  fn ChunkImportBodyEarly() -> u32 { use later_body as inner_body; inner_body() }\n" ^
     "  use ChunkImportLaterBody as later_body;\n" ^
     "  fn ChunkImportLaterBody() -> u32 { 3 }\n")
    "later_body" 0
  val _ = rejects_at \<^theory> "never-declared target"
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
  val _ = rejects_at \<^theory> "duplicate import" ["duplicate import \"value\""]
    (broken ^ "  use demo::value;\n  use demo::value;\n") "value" 1
  val _ = rejects \<^theory> "cyclic imports" ["cyclic imports"]
    (broken ^ "  use chunk_left as chunk_right;\n  use chunk_right as chunk_left;\n")
  val _ = rejects_at \<^theory> "duplicate value import" ["duplicate value import \"dup\""]
    (broken ^ "  use demo::value as dup;\n  use UseTuple as dup;\n") "dup" 1
  val _ = rejects \<^theory> "unusable target" ["field notation \"sample\""]
    (broken ^ "  use sample;\n")
  val _ = rejects_at \<^theory> "glob import" ["glob imports (`*`) are not supported"]
    (broken ^ "  use demo::*;\n") "*" 0
  val _ = rejects_at \<^theory> "visibility" ["visibility qualifiers (`pub use`) are not supported"]
    (broken ^ "  pub use demo::value;\n") "pub" 0
  val _ = rejects_at \<^theory> "rooted path" ["`crate`"]
    (broken ^ "  use crate::value;\n") "crate" 0
  val _ =
    let
      val body = broken ^ "  " ^ annotation "pretty" ^ "\n  use demo::value;\n"
      val text = quiet ^ chunk body
      val message =
        #message (rejected \<^theory> "annotated use" ["an \<omega> annotation cannot precede a use item"] text)
      val (start, _) = range_of text omega 0
      val (_, stop) = range_of text (Symbol.close ^ "\n  use") 0
    in
      require ("annotated use positioned at the annotation: " ^ plain message)
        (message_range message = (start, stop - 6))
    end
end
\<close>

subsection\<open> Namespace-precise forward targets \<close>

text\<open>
Each declaration's preparation knows the registry entities that it and the later members will
declare, as their declaration backends report them from the decisions they declare with:
datatype types and mappings, constructors and enum variants, the conversion call notations of the
native \<open>simple_word_enum\<close> backend under its plugin filter, and the call keys of registered
functions. An entity among them is unavailable in its own namespace only; an entity that already
exists keeps resolving, and a target that neither exists nor is declared with a Rust registration
is unknown at its path before the first declaration.
\<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  val lthy = Named_Target.theory_init \<^theory>
  (* Members with every backend and plugin choice that changes registrations. *)
  val members =
    [("ChunkPredReprEight", "verbosity = 0",
       "#[repr(u8)]\n  enum ChunkPredReprEight { Low = 1, High = 4 }"),
     ("ChunkPredReprSixteen", "verbosity = 0",
       "#[repr(u16)]\n  enum ChunkPredReprSixteen { Low, High }"),
     ("ChunkPredWord", "backend = \"simple_word_enum\", word_width = 16",
       "enum ChunkPredWord { Low = 1, High = 2 }"),
     ("ChunkPredWordOnly",
       "backend = \"simple_word_enum\", word_width = 16, plugins = (plugins only: word_conversion)",
       "enum ChunkPredWordOnly { Low = 1, High = 2 }"),
     ("ChunkPredReprDel", "plugins = (plugins del: urust_conversion)",
       "#[repr(u8)]\n  enum ChunkPredReprDel { Low = 1, High = 2 }"),
     ("ChunkPredReprEnum", "backend = \"enum\"",
       "#[repr(u8)]\n  enum ChunkPredReprEnum { Low = 1, High = 2 }"),
     ("ChunkPredReprHidden", "register_notation = false",
       "#[repr(u8)]\n  enum ChunkPredReprHidden { Low = 1, High = 2 }"),
     ("ChunkPredHol", "backend = hol",
       "enum ChunkPredHol { Empty, Value(u32), Named { sample: u32 } }"),
     ("ChunkPredChoice", "verbosity = 0",
       "enum ChunkPredChoice { Empty, Value(u32), Named { sample: u32 } }"),
     ("ChunkPredPacket", "verbosity = 0", "struct ChunkPredPacket { sample: u32 }"),
     ("ChunkPredTuple", "verbosity = 0", "struct ChunkPredTuple(u32);"),
     ("ChunkPredUnit", "verbosity = 0", "struct ChunkPredUnit;"),
     ("ChunkPredWrapper", "verbosity = 0", "struct ChunkPredWrapper<T> { inner: T }"),
     ("ChunkPredEmpty", "verbosity = 0", "struct ChunkPredEmpty {}"),
     ("ChunkPredFn", "verbosity = 0", "fn ChunkPredFn(x: u32) -> u32 { x + 1 }"),
     ("ChunkPredHiddenFn", "register_notation = false",
       "fn ChunkPredHiddenFn(x: u32) -> u32 { x }"),
     ("ChunkPredAnonFn", "name = _", "fn ChunkPredAnonFn(x: u32) -> u32 { x }")]
  fun member_text (_, payload, item) = annotation payload ^ "\n  " ^ item ^ "\n"
  val declared =
    #ctxt (run_success \<^theory> "chunk-prediction"
      (quiet ^ chunk (implode (map (fn member => "  " ^ member_text member) members))))
  (* The prediction a chunk makes before declaring the member, in the enclosing context. *)
  fun prediction member =
    let
      val envelope =
        hd (URust_AST.chunk_items (the_chunk lthy "chunk-prediction-member" (member_text member)))
      val annotation = the (URust_AST.annotated_item_annotation envelope)
      val source = URust_AST.annotated_item_source envelope
      fun read schema = URust_Command.read_annotation_options lthy schema annotation
      val registrations =
        (case URust_AST.annotated_item_item envelope of
           URust_AST.Function_Item_Node function =>
             URust_Command.prepared_function_registrations
               (URust_Command.prepare_function_item lthy
                 {interactive = false, roundtrip = false,
                  options = read URust_Command.Function_Annotation,
                  source = source, function = function})
         | URust_AST.Datatype_Item item =>
             URust_Command.prepared_datatype_registrations lthy
               (URust_Command.prepare_datatype_item lthy
                 {interactive = false, roundtrip = false,
                  options = read URust_Command.Datatype_Annotation, source = source, item = item})
         | _ => error "chunk prediction audit: unexpected member")
    in URust_Imports.registration_entities registrations end
  (* Every registry entry that declaring the member added under its Rust name. *)
  fun observed name =
    let
      val {notations, types, constructors, functions, mappings} = registry_snapshot declared
      fun own key = key = name orelse String.isPrefix (name ^ "::") key
      val keys =
        distinct (op =)
          (filter own (map #2 notations @ types @ constructors @ functions @ mappings))
    in
      maps (URust_Imports.registration_entities o URust_Imports.installed_registrations declared)
        keys
    end
  fun triple ({key, namespace, roles}: URust_Imports.entity) = (key, namespace, roles)
  fun render entities =
    commas (map (fn (key, namespace, roles) =>
      key ^ "/" ^ URust_Import_Scope.namespace_name namespace ^ "/" ^
        space_implode "+" (map URust_Import_Scope.role_name roles)) entities)
  fun check (member as (name, _, _)) =
    let
      val predicted = map triple (prediction member)
      val actual = map triple (observed name)
    in
      require ("predicted registrations of " ^ name ^ ": " ^ render predicted ^
          "\nactual registrations: " ^ render actual)
        (eq_set (op =) (predicted, actual))
    end
  val _ = List.app check members
  fun predicts member key = exists (fn entity => #key entity = key) (prediction member)
  val _ = require "repr enums predict their conversion calls"
    (predicts (nth members 0) "ChunkPredReprEight::to_u8" andalso
      predicts (nth members 0) "ChunkPredReprEight::try_from" andalso
      predicts (nth members 1) "ChunkPredReprSixteen::to_u16" andalso
      predicts (nth members 2) "ChunkPredWord::to_u16" andalso
      predicts (nth members 6) "ChunkPredReprHidden::to_u8")
  val _ = require "plugin filters and other backends predict no conversion call"
    (not (predicts (nth members 3) "ChunkPredWordOnly::to_u16") andalso
      not (predicts (nth members 4) "ChunkPredReprDel::to_u8") andalso
      not (predicts (nth members 5) "ChunkPredReprEnum::to_u8"))
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val type_ns = S.Type_Namespace
  val value_ns = S.Value_Namespace
  val later =
    URust_Imports.Declared_Later
      [{key = "LaterItem", namespace = value_ns, roles = [S.Generated_Function]},
       {key = "UseChoice", namespace = value_ns, roles = [S.Generated_Function]},
       {key = "LaterEnum", namespace = type_ns, roles = [S.Generated_Enum, S.Mapped_Type]},
       {key = "LaterEnum::Ready", namespace = type_ns, roles = [S.Enum_Variant]},
       {key = "LaterEnum::Ready", namespace = value_ns, roles = [S.Generated_Constructor]}]
  val partial =
    prepare_with later ctxt
      [leaf ["LaterItem"] (SOME "later"), leaf ["UseChoice"] (SOME "both"),
       leaf ["later"] (SOME "dependent"), leaf ["LaterEnum"] (SOME "Enum"),
       leaf ["Enum", "Ready"] (SOME "ready"), group ["LaterEnum"] [self_member (SOME "Grouped")]]
  fun availability alias namespace = Option.map #available (S.lookup partial namespace alias)
  val _ = require "a later value entity is unavailable in the value namespace only"
    (availability "later" value_ns = SOME false andalso availability "later" type_ns = NONE andalso
      availability "dependent" value_ns = SOME false andalso
      availability "dependent" type_ns = NONE)
  val _ = require "an existing entity keeps resolving beside a later one"
    (lookup_roles partial type_ns "both" = SOME [S.Generated_Enum, S.Mapped_Type] andalso
      availability "both" value_ns = SOME false)
  val _ = require "a later enum qualifies exactly its declared variants"
    (availability "Enum" type_ns = SOME false andalso
      availability "Grouped" type_ns = SOME false andalso
      availability "ready" type_ns = SOME false andalso availability "ready" value_ns = SOME false)
  val _ = rejects "a variant the later enum does not declare" "\"Missing\" is not a variant of enum"
    (fn () => prepare_with later ctxt
      [leaf ["LaterEnum"] (SOME "Enum"), leaf ["Enum", "Missing"] (SOME "missing")])
  val _ = rejects "a target neither existing nor declared" "unknown import target \"NeverItem\""
    (fn () => prepare_with later ctxt [leaf ["NeverItem"] (SOME "never")])
in
  val _ = ()
end
\<close>

urust_datatype \<open> enum ChunkImportFE { A } \<close>
urust_use \<open> use demo::value as ChunkImportFBoth; \<close>
urust_type "ChunkImportFT" = \<open> nat \<close>
urust_use \<open> use demo::value as ChunkImportFT2; \<close>
urust_datatype \<open> enum ChunkImportFG { A } \<close>
urust_fn \<open> fn ChunkImportFG2() -> u32 { 3 } \<close>
urust_datatype \<open> enum ChunkImportFN { A } \<close>

ML_val\<open>
local
  open Chunk_Use_Audit
  fun later_value label target alias =
    rejects_at \<^theory> label
      ["import target " ^ quote target ^ " of " ^ quote alias ^ " is not yet available"]
      ("  fn " ^ target ^ "Early() -> u32 { " ^ alias ^ "() }\n" ^
       "  use " ^ target ^ " as " ^ alias ^ ";\n" ^
       "  fn " ^ target ^ "() -> u32 { 7 }\n" ^
       "  fn " ^ target ^ "Late() -> u32 { " ^ alias ^ "() }\n")
      alias 0
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  (* The target's type entity exists; its value entity is declared later. The earlier value use
     neither falls back to a persistent alias or an outer item of the alias spelling nor reads an
     unresolved name. *)
  val _ = later_value "enum with a later function, persistent fallback"
    "ChunkImportFE" "ChunkImportFBoth"
  val _ = later_value "type mapping with a later function, persistent fallback"
    "ChunkImportFT" "ChunkImportFT2"
  val _ = later_value "enum with a later function, outer item fallback"
    "ChunkImportFG" "ChunkImportFG2"
  val _ = later_value "enum with a later function, no fallback" "ChunkImportFN" "ChunkImportFNAlias"
  (* Targets without a Rust registration are unknown at their path, before the first declaration. *)
  val _ = rejects_at \<^theory> "unregistered function target" ["unknown import target \"ChunkImportHidden\""]
    (broken ^ "  " ^ annotation "register_notation = false" ^ "\n" ^
     "  fn ChunkImportHidden(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportHidden as hidden;\n" ^
     "  fn ChunkImportHiddenUser() -> u32 { hidden(1) }\n")
    "ChunkImportHidden" 1
  val _ = rejects_at \<^theory> "anonymous function target" ["unknown import target \"ChunkImportAnonymous\""]
    (broken ^ "  " ^ annotation "name = _" ^ "\n" ^
     "  fn ChunkImportAnonymous(x: u32) -> u32 { x }\n" ^
     "  use ChunkImportAnonymous as anonymous;\n" ^
     "  fn ChunkImportAnonymousUser() -> u32 { anonymous(1) }\n")
    "ChunkImportAnonymous" 1
  val _ = rejects_at \<^theory> "never-declared target used by an earlier member"
    ["unknown import target \"ChunkImportNeverDeclared\""]
    (broken ^ "  fn ChunkImportNeverUser() -> u32 { never_declared(1) }\n" ^
     "  use ChunkImportNeverDeclared as never_declared;\n")
    "ChunkImportNeverDeclared" 0
  val _ = rejects_at \<^theory> "missing variant of a later enum"
    ["unknown import target \"ChunkImportLaterEnum::Missing\""]
    (broken ^ "  use ChunkImportLaterEnum::Missing as missing_variant;\n" ^
     "  enum ChunkImportLaterEnum { Ready }\n")
    "ChunkImportLaterEnum::Missing" 0
  val _ = rejects_at \<^theory> "missing variant through an imported later enum"
    ["\"Missing\" is not a variant of enum \"ChunkImportLaterEnum\""]
    (broken ^ "  use ChunkImportLaterEnum as LaterEnumAlias;\n" ^
     "  use LaterEnumAlias::Missing as missing_variant;\n" ^
     "  enum ChunkImportLaterEnum { Ready }\n")
    "Missing" 0
  val _ = rejects_at \<^theory> "later enum variant"
    ["import target \"ChunkImportLaterChoice::Ready\" of \"later_ready\" is not yet available"]
    ("  fn ChunkImportLaterUse(x: u32) -> u32 { match x { later_ready => 1 } }\n" ^
     "  use ChunkImportLaterChoice::{self as LaterChoice, Ready as later_ready};\n" ^
     "  enum ChunkImportLaterChoice { Ready }\n")
    "later_ready" 0
end
\<close>

text\<open>
Entities that exist before the chunk keep resolving through an alias whose other namespace a later
member declares, and a later value-only target leaves the type namespace of its spelling to the
persistent alias.
\<close>

urust_datatype \<open> enum ChunkImportBoth { Only } \<close>
urust_use \<open> use demo::Width as ChunkImportSpell; \<close>

urust \<open>
  fn ChunkImportBothType(choice: ChunkImportBothAlias) -> u32 {
    match choice { ChunkImportBothAlias::Only => 1 }
  }

  fn ChunkImportSpellUser(width: ChunkImportSpell) -> ChunkImportSpell { width }

  use ChunkImportBoth as ChunkImportBothAlias;
  use ChunkImportSpellLater as ChunkImportSpell;

  fn ChunkImportBoth() -> u32 { 2 }

  fn ChunkImportSpellLater() -> u32 { 1 }

  fn ChunkImportBothValue() -> u32 { ChunkImportBothAlias() + ChunkImportSpell() }
\<close>

urust_fn \<open>
  fn ChunkImportBothTypeControl(choice: ChunkImportBoth) -> u32 {
    match choice { ChunkImportBoth::Only => 1 }
  }
\<close>
urust_fn \<open> fn ChunkImportSpellUserControl(width: demo::Width) -> demo::Width { width } \<close>
urust_fn \<open> fn ChunkImportBothValueControl() -> u32 { ChunkImportBoth() + ChunkImportSpellLater() } \<close>

lemma \<open> chunk_import_both_type = chunk_import_both_type_control \<close>
  unfolding chunk_import_both_type_def chunk_import_both_type_control_def by (rule refl)
lemma \<open> chunk_import_spell_user = chunk_import_spell_user_control \<close>
  unfolding chunk_import_spell_user_def chunk_import_spell_user_control_def by (rule refl)
lemma \<open> chunk_import_both_value = chunk_import_both_value_control \<close>
  unfolding chunk_import_both_value_def chunk_import_both_value_control_def by (rule refl)

text\<open>
The conversion calls of a native \<open>simple_word_enum\<close> enum that the chunk declares are importable
by the members after it, exactly as in a single-item sequence.
\<close>

urust \<open>
  #[repr(u8)]
  enum ChunkImportConv { Low = 1, High = 4 }

  \<omega>\<open>backend = "simple_word_enum", word_width = 16\<close>
  enum ChunkImportConvWide { Low = 1, High = 2 }

  use ChunkImportConv::{to_u8 as conv_to_byte, try_from as conv_from};
  use ChunkImportConvWide::to_u16 as wide_to_word;

  fn ChunkImportConvUse(level: ChunkImportConv) -> u8 { conv_to_byte(level) }

  fn ChunkImportConvWideUse(level: ChunkImportConvWide) -> u16 { wide_to_word(level) }
\<close>

urust_fn \<open>
  fn ChunkImportConvUseControl(level: ChunkImportConv) -> u8 { ChunkImportConv::to_u8(level) }
\<close>
urust_fn \<open>
  fn ChunkImportConvWideUseControl(level: ChunkImportConvWide) -> u16 {
    ChunkImportConvWide::to_u16(level)
  }
\<close>

lemma \<open> chunk_import_conv_use = chunk_import_conv_use_control \<close>
  unfolding chunk_import_conv_use_def chunk_import_conv_use_control_def by (rule refl)
lemma \<open> chunk_import_conv_wide_use = chunk_import_conv_wide_use_control \<close>
  unfolding chunk_import_conv_wide_use_def chunk_import_conv_wide_use_control_def by (rule refl)

text\<open>
A body import of a chunk alias whose type exists and whose value a later member declares is
available in the type namespace and unavailable in the value namespace.
\<close>

urust_datatype \<open> enum ChunkImportBodyType { Only } \<close>
urust_datatype \<open> enum ChunkImportBodyValue { Only } \<close>

urust \<open>
  fn ChunkImportBodyTypeUse(choice: ChunkImportBodyType) -> u32 {
    use BodyTypeAlias as BodyInner;
    match choice { BodyInner::Only => 1 }
  }

  use ChunkImportBodyType as BodyTypeAlias;

  fn ChunkImportBodyType() -> u32 { 2 }
\<close>

urust_fn \<open>
  fn ChunkImportBodyTypeUseControl(choice: ChunkImportBodyType) -> u32 {
    match choice { ChunkImportBodyType::Only => 1 }
  }
\<close>

lemma \<open> chunk_import_body_type_use = chunk_import_body_type_use_control \<close>
  unfolding chunk_import_body_type_use_def chunk_import_body_type_use_control_def by (rule refl)

text\<open>
A call through an alias of an existing literal whose function a later member declares names the
unavailable call; value uses keep the literal, and calls after the function resolve to it.
\<close>

definition chunk_import_lit_value :: \<open> 32 word \<close> where
  \<open> chunk_import_lit_value = 5 \<close>
micro_rust_notation (literal) chunk_import_lit_value ("ChunkImportLit")

urust_fn \<open> fn ChunkImportLitEarlyControl() -> u32 { ChunkImportLit } \<close>

urust \<open>
  fn ChunkImportLitEarly() -> u32 { lit_value }

  use ChunkImportLit as lit_value;

  fn ChunkImportLit() -> u32 { 6 }

  fn ChunkImportLitLate() -> u32 { lit_value() }
\<close>

urust_fn \<open> fn ChunkImportLitLateControl() -> u32 { ChunkImportLit() } \<close>

lemma \<open> chunk_import_lit_early = chunk_import_lit_early_control \<close>
  unfolding chunk_import_lit_early_def chunk_import_lit_early_control_def by (rule refl)
lemma \<open> chunk_import_lit_late = chunk_import_lit_late_control \<close>
  unfolding chunk_import_lit_late_def chunk_import_lit_late_control_def by (rule refl)

definition chunk_import_lit_two_value :: \<open> 32 word \<close> where
  \<open> chunk_import_lit_two_value = 7 \<close>
micro_rust_notation (literal) chunk_import_lit_two_value ("ChunkImportLitTwo")

ML_val\<open>
local
  open Chunk_Use_Audit
  val broken = "  fn ChunkImportBroken() -> bool { 1u32 }\n"
in
  val _ = rejects_at \<^theory> "conversion call before its enum"
    ["import target \"ChunkImportConvLater::to_u8\" of \"later_to_byte\" is not yet available"]
    ("  fn ChunkImportConvEarly(x: u8) -> u8 { later_to_byte(x) }\n" ^
     "  use ChunkImportConvLater::to_u8 as later_to_byte;\n" ^
     "  #[repr(u8)]\n  enum ChunkImportConvLater { Low = 1 }\n")
    "later_to_byte" 0
  val _ = rejects_at \<^theory> "conversion call filtered out" ["unknown import target \"ChunkImportConvNone::to_u8\""]
    (broken ^ "  " ^ annotation "plugins = (plugins only: word_conversion)" ^ "\n" ^
     "  #[repr(u8)]\n  enum ChunkImportConvNone { Low = 1 }\n" ^
     "  use ChunkImportConvNone::to_u8 as none_to_byte;\n")
    "ChunkImportConvNone::to_u8" 0
  val _ = rejects_at \<^theory> "value use through a partially available body import"
    ["import target \"ChunkImportBodyValue\" of \"body_inner\" is not yet available"]
    ("  fn ChunkImportBodyValueUse() -> u32 { use BodyValueAlias as body_inner; body_inner() }\n" ^
     "  use ChunkImportBodyValue as BodyValueAlias;\n" ^
     "  fn ChunkImportBodyValue() -> u32 { 3 }\n")
    "body_inner" 1
  val _ = rejects_at \<^theory> "predicted duplicate before the first declaration"
    ["duplicate value import \"dup_predicted\""]
    (broken ^ "  use ChunkImportDupLater as dup_predicted;\n  use demo::value as dup_predicted;\n" ^
     "  fn ChunkImportDupLater() -> u32 { 1 }\n")
    "dup_predicted" 1
  val _ = rejects_at \<^theory> "call through a literal whose function is declared later"
    ["import target \"ChunkImportLitTwo\" of \"lit_two\" is not yet available as a call"]
    ("  fn ChunkImportLitTwoEarly() -> u32 { lit_two() }\n" ^
     "  use ChunkImportLitTwo as lit_two;\n" ^
     "  fn ChunkImportLitTwo() -> u32 { 8 }\n")
    "lit_two" 0
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
  val _ = rejects_at \<^theory> "import before item" value_clash
    ("  use demo::value as ChunkImportClash;\n  fn ChunkImportClash() -> u32 { 1 }\n")
    "ChunkImportClash" 0
  val _ = rejects_at \<^theory> "import after item" value_clash
    ("  fn ChunkImportClash() -> u32 { 1 }\n  use demo::value as ChunkImportClash;\n")
    "ChunkImportClash" 1
  val _ = rejects_at \<^theory> "type import and struct"
    ["type import \"ChunkImportClashType\" collides with the same-scope generated Rust item"]
    ("  use UsePacket as ChunkImportClashType;\n  struct ChunkImportClashType { value: u32 }\n")
    "ChunkImportClashType" 0
  val _ = rejects_at \<^theory> "value import and unit struct"
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
      val {output, warnings, reports, ...} = rejected \<^theory> label expected text
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
  val {reports, warnings, ...} = run_success \<^theory> "chunk-import-navigation" text
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
  val pretty = run_success \<^theory> "chunk-import-pretty" ("urust [pretty, verbosity = 2, pp_test] " ^
    command_source body)
  val plain_run = run_success \<^theory> "chunk-import-plain" ("urust [verbosity = 2] " ^ command_source body)
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
