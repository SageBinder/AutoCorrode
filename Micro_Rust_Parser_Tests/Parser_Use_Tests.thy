theory Parser_Use_Tests
  imports
    Parser_Use_Left_Fixtures
    Parser_Use_Right_Fixtures
begin

section\<open> Scope foundation \<close>

text\<open>
Direct tests of \<^ML_structure>\<open>URust_Import_Scope\<close> and \<^ML_structure>\<open>URust_Imports\<close>.
They construct use trees without parsing and check namespace membership, collisions, cycles,
confinement, merging and stable identities.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val type_ns = S.Type_Namespace
  val value_ns = S.Value_Namespace

  val choice =
    prepare ctxt
      [group ["UseChoice"]
        [self_member (SOME "Selection"), leaf ["Empty"] NONE,
         leaf ["Value"] (SOME "Present"), leaf ["Named"] (SOME "Pick")]]
  val _ = require "grouped self imports the enum type"
    (lookup_roles choice type_ns "Selection" = SOME [S.Generated_Enum, S.Mapped_Type])
  val _ = require "grouped self imports no value" (is_none (S.lookup choice value_ns "Selection"))
  val _ = require "unit variant constructor"
    (lookup_roles choice value_ns "Empty" = SOME [S.Generated_Constructor])
  val _ = require "unit variant declaration"
    (lookup_roles choice type_ns "Empty" = SOME [S.Enum_Variant])
  val _ = require "renamed tuple variant"
    (lookup_key choice value_ns "Present" = SOME "UseChoice::Value")
  val _ = require "named variant has only its declaration identity"
    (is_none (S.lookup choice value_ns "Pick") andalso
      lookup_roles choice type_ns "Pick" = SOME [S.Enum_Variant])
  val _ = require "one identity per leaf"
    (#identity (the (S.lookup choice type_ns "Empty")) =
      #identity (the (S.lookup choice value_ns "Empty")))

  val shapes =
    prepare ctxt
      [leaf ["UsePacket"] NONE, leaf ["UseTuple"] NONE, leaf ["UseUnit"] NONE,
       leaf ["use_increment"] (SOME "inc"), leaf ["demo", "increment"] (SOME "call"),
       leaf ["demo", "WIDTH"] NONE, leaf ["demo", "ZERO"] NONE, leaf ["demo", "Width"] NONE,
       leaf ["demo", "Short"] NONE, leaf ["demo", "Cell"] NONE, leaf ["UseWrapper"] NONE]
  val _ = require "named struct has no value identity"
    (lookup_roles shapes type_ns "UsePacket" = SOME [S.Generated_Struct, S.Mapped_Type] andalso
      is_none (S.lookup shapes value_ns "UsePacket"))
  val _ = require "tuple and unit structs import both namespaces"
    (lookup_roles shapes value_ns "UseTuple" = SOME [S.Generated_Constructor] andalso
      lookup_roles shapes value_ns "UseUnit" = SOME [S.Generated_Constructor] andalso
      lookup_roles shapes type_ns "UseUnit" = SOME [S.Generated_Struct, S.Mapped_Type])
  val _ = require "generated function"
    (lookup_roles shapes value_ns "inc" = SOME [S.Generated_Function] andalso
      is_none (S.lookup shapes type_ns "inc"))
  val _ = require "exact notation roles"
    (lookup_roles shapes value_ns "call" = SOME [S.Call_Notation] andalso
      lookup_roles shapes value_ns "WIDTH" = SOME [S.Literal_Notation] andalso
      lookup_roles shapes value_ns "ZERO" = SOME [S.Literal_Notation])
  val _ = require "type mappings and aliases"
    (lookup_roles shapes type_ns "Width" = SOME [S.Mapped_Type] andalso
      lookup_roles shapes type_ns "Short" = SOME [S.Mapped_Type] andalso
      lookup_key shapes type_ns "Cell" = SOME "demo::Cell")

  val shared = prepare ctxt [leaf ["UsePacket"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")]
  val _ = require "distinct type and value bindings may share a spelling"
    (lookup_key shared type_ns "Pick" = SOME "UsePacket" andalso
      lookup_key shared value_ns "Pick" = SOME "demo::value")

  val _ = rejects "value imports with different notation roles" "duplicate value import"
    (fn () => prepare ctxt [leaf ["demo", "WIDTH"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "identical duplicate import" "duplicate value import"
    (fn () => prepare ctxt [leaf ["demo", "increment"] NONE, leaf ["demo", "increment"] NONE])
  val _ = rejects "tuple struct and function value collision" "duplicate value import"
    (fn () => prepare ctxt [leaf ["UseTuple"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "unit variant and function value collision" "duplicate value import"
    (fn () =>
      prepare ctxt [leaf ["UseChoice", "Empty"] (SOME "Pick"), leaf ["demo", "value"] (SOME "Pick")])
  val _ = rejects "import cycle" "cyclic imports"
    (fn () => prepare ctxt [leaf ["Left"] (SOME "Right"), leaf ["Right"] (SOME "Left")])
  val _ = rejects "unused missing target" "unknown import target \"MissingTarget\""
    (fn () => prepare ctxt [leaf ["MissingTarget"] (SOME "Unused")])
  val _ = rejects "grouped self on a struct" "grouped `self` requires a generated enum"
    (fn () => prepare ctxt [group ["UsePacket"] [self_member (SOME "Selection")]])
  val _ = rejects "type aliases own no variants" "is not a generated enum"
    (fn () => prepare ctxt [leaf ["demo", "Short"] (SOME "Alias"), leaf ["Alias", "Empty"] NONE])
  val _ = rejects "unknown variant of an imported enum" "is not a variant of enum \"UseChoice\""
    (fn () => prepare ctxt [leaf ["UseChoice"] (SOME "C"), leaf ["C", "Missing"] NONE])
  val _ = rejects "field-only lens aliases" "field notation \"sample\" is outside the import surface"
    (fn () => prepare ctxt [leaf ["sample"] NONE])
  val _ = rejects "associated items" "unknown import target \"UsePacket::new\""
    (fn () => prepare ctxt [leaf ["UsePacket", "new"] NONE])
  val _ = rejects "variants own no nested items" "enum variants have no nested importable items"
    (fn () => prepare ctxt [leaf ["UseChoice"] (SOME "C"), leaf ["C", "Value", "inner"] NONE])

  val reverse =
    prepare ctxt
      [leaf ["Selection", "Value"] (SOME "Present"), leaf ["UseChoice"] (SOME "Selection")]
  val _ = require "same-batch dependency in reverse source order"
    (lookup_key reverse value_ns "Present" = SOME "UseChoice::Value")
  val existing = prepare ctxt [leaf ["use_increment"] NONE, leaf ["use_increment"] (SOME "again")]
  val _ = require "an import never resolves through itself"
    (lookup_key existing value_ns "again" = SOME "use_increment")

  val fixed_ctxt = #2 (Variable.add_fixes ["fixed_name"] ctxt)
  val _ = rejects "imports never capture fixed variables" "unknown import target \"fixed_name\""
    (fn () => prepare fixed_ctxt [leaf ["fixed_name"] (SOME "Captured")])

  val outer = prepare ctxt [leaf ["UseChoice"] (SOME "Selection"), leaf ["Selection", "Value"] (SOME "Present")]
  val inner = prepare outer [leaf ["UseOtherChoice"] (SOME "Selection")]
  val _ = require "frames are confined to derived contexts"
    (S.frame_depth ctxt = 0 andalso S.frame_depth outer = 1 andalso S.frame_depth inner = 2 andalso
      is_none (S.lookup ctxt type_ns "Selection"))
  val _ = require "an inner frame shadows its enclosing frame"
    (lookup_key inner type_ns "Selection" = SOME "UseOtherChoice" andalso
      lookup_key outer type_ns "Selection" = SOME "UseChoice")
  val _ = require "captured identities survive later shadowing"
    (lookup_key inner value_ns "Present" = SOME "UseChoice::Value")
  val per_namespace = prepare outer [leaf ["demo", "value"] (SOME "Selection")]
  val _ = require "shadowing is per namespace"
    (lookup_key per_namespace type_ns "Selection" = SOME "UseChoice" andalso
      lookup_key per_namespace value_ns "Selection" = SOME "demo::value")
in
  val _ = ()
end
\<close>

subsection\<open> Persistent bindings, merging and collisions \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  val value_ns = S.Value_Namespace
  fun theory_context name =
    Proof_Context.init_global
      (Context.get_theory {long = true} \<^theory> ("Micro_Rust_Parser_Tests." ^ name))
  fun identity context alias = #identity (the (S.lookup context value_ns alias))

  val aliases = S.dump_persistent ctxt |> map #alias |> sort_strings
  val _ = require "diamond inventory"
    (aliases = ["MergedCollision", "left_value", "merged_width", "right_value", "shared_increment"])
  val _ = require "diamond import retains its declaration identity"
    (identity ctxt "shared_increment" =
      identity (theory_context "Parser_Use_Base_Fixtures") "shared_increment")
  val left = identity (theory_context "Parser_Use_Left_Fixtures") "merged_width"
  val right = identity (theory_context "Parser_Use_Right_Fixtures") "merged_width"
  val _ = require "independent identical imports merge to the lower identity"
    (left <> right andalso identity ctxt "merged_width" = Int.min (left, right))

  val left_binding = the (S.lookup ctxt value_ns "left_value")
  val conflicting = {alias = "left_value", alias_pos = Position.none, namespace = value_ns,
    key = "demo::increment", roles = [S.Call_Notation], identity = serial (),
    declaration_pos = Position.none}: S.binding
  val _ = require "merging the same binding is idempotent"
    (map #identity (S.merge_persistent ([left_binding], [left_binding])) = [#identity left_binding])
  val _ = rejects "conflicting merged imports" "conflicting value imports for \"left_value\""
    (fn () => S.merge_persistent ([left_binding], [conflicting]))

  val lthy = Named_Target.theory_init \<^theory>
  fun install trees context = fold (URust_Imports.install o item) trees context
  val _ = rejects "persistent duplicate in one scope" "duplicate value import \"left_value\""
    (fn () => install [leaf ["demo", "increment"] (SOME "left_value")] lthy)
  val _ = rejects "import after a same-scope function" "collides with the same-scope generated Rust function"
    (fn () => install [leaf ["demo", "value"] (SOME "use_increment")] lthy)
  val _ = rejects "import after a same-scope constructor" "collides with the same-scope generated Rust constructor"
    (fn () => install [leaf ["demo", "value"] (SOME "UseUnit")] lthy)
  val _ = rejects "import after a same-scope type" "collides with the same-scope generated Rust item"
    (fn () => install [leaf ["demo", "Width"] (SOME "UsePacket")] lthy)
  val _ = rejects "import after a same-scope type mapping" "collides with the same-scope Rust type"
    (fn () => install [leaf ["UsePacket"] (SOME "u8")] lthy)
  val later = install [leaf ["demo", "value"] (SOME "LaterItem"), leaf ["demo", "Width"] (SOME "LaterType")] lthy
  val _ = rejects "function after a same-scope import" "collides with the value import"
    (fn () =>
      URust_Item_Scope.register_function
        {rust_name = "LaterItem", rust_pos = Position.none, function = \<^term>\<open>use_increment\<close>} later)
  val _ = rejects "type after a same-scope import" "collides with the type import"
    (fn () =>
      URust_Type_Mappings.register_generated
        {rust_name = "LaterType", rust_pos = Position.none, hol_type_name = \<^type_name>\<open>bool\<close>} later)
in
  val _ = ()
end
\<close>

experiment
begin

local_setup \<open>
  URust_Imports.install (Parser_Use_Test.item (Parser_Use_Test.leaf ["demo", "value"] (SOME "experiment_value")))
\<close>

ML_val\<open>
  Parser_Use_Test.require "experiment import is active"
    (Parser_Use_Test.lookup_key \<^context> URust_Import_Scope.Value_Namespace "experiment_value" =
      SOME "demo::value")
\<close>

end

ML_val\<open>
  Parser_Use_Test.require "experiment import is confined"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "experiment_value"))
\<close>

locale use_scope_locale =
  fixes use_scope_parameter :: nat
begin

local_setup \<open>
  URust_Imports.install (Parser_Use_Test.item (Parser_Use_Test.leaf ["demo", "WIDTH"] (SOME "locale_width")))
\<close>

end

ML_val\<open>
  Parser_Use_Test.require "locale import is confined to its context"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "locale_width"))
\<close>

context use_scope_locale
begin

ML_val\<open>
  Parser_Use_Test.require "locale import is available when the locale is reopened"
    (Parser_Use_Test.lookup_key \<^context> URust_Import_Scope.Value_Namespace "locale_width" =
      SOME "demo::WIDTH")
\<close>

end


section\<open> Syntax and printing \<close>

text\<open>
Parser-only tests of the shared use-tree grammar for complete items and body statements, their
positioned rejections, exact symbol-counted ranges, recovery and printer roundtrips.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  open URust_AST
  val ctxt = \<^context>
  fun parse text =
    (case URust_Parser.parse_use_source ctxt (Parser_Lex_Util.text_source text) of
       SOME item => item
     | NONE => error ("empty use item " ^ quote text))
  fun body text =
    (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source text) of
       SOME expression => expression
     | NONE => error ("empty body " ^ quote text))
  fun leaves text =
    URust_Imports.flatten (parse text)
    |> map (fn leaf => (URust_Imports.leaf_path leaf, #1 (URust_Imports.leaf_alias leaf)))

  val _ = require "plain import" (leaves "use demo::increment;" = [(["demo", "increment"], "increment")])
  val _ = require "renamed import" (leaves "use demo::increment as inc;" = [(["demo", "increment"], "inc")])
  val _ = require "group import"
    (leaves "use demo::{increment as inc, Width};" =
      [(["demo", "increment"], "inc"), (["demo", "Width"], "Width")])
  val _ = require "enum self and renamed variants"
    (leaves "use UseChoice::{self as Selection, Empty, Value as Present};" =
      [(["UseChoice"], "Selection"), (["UseChoice", "Empty"], "Empty"),
       (["UseChoice", "Value"], "Present")])
  val _ = require "nested root group with trailing commas"
    (leaves "use {demo::{WIDTH, value,}, UseChoice::{self, Value as Present,},};" =
      [(["demo", "WIDTH"], "WIDTH"), (["demo", "value"], "value"),
       (["UseChoice"], "UseChoice"), (["UseChoice", "Value"], "Present")])
  val _ =
    (case use_item_tree (parse "use UseChoice::{self};") of
       Use_Group ([("UseChoice", _)], [Use_Self (_, NONE, _)], _) => ()
     | _ => error "grouped self is not represented explicitly")
  val _ =
    (case use_item_tree (parse "use demo::{ // comment\n increment /* block */ as inc };") of
       Use_Group (_, [Use_Path ([("increment", _)], SOME ("inc", _), _)], _) => ()
     | _ => error "comments inside a use tree changed its AST")

  fun reject_use (expected, text) =
    rejects ("use syntax " ^ quote text) expected (fn () => parse text)
  val _ =
    List.app reject_use
      [("glob imports (`*`) are not supported", "use demo::*;"),
       ("glob imports (`*`) are not supported", "use *;"),
       ("glob imports (`*`) are not supported", "use demo::{value, *};"),
       ("empty use groups are not supported", "use demo::{};"),
       ("empty use groups are not supported", "use {};"),
       ("rooted at `::`", "use ::demo::value;"),
       ("rooted at `crate`", "use crate::demo;"),
       ("rooted at `super`", "use super::demo;"),
       ("rooted at `self`", "use self::demo;"),
       ("rooted at `Self`", "use Self::Value;"),
       ("supported only as a grouped `{self}` import", "use demo::self;"),
       ("supported only as a grouped `{self}` import", "use self;"),
       ("supported only as a grouped `{self}` import", "use demo::{Choice::self};"),
       ("grouped `self` requires a group prefix", "use {self};"),
       ("underscore imports (`as _`) are not supported", "use demo::value as _;"),
       ("`_` is not a use path segment", "use demo::_;"),
       ("cannot be an import alias", "use demo::value as self;"),
       ("cannot be an import alias", "use demo::value as crate;"),
       ("cannot be a use path segment", "use demo::impl;"),
       ("generic arguments are not allowed in use paths", "use demo::Cell::<u8>;"),
       ("generic arguments are not allowed in use paths", "use demo::<u8>::Cell;"),
       ("visibility qualifiers (`pub use`) are not supported", "pub use demo::value;"),
       ("visibility qualifiers (`pub use`) are not supported", "pub(crate) use demo::value;"),
       ("unexpected `extern` before a use item", "extern use demo::value;"),
       ("syntax error", "use demo::value"),
       ("syntax error", "use demo::value as fn;"),
       ("syntax error", "use demo::{value as};"),
       ("syntax error", "use u8::MAX;"),
       ("syntax error", "use demo::shout!;"),
       ("syntax error", "use demo::{value,,};"),
       ("syntax error", "use demo::value; use demo::WIDTH;"),
       ("expected one complete use item", "type Width = u16;"),
       ("expected one complete use item", "fn probe() {}")]
  val _ =
    rejects "use item as a function" "urust_fn: expected a complete function item"
      (fn () => URust_Parser.parse_function_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ =
    rejects "use item as a datatype" "urust_datatype: expected a struct or enum item"
      (fn () => URust_Parser.parse_datatype_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ =
    rejects "use item as a type alias" "urust_type_alias: expected a complete type alias item"
      (fn () => URust_Parser.parse_type_alias_source ctxt (Parser_Lex_Util.text_source "use demo::value;"))
  val _ = require "recovery after a failed use item" (leaves "use demo::value;" = [(["demo", "value"], "value")])

  val _ =
    (case body "use demo::value; value()" of
       UE_Use (_, UE_Call _, _) => ()
     | _ => error "leading body import")
  val _ =
    (case body "{ use demo::value; }" of
       UE_Block (UE_Use (_, UE_Unit unit_layout, _), _) =>
         require "terminal import has a token-free unit continuation"
           (null (source_tokens unit_layout))
     | _ => error "import-only block")
  val _ =
    (case body "let x = 1; use demo::value; x" of
       UE_Let (_, _, UE_Use (_, UE_Path _, _), _) => ()
     | _ => error "import after a let")
  val _ =
    (case body "x; use demo::value; use demo::WIDTH;" of
       UE_Seq (_, UE_Use (_, UE_Use (_, UE_Unit _, _), _), _) => ()
     | _ => error "terminal imports after a statement")
  val _ =
    (case body "if c { use demo::value; value() } else { 0 }" of
       UE_If (_, UE_Block (UE_Use _, _), _, _) => ()
     | _ => error "branch block import")
  val _ = rejects "import as an operand" "syntax error" (fn () => body "1 + use demo::value;")
  val _ = rejects "import as a let initializer" "syntax error" (fn () => body "let x = use demo::value; x")
  val _ = rejects "body visibility" "visibility qualifiers (`pub use`) are not supported"
    (fn () => body "pub use demo::value; value()")
  val _ =
    (case body "x + 1" of
       UE_Bin _ => ()
     | _ => error "expression recovery after a failed body import")

  val positioned =
    Parser_Lex_Util.positioned_content_source
      "/* \<alpha>\<beta> */ use demo::{value as picked, UseChoice::{self}};"
      (Position.make0 1 7000 0 "" "" "use-syntax-positions")
  val text = Input.string_of positioned
  fun offset_of_text needle =
    let
      val (prefix, rest) = Substring.position needle (Substring.full text)
      val _ = if Substring.isEmpty rest then error ("missing " ^ needle) else ()
    in 7000 + length (Symbol.explode (Substring.string prefix)) end
  fun range_of needle =
    let val start = offset_of_text needle
    in (SOME start, SOME (start + length (Symbol.explode needle))) end
  fun offsets pos = (Position.offset_of pos, Position.end_offset_of pos)
  val positioned_item = the (URust_Parser.parse_use_source ctxt positioned)
  val positioned_leaves = URust_Imports.flatten positioned_item
  val _ = require "alias range after escaped symbols"
    (offsets (#2 (URust_Imports.leaf_alias (hd positioned_leaves))) = range_of "picked")
  val _ = require "grouped self alias range"
    (offsets (#2 (URust_Imports.leaf_alias (nth positioned_leaves 1))) = range_of "self")
  val _ = require "complete use item span"
    (offsets (use_item_position positioned_item) =
      (SOME (offset_of_text "use"), SOME (offset_of_text ";" + 1)))
  val _ =
    (case use_item_tree positioned_item of
       Use_Group ([("demo", demo_pos)], [Use_Path ([("value", value_pos)], _, path_layout), _], layout) =>
         (require "prefix segment range" (offsets demo_pos = range_of "demo");
          require "member segment range" (offsets value_pos = range_of "value");
          require "as keyword range"
            (map offsets (source_token_positions path_layout (Keyword_Token "as")) = [range_of "as"]);
          require "group delimiters"
            (length (source_token_positions layout (Delimiter_Token "{")) = 1 andalso
              length (source_token_positions layout (Delimiter_Token ",")) = 1))
     | _ => error "positioned use tree shape")

  fun roundtrip options text =
    let
      val original = parse text
      val rendered = URust_Printer.string_of_use_item options original
      val reparsed = parse rendered
    in
      require ("use item tokens changed for " ^ quote text ^ " rendered as " ^ quote rendered)
        (URust_Printer.tokens_of_use_item options original =
          URust_Printer.tokens_of_use_item options reparsed)
    end
  val roundtrip_items =
    ["use demo::increment;", "use demo::increment as inc;",
     "use demo::{increment as inc, Width};",
     "use UseChoice::{self as Selection, Empty, Value as Present};",
     "use {demo::{WIDTH, value,}, UseChoice::{self,},};"]
  val _ = List.app (roundtrip URust_Printer.serialized_options) roundtrip_items
  val _ = List.app (roundtrip URust_Printer.human_options) roundtrip_items
  val _ =
    require "canonical rendering"
      (URust_Printer.string_of_use_item URust_Printer.serialized_options
         (parse "use {demo::{WIDTH, value,}, UseChoice::{self as S,},};") =
        "use {demo::{WIDTH, value}, UseChoice::{self as S}};")
  fun body_roundtrip options text =
    let
      val original = body text
      val rendered = URust_Printer.string_of_expr options original
      val reparsed = body rendered
    in
      require ("body tokens changed for " ^ quote text ^ " rendered as " ^ quote rendered)
        (URust_Printer.tokens_of_expr options original =
          URust_Printer.tokens_of_expr options reparsed)
    end
  val roundtrip_bodies =
    ["use demo::value; value()", "{ use demo::value; }", "let x = 1; use demo::value; x",
     "x; use demo::value; use demo::WIDTH;",
     "match c { Present(n) => { use demo::value; n } _ => 0 }",
     "(use demo::value; 1)", "|x| { use demo::value as v; v() }"]
  val _ = List.app (body_roundtrip URust_Printer.serialized_options) roundtrip_bodies
  val _ = List.app (body_roundtrip URust_Printer.human_options) roundtrip_bodies
  val _ =
    URust_Printer_Output.pretty_human_use_item_with_reparse
      (fn input => ignore (URust_Parser.parse_use_source ctxt input))
      (parse "use UseChoice::{self as Selection, Value as Present};")
    |> ignore
in
  val _ = ()
end
\<close>


section\<open> Persistent imports \<close>

text\<open>
\<open>urust_use\<close> installs one complete use item as ordinary local-theory declarations. Every
generated definition below is compared by kernel reflexivity with its explicitly qualified
counterpart, so the import changes only name resolution.
\<close>

urust_use \<open> use demo::increment as inc; \<close>
urust_use \<open> use demo::{WIDTH as Width_Value, ZERO, COUNT, value as fetch}; \<close>
urust_use \<open> use UseChoice::{self as Selection, Empty, Value as Present, Named as NamedVariant}; \<close>
urust_use \<open> use use_increment as bump; \<close>
urust_use \<open> use use_identity as ident; \<close>
urust_use \<open> use demo::{Width as Word32, Short, Cell, Pointer}; \<close>
urust_use \<open> use {UsePacket as Packet, UseTuple as Tuple1, UseUnit as Unit1, UseWrapper as Wrapper}; \<close>
urust_use \<open> use Selection::Value as SelectedValue; \<close>

subsection\<open> Values, calls and constructors \<close>

urust_expr use_call \<open> inc(3) \<close>
urust_expr use_call_qualified \<open> demo::increment(3) \<close>
lemma \<open> use_call = use_call_qualified \<close>
  unfolding use_call_def use_call_qualified_def by (rule refl)

urust_expr use_literal \<open> Width_Value \<close>
urust_expr use_literal_qualified \<open> demo::WIDTH \<close>
lemma \<open> use_literal = use_literal_qualified \<close>
  unfolding use_literal_def use_literal_qualified_def by (rule refl)

urust_expr use_overloaded_narrow \<open> ZERO + 1u32 \<close>
urust_expr use_overloaded_narrow_qualified \<open> demo::ZERO + 1u32 \<close>
lemma \<open> use_overloaded_narrow = use_overloaded_narrow_qualified \<close>
  unfolding use_overloaded_narrow_def use_overloaded_narrow_qualified_def by (rule refl)

urust_expr use_overloaded_wide \<open> ZERO + 1u64 \<close>
urust_expr use_overloaded_wide_qualified \<open> demo::ZERO + 1u64 \<close>
lemma \<open> use_overloaded_wide = use_overloaded_wide_qualified \<close>
  unfolding use_overloaded_wide_def use_overloaded_wide_qualified_def by (rule refl)

urust_expr use_nullary_call \<open> fetch() \<close>
urust_expr use_nullary_call_qualified \<open> demo::value() \<close>
lemma \<open> use_nullary_call = use_nullary_call_qualified \<close>
  unfolding use_nullary_call_def use_nullary_call_qualified_def by (rule refl)

urust_expr use_generated_call \<open> bump(2) \<close>
urust_expr use_generated_call_qualified \<open> use_increment(2) \<close>
lemma \<open> use_generated_call = use_generated_call_qualified \<close>
  unfolding use_generated_call_def use_generated_call_qualified_def by (rule refl)

urust_expr use_heterogeneous \<open> (ident(1u32), ident(true)) \<close>
urust_expr use_heterogeneous_qualified \<open> (use_identity(1u32), use_identity(true)) \<close>
lemma \<open> use_heterogeneous = use_heterogeneous_qualified \<close>
  unfolding use_heterogeneous_def use_heterogeneous_qualified_def by (rule refl)

urust_expr use_constructors \<open> (Present(3), Empty, Selection::Value(4), SelectedValue(5)) \<close>
urust_expr use_constructors_qualified
  \<open> (UseChoice::Value(3), UseChoice::Empty, UseChoice::Value(4), UseChoice::Value(5)) \<close>
lemma \<open> use_constructors = use_constructors_qualified \<close>
  unfolding use_constructors_def use_constructors_qualified_def by (rule refl)

urust_expr use_named_construction
  \<open> (NamedVariant { sample: 5 }, Selection::Named { sample: 6 }, Packet { sample: 7 }) \<close>
urust_expr use_named_construction_qualified
  \<open> (UseChoice::Named { sample: 5 }, UseChoice::Named { sample: 6 }, UsePacket { sample: 7 }) \<close>
lemma \<open> use_named_construction = use_named_construction_qualified \<close>
  unfolding use_named_construction_def use_named_construction_qualified_def by (rule refl)

urust_expr use_struct_constructors \<open> (Tuple1(7), Unit1) \<close>
urust_expr use_struct_constructors_qualified \<open> (UseTuple(7), UseUnit) \<close>
lemma \<open> use_struct_constructors = use_struct_constructors_qualified \<close>
  unfolding use_struct_constructors_def use_struct_constructors_qualified_def by (rule refl)

urust_expr use_repeat \<open> [0u8; COUNT] \<close>
urust_expr use_repeat_qualified \<open> [0u8; demo::COUNT] \<close>
lemma \<open> use_repeat = use_repeat_qualified \<close>
  unfolding use_repeat_def use_repeat_qualified_def by (rule refl)

urust_expr use_cast (x) \<open> x as Short \<close>
urust_expr use_cast_qualified (x) \<open> x as demo::Short \<close>
lemma \<open> use_cast = use_cast_qualified \<close>
  unfolding use_cast_def use_cast_qualified_def by (rule refl)

urust_expr use_imported_theory \<open> (shared_increment(1), merged_width, left_value(), right_value()) \<close>
urust_expr use_imported_theory_qualified
  \<open> (demo::increment(1), demo::WIDTH, demo::value(), demo::value()) \<close>
lemma \<open> use_imported_theory = use_imported_theory_qualified \<close>
  unfolding use_imported_theory_def use_imported_theory_qualified_def by (rule refl)

subsection\<open> Patterns \<close>

urust_expr use_match (c)
  \<open>
    match c {
      Present(n) => n,
      Empty => 0,
      NamedVariant { sample } => sample,
    }
  \<close>
urust_expr use_match_qualified (c)
  \<open>
    match c {
      UseChoice::Value(n) => n,
      UseChoice::Empty => 0,
      UseChoice::Named { sample } => sample,
    }
  \<close>
lemma \<open> use_match = use_match_qualified \<close>
  unfolding use_match_def use_match_qualified_def by (rule refl)

urust_expr use_match_enum_paths (c)
  \<open>
    match c {
      Selection::Value(n) => n,
      Selection::Named { sample } => sample,
      _ => 0,
    }
  \<close>
urust_expr use_match_enum_paths_qualified (c)
  \<open>
    match c {
      UseChoice::Value(n) => n,
      UseChoice::Named { sample } => sample,
      _ => 0,
    }
  \<close>
lemma \<open> use_match_enum_paths = use_match_enum_paths_qualified \<close>
  unfolding use_match_enum_paths_def use_match_enum_paths_qualified_def by (rule refl)

urust_expr use_literal_pattern (x) \<open> match x { Width_Value => 1u32, _ => 0 } \<close>
urust_expr use_literal_pattern_qualified (x) \<open> match x { demo::WIDTH => 1u32, _ => 0 } \<close>
lemma \<open> use_literal_pattern = use_literal_pattern_qualified \<close>
  unfolding use_literal_pattern_def use_literal_pattern_qualified_def by (rule refl)

urust_expr use_struct_pattern (p) \<open> match p { Packet { sample } => sample } \<close>
urust_expr use_struct_pattern_qualified (p) \<open> match p { UsePacket { sample } => sample } \<close>
lemma \<open> use_struct_pattern = use_struct_pattern_qualified \<close>
  unfolding use_struct_pattern_def use_struct_pattern_qualified_def by (rule refl)

subsection\<open> Types \<close>

urust_fn use_signature
  \<open> fn use_signature(x: Word32, y: Short, z: Cell<u8>, w: Wrapper<u8>, p: Pointer<u8>) -> Short { y } \<close>
urust_fn use_signature_qualified
  \<open>
    fn use_signature_qualified(
      x: demo::Width, y: demo::Short, z: demo::Cell<u8>, w: UseWrapper<u8>, p: demo::Pointer<u8>
    ) -> demo::Short { y }
  \<close>
lemma \<open> use_signature = use_signature_qualified \<close>
  unfolding use_signature_def use_signature_qualified_def by (rule refl)

urust_datatype \<open> struct UseImportedFields { width: Word32, short: Short, cell: Cell<u8> } \<close>
urust_datatype \<open> struct UseQualifiedFields { width: demo::Width, short: demo::Short, cell: demo::Cell<u8> } \<close>
urust_type_alias \<open> type UseAliasOfImport = Short; \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val ctxt = \<^context>
  fun selector_type name = fastype_of (Syntax.read_term ctxt name) |> range_type
  val _ = require "imported datatype field types"
    (map selector_type
       ["use_imported_fields_width", "use_imported_fields_short", "use_imported_fields_cell"] =
     map selector_type
       ["use_qualified_fields_width", "use_qualified_fields_short", "use_qualified_fields_cell"])
  fun resolve text = URust_Type_Mappings.resolve ctxt (URust_Parser.parse_type_source ctxt
    (Parser_Lex_Util.text_source text))
  val _ = require "type alias depending on an import" (resolve "UseAliasOfImport" = resolve "u16")
in
  val _ = ()
end
\<close>

subsection\<open> Rejections without fallback \<close>

urust_expr_rejects \<open> MergedCollision() \<close>
  \<open> generated Rust function "MergedCollision" collides with the value import of "demo::value" \<close>

urust_expr_rejects \<open> Width_Value(3) \<close> \<open> resolves to "demo::WIDTH", which cannot be used as a call \<close>
urust_expr_rejects \<open> inc \<close> \<open> resolves to "demo::increment", which cannot be used as a value \<close>
urust_expr_rejects \<open> [0u8; inc] \<close> \<open> which cannot be used as an array repeat length \<close>
urust_expr_rejects \<open> Present \<close> \<open> requires positional call syntax \<close>
urust_expr_rejects \<open> Empty() \<close> \<open> is a bare value, not a call \<close>
urust_expr_rejects \<open> Present(1, 2) \<close> \<open> expects 1 argument(s), but got 2 \<close>
urust_expr_rejects \<open> Selection::Missing(1) \<close> \<open> resolves to "UseChoice::Missing", which cannot be used as a call \<close>
urust_expr_rejects \<open> Word32::Value(1) \<close> \<open> is not a generated enum and cannot qualify a path \<close>
urust_expr_rejects \<open> bump::<u8>(1) \<close> \<open> generic arguments are not supported on generated Rust function paths \<close>
urust_expr_rejects \<open> 1u8 as NamedVariant \<close> \<open> names the enum variant "UseChoice::Named", not a type \<close>
urust_expr_rejects \<open> 1u8 as Word32 \<close> \<open> no supported cast operation \<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
in
  val _ = command_rejects thy "variant as a parameter type" "names the enum variant \"UseChoice::Named\""
    ("urust_fn _ " ^ cartouche " fn bad(x: NamedVariant) {} ")
  val _ = command_rejects thy "generic arity through an import" "has generic arities [0, 2]"
    ("urust_fn _ " ^ cartouche " fn bad(x: Cell<u8, u8>) {} ")
  val _ = command_rejects thy "unknown target" "unknown import target \"demo::Missing\""
    ("urust_use " ^ cartouche " use demo::{value as atomic_value, Missing}; ")
  val _ = command_rejects thy "persistent duplicate" "duplicate value import \"inc\""
    ("urust_use " ^ cartouche " use demo::value as inc; ")
  val _ = command_rejects thy "import after a generated function" "collides with the same-scope generated Rust function"
    ("urust_use " ^ cartouche " use demo::value as use_pair; ")
  val _ = command_rejects thy "generated function after an import" "collides with the value import"
    ("urust_use " ^ cartouche " use demo::value as LaterFunction; " ^
      "\nurust_fn " ^ cartouche " fn LaterFunction() {} ")
  val _ = command_rejects thy "datatype after an import" "collides with the type import"
    ("urust_use " ^ cartouche " use demo::Width as LaterType; " ^
      "\nurust_datatype " ^ cartouche " struct LaterType; ")
  val _ = command_rejects thy "use command parse failure" "glob imports"
    ("urust_use " ^ cartouche " use demo::*; ")
  val recovered = run_from (initial thy) "recovered use" ("urust_use " ^ cartouche " use demo::value as recovered_value; ")
  val _ = require "recovery after a failed use command"
    (lookup_key (Toplevel.context_of recovered) S.Value_Namespace "recovered_value" = SOME "demo::value")
  val _ = require "failed declarations install nothing"
    (is_none (S.lookup \<^context> S.Value_Namespace "atomic_value") andalso
      is_none (S.lookup \<^context> S.Value_Namespace "recovered_value"))
end
\<close>

subsection\<open> Locales, experiments and interpretation \<close>

locale use_command_locale =
  fixes use_command_parameter :: nat
begin

urust_use \<open> use demo::WIDTH as LocaleWidth; \<close>

urust_expr use_locale_literal \<open> LocaleWidth \<close>
urust_expr use_locale_literal_qualified \<open> demo::WIDTH \<close>
lemma \<open> use_locale_literal = use_locale_literal_qualified \<close>
  unfolding use_locale_literal_def use_locale_literal_qualified_def by (rule refl)

end

ML_val\<open>
  Parser_Use_Test.require "locale import is confined"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "LocaleWidth"))
\<close>

context use_command_locale
begin

urust_expr use_locale_reopened \<open> LocaleWidth \<close>

end

experiment
begin

urust_use \<open> use demo::value as experiment_fetch; \<close>
urust_expr use_experiment_call \<open> experiment_fetch() \<close>

end

ML_val\<open>
  Parser_Use_Test.require "experiment import is confined"
    (is_none (URust_Import_Scope.lookup \<^context> URust_Import_Scope.Value_Namespace "experiment_fetch"))
\<close>

interpretation use_command_interpretation: use_command_locale 0 .

ML_val\<open>
local
  open Parser_Use_Test
  fun locale_identity ctxt =
    #identity (the (S.lookup ctxt S.Value_Namespace "LocaleWidth"))
  val locale_ctxt = Named_Target.init [] \<^locale>\<open>use_command_locale\<close> \<^theory>
in
  val _ = require "interpretation replays the import with its declaration identity"
    (locale_identity \<^context> = locale_identity locale_ctxt)
end
\<close>


section\<open> Block imports \<close>

text\<open>
A use statement is visible throughout its block, including before its declaration, and in every
nested expression scope; it never escapes the block. Each block's imports are resolved before any
of its expressions or patterns, and are erased: every definition below is kernel-equal to its
import-free counterpart.
\<close>

definition use_tick :: \<open>(nat, nat, 'r, 'abort, 'i, 'o) expression\<close> where
  \<open>use_tick = bind (get id) (\<lambda>current. bind (put Suc) (\<lambda>_. literal current))\<close>

urust_expr use_block_before_declaration
  \<open> { let answer = local_inc(41); let retained = answer; use demo::increment as local_inc; retained } \<close>
urust_expr use_block_before_declaration_plain
  \<open> { let answer = demo::increment(41); let retained = answer; retained } \<close>
lemma \<open> use_block_before_declaration = use_block_before_declaration_plain \<close>
  unfolding use_block_before_declaration_def use_block_before_declaration_plain_def by (rule refl)

urust_expr use_block_reverse_dependencies
  \<open> { assert!(LocalPresent(7) == LocalSelection::Value(7)); use LocalSelection::Value as LocalPresent; use UseChoice as LocalSelection; LocalPresent(8) } \<close>
urust_expr use_block_reverse_dependencies_plain
  \<open> { assert!(UseChoice::Value(7) == UseChoice::Value(7)); UseChoice::Value(8) } \<close>
lemma \<open> use_block_reverse_dependencies = use_block_reverse_dependencies_plain \<close>
  unfolding use_block_reverse_dependencies_def use_block_reverse_dependencies_plain_def by (rule refl)

urust_expr use_block_nested
  \<open>
    {
      use demo::increment as pick;
      let first = pick(1);
      let second = { let early = pick(2); use use_increment as pick; (early, pick(3)) };
      let third = pick(4);
      let sibling = { use use_increment as pick; pick(5) };
      (first, second, third, sibling, pick(6))
    }
  \<close>
urust_expr use_block_nested_plain
  \<open>
    {
      let first = demo::increment(1);
      let second = { let early = use_increment(2); (early, use_increment(3)) };
      let third = demo::increment(4);
      let sibling = { use_increment(5) };
      (first, second, third, sibling, demo::increment(6))
    }
  \<close>
lemma \<open> use_block_nested = use_block_nested_plain \<close>
  unfolding use_block_nested_def use_block_nested_plain_def by (rule refl)

urust_expr use_block_captured_identity
  \<open>
    {
      use UseChoice as Selected;
      use Selected::Value as Captured;
      { use UseOtherChoice as Selected; (Captured(7), Selected::Value(true)) }
    }
  \<close>
urust_expr use_block_captured_identity_plain
  \<open> { { (UseChoice::Value(7), UseOtherChoice::Value(true)) } } \<close>
lemma \<open> use_block_captured_identity = use_block_captured_identity_plain \<close>
  unfolding use_block_captured_identity_def use_block_captured_identity_plain_def by (rule refl)

urust_expr use_block_closures
  \<open>
    {
      let callback = || selected_value();
      use demo::value as selected_value;
      let inner = |x| { use demo::increment as step; step(x) };
      use use_increment as shadowed;
      let first = shadowed(1);
      let shadowed = |x| x;
      (callback(), inner(2), first, shadowed(3))
    }
  \<close>
urust_expr use_block_closures_plain
  \<open>
    {
      let callback = || demo::value();
      let inner = |x| { demo::increment(x) };
      let first = use_increment(1);
      let shadowed = |x| x;
      (callback(), inner(2), first, shadowed(3))
    }
  \<close>
lemma \<open> use_block_closures = use_block_closures_plain \<close>
  unfolding use_block_closures_def use_block_closures_plain_def by (rule refl)

urust_expr use_block_control (c, choice)
  \<open>
    {
      let branch = if c { use demo::increment as step; step(1) } else { use use_increment as step; step(2) };
      for i in 0u32..3 { use demo::increment as each; each(i); }
      let UseChoice::Value(n) = choice else { use demo::value as fallback; return fallback(); };
      let matched = match choice { UseChoice::Empty => { use demo::value as arm; arm() }, _ => n };
      (branch, matched)
    }
  \<close>
urust_expr use_block_control_plain (c, choice)
  \<open>
    {
      let branch = if c { demo::increment(1) } else { use_increment(2) };
      for i in 0u32..3 { demo::increment(i); }
      let UseChoice::Value(n) = choice else { return demo::value(); };
      let matched = match choice { UseChoice::Empty => { demo::value() }, _ => n };
      (branch, matched)
    }
  \<close>
lemma \<open> use_block_control = use_block_control_plain \<close>
  unfolding use_block_control_def use_block_control_plain_def by (rule refl)

urust_expr use_block_patterns (choice)
  \<open>
    {
      use UseChoice::{Value as V, Empty as E, Named as N};
      match choice { V(n) => n, E => 0, N { sample } => sample }
    }
  \<close>
urust_expr use_block_patterns_plain (choice)
  \<open>
    {
      match choice { UseChoice::Value(n) => n, UseChoice::Empty => 0, UseChoice::Named { sample } => sample }
    }
  \<close>
lemma \<open> use_block_patterns = use_block_patterns_plain \<close>
  unfolding use_block_patterns_def use_block_patterns_plain_def by (rule refl)

urust_expr use_block_binder (choice) \<open> { use UseChoice::Value as V; match choice { V(n) => n, other => 0 } } \<close>
urust_expr use_block_binder_plain (choice) \<open> { match choice { UseChoice::Value(n) => n, other => 0 } } \<close>
lemma \<open> use_block_binder = use_block_binder_plain \<close>
  unfolding use_block_binder_def use_block_binder_plain_def by (rule refl)

urust_expr use_block_namespaces
  \<open> { use UsePacket as Pick; use demo::value as Pick; let packet = Pick { sample: Pick() }; packet } \<close>
urust_expr use_block_namespaces_plain
  \<open> { let packet = UsePacket { sample: demo::value() }; packet } \<close>
lemma \<open> use_block_namespaces = use_block_namespaces_plain \<close>
  unfolding use_block_namespaces_def use_block_namespaces_plain_def by (rule refl)

urust_expr use_block_cast (x) \<open> { use demo::Short as LocalShort; x as LocalShort } \<close>
urust_expr use_block_cast_plain (x) \<open> { x as u16 } \<close>
lemma \<open> use_block_cast = use_block_cast_plain \<close>
  unfolding use_block_cast_def use_block_cast_plain_def by (rule refl)

urust_expr use_block_terminal (x)
  \<open> { let only = { use demo::value; }; let after = { x; use demo::value; }; (only, after) } \<close>
urust_expr use_block_terminal_plain (x) \<open> { let only = {}; let after = { x; }; (only, after) } \<close>
lemma \<open> use_block_terminal = use_block_terminal_plain \<close>
  unfolding use_block_terminal_def use_block_terminal_plain_def by (rule refl)

urust_expr use_implicit_body \<open> let first = body_inc(1); use demo::increment as body_inc; body_inc(first) \<close>
urust_expr use_implicit_body_plain \<open> let first = demo::increment(1); demo::increment(first) \<close>
lemma \<open> use_implicit_body = use_implicit_body_plain \<close>
  unfolding use_implicit_body_def use_implicit_body_plain_def by (rule refl)

urust_fn use_function_body \<open> fn use_function_body(x: u32) -> u32 { use demo::increment as step; step(x) } \<close>
urust_fn use_function_body_plain \<open> fn use_function_body_plain(x: u32) -> u32 { demo::increment(x) } \<close>
lemma \<open> use_function_body = use_function_body_plain \<close>
  unfolding use_function_body_def use_function_body_plain_def by (rule refl)

urust_expr use_effect_order
  \<open>
    {
      use demo::value as unused_value;
      let first = \<epsilon>\<open> use_tick \<close>;
      use UseChoice::Value as UnusedPresent;
      let second = \<epsilon>\<open> use_tick \<close>;
      (first, second)
    }
  \<close>
urust_expr use_effect_order_plain
  \<open> { let first = \<epsilon>\<open> use_tick \<close>; let second = \<epsilon>\<open> use_tick \<close>; (first, second) } \<close>
lemma use_effect_order_plain: \<open> use_effect_order = use_effect_order_plain \<close>
  unfolding use_effect_order_def use_effect_order_plain_def by (rule refl)

lemma use_effect_order_evaluation:
  \<open> evaluate use_effect_order 0 = Success (0, 1, TNil) 2 \<close>
  by (simp add: use_effect_order_def use_tick_def micro_rust_simps evaluate_def get_def put_def
    literal_def Core_Expression.bind.simps bind_evaluate Let_def)

subsection\<open> Block rejections \<close>

urust_expr_rejects \<open> { use Left as Right; use Right as Left; 1 } \<close> \<open> cyclic imports \<close>
urust_expr_rejects \<open> { use MissingTarget as Unused; 1 } \<close> \<open> unknown import target "MissingTarget" \<close>
urust_expr_rejects \<open> { let ExistingName = 7u32; { use ExistingName as Captured; 1 } } \<close>
  \<open> unknown import target "ExistingName" \<close>
urust_expr_rejects \<open> |param| { use param as captured; 1 } \<close> \<open> unknown import target "param" \<close>
urust_expr_rejects \<open> { use demo::value; use demo::value; 1 } \<close> \<open> duplicate value import "value" \<close>
urust_expr_rejects \<open> { use demo::WIDTH as w; w() } \<close> \<open> which cannot be used as a call \<close>
urust_expr_rejects \<open> (use demo::value; 1) \<close> \<open> use declarations require an enclosing block \<close>
urust_expr_rejects \<open> assert!(use demo::value; true) \<close> \<open> use declarations require an enclosing block \<close>
urust_expr_rejects \<open> UsePacket { sample: use demo::value; 1 } \<close> \<open> use declarations require an enclosing block \<close>
urust_expr_rejects \<open> match 1u32 { _ if use demo::value; true => 1, _ => 0 } \<close>
  \<open> use declarations require an enclosing block \<close>

context use_command_locale
begin

urust_expr_rejects \<open> { use use_command_parameter as fixed_alias; 1 } \<close>
  \<open> unknown import target "use_command_parameter" \<close>

end

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
  val ctxt = \<^context>
in
  val _ = command_rejects thy "body imports do not type the signature" "unknown Rust type \"LocalShortSig\""
    ("urust_fn _ " ^ cartouche " fn bad(x: LocalShortSig) { use demo::Short as LocalShortSig; } ")
  val escaped =
    Parser_Test_Elaboration.expression ctxt
      (Parser_Lex_Util.text_source "{ { use demo::value as inner_only; } inner_only() }")
  val _ = require "inner imports do not escape their block"
    (exists_subterm (fn Free ("inner_only", _) => true | _ => false) escaped andalso
      not (exists_Const (fn (name, _) => name = \<^const_name>\<open>use_demo_value_impl\<close>) escaped))
  val _ = rejects "declaration arguments are not import targets" "unknown import target \"argument\""
    (fn () => Parser_Test_Elaboration.expression_with_arguments ctxt [("argument", Position.none)]
      (Parser_Lex_Util.text_source "{ use argument as captured; 1 }"))
  val _ = require "block imports leave no persistent binding"
    (is_none (S.lookup ctxt S.Value_Namespace "local_inc") andalso
      is_none (S.lookup ctxt S.Value_Namespace "body_inc"))
end
\<close>


section\<open> Editor integration and replay \<close>

text\<open>
An import declaration reports keyword and delimiter markup, a definition and tooltip for each
alias, and references to its exact target registrations without selecting an overload. Each later
alias occurrence keeps its backend and type navigation and makes the import declaration its final
navigation target. Failed declarations replay no semantic reports, and replaying pretty output
or importing changes no registry inventory.
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>

  fun markup_reports text =
    let
      val (result, chunks) =
        Parser_Test_Reports.chunks (fn () =>
          Exn.result (fn () => run_from (initial thy) "use-editor" text) ())
      (* The capture prepends each output chunk; restore emission order. *)
      val markups =
        maps YXML.parse_body (rev chunks)
        |> map_filter (fn XML.Elem (markup, _) => SOME markup | XML.Text _ => NONE)
    in (result, markups) end

  fun property name ((_, props): Markup.T) = AList.lookup (op =) props name
  fun occurrence text needle index =
    let
      fun find start remaining =
        let
          val (prefix, rest) = Substring.position needle (Substring.extract (text, start, NONE))
          val _ = if Substring.isEmpty rest then error ("missing " ^ needle) else ()
          val position = start + size (Substring.string prefix)
        in if remaining = 0 then position else find (position + size needle) (remaining - 1) end
    in 1 + length (Symbol.explode (String.substring (text, 0, find 0 index))) end
  fun at offset markup = property "offset" markup = SOME (Value.print_int offset)
  fun entity_kind (markup as (name, _): Markup.T) =
    if name = Markup.entityN then property Markup.kindN markup else NONE
  fun entities markups offset = filter (fn markup => at offset markup andalso is_some (entity_kind markup)) markups
  fun kinds markups offset = map (the o entity_kind) (entities markups offset)
  fun last_kind markups offset = try List.last (kinds markups offset)
  fun has markups offset name = exists (fn markup as (markup_name, _) => markup_name = name andalso at offset markup) markups
  fun definition markups offset =
    exists (fn markup => entity_kind markup = SOME "urust_import" andalso is_some (property "def" markup))
      (entities markups offset)
  fun import_reference_target markups offset =
    entities markups offset
    |> filter (fn markup => entity_kind markup = SOME "urust_import" andalso is_some (property "ref" markup))
    |> map (property "def_offset")

  val call_text =
    "urust_use " ^ cartouche " use demo::increment as nav_inc; " ^ "\n" ^
    "urust_expr nav_call " ^ cartouche " nav_inc(3) "
  val (call_result, call_markups) = markup_reports call_text
  val _ = require "navigation fixture succeeded" (is_some (Exn.get_res call_result))
  val alias = occurrence call_text "nav_inc" 0
  val use_site = occurrence call_text "nav_inc" 1
  val _ = require "alias definition" (definition call_markups alias)
  val _ = require "alias tooltip" (has call_markups alias Markup.typingN)
  val _ = require "use and as keywords"
    (has call_markups (occurrence call_text "use demo" 0) Markup.keyword1N andalso
      has call_markups (occurrence call_text "as nav_inc" 0) Markup.keyword1N)
  val _ = require "path and item delimiters"
    (has call_markups (occurrence call_text "::" 0) Markup.delimiterN andalso
      has call_markups (occurrence call_text ";" 0) Markup.delimiterN)
  val _ = require "target registration reference"
    (member (op =) (kinds call_markups (occurrence call_text "increment" 0)) Micro_Rust_Names.notationN)
  val _ = require "use site retains backend navigation"
    (member (op =) (kinds call_markups use_site) Micro_Rust_Names.notationN)
  val _ = require ("import declaration is the final use-site target: " ^
      commas (kinds call_markups use_site))
    (last_kind call_markups use_site = SOME "urust_import" andalso
      import_reference_target call_markups use_site = [SOME (Value.print_int alias)])

  val block_text = "urust_expr nav_block " ^ cartouche " { use demo::increment as blk; blk(1) } "
  val (_, block_markups) = markup_reports block_text
  val _ = require "block alias definition" (definition block_markups (occurrence block_text "blk" 0))
  val _ = require "block alias final target"
    (last_kind block_markups (occurrence block_text "blk" 1) = SOME "urust_import")

  val type_text =
    "urust_use " ^ cartouche " use demo::Width as NavWord; " ^ "\n" ^
    "urust_fn _ " ^ cartouche " fn nav_sig(x: NavWord) {} "
  val (_, type_markups) = markup_reports type_text
  val type_site = occurrence type_text "NavWord" 1
  val _ = require "type alias occurrence keeps its mapping and ends at the import"
    (member (op =) (kinds type_markups type_site) "micro_rust_type_mapping" andalso
      last_kind type_markups type_site = SOME "urust_import")

  val self_text = "urust_use " ^ cartouche " use UseChoice::{self as NavSelection}; "
  val (_, self_markups) = markup_reports self_text
  val self_pos = occurrence self_text "self" 0
  val _ = require "grouped self keyword and enum reference"
    (has self_markups self_pos Markup.keyword1N andalso
      member (op =) (kinds self_markups self_pos) "urust_item")

  val overload_text =
    "urust_use " ^ cartouche " use demo::ZERO as NavZero; " ^ "\n" ^
    "urust_expr nav_zero " ^ cartouche " NavZero + 1u64 "
  val (overload_result, overload_markups) = markup_reports overload_text
  val overload_ctxt = Toplevel.context_of (Exn.release overload_result)
  val wide_serial =
    Micro_Rust_Names.lookups overload_ctxt Micro_Rust_Names.NLiteral "demo::ZERO"
    |> filter (fn {hol_term, ...} : Micro_Rust_Names.entry =>
         Term.aconv_untyped (hol_term, \<^term>\<open>use_demo_zero_wide\<close>))
    |> map #serial
  val target = occurrence overload_text "ZERO" 0
  val _ = require "import declaration reports every candidate registration"
    (length (filter (fn kind => kind = Micro_Rust_Names.notationN) (kinds overload_markups target)) = 2)
  val overload_site = occurrence overload_text "NavZero" 1
  val selected =
    entities overload_markups overload_site
    |> filter (fn markup => entity_kind markup = SOME Micro_Rust_Names.notationN)
    |> map (property "ref")
  val _ = require "typed dispatch still selects the overload before the import target"
    (try List.last selected = SOME (Option.map Value.print_int (try hd wide_serial)) andalso
      last_kind overload_markups overload_site = SOME "urust_import")

  val rejected_text = "urust_use " ^ cartouche " use demo::{value as nav_rejected, Missing}; "
  val (rejected_result, rejected_markups) = markup_reports rejected_text
  val _ = require "rejected declaration fails" (is_none (Exn.get_res rejected_result))
  val _ = require "rejected declaration replays no semantic reports"
    (not (exists (is_some o entity_kind) rejected_markups))
  val rejected_block_text =
    "urust_expr nav_rejected_block " ^
      cartouche " { use demo::value as nav_dup; use demo::WIDTH as nav_dup; 1 } "
  val (rejected_block_result, rejected_block_markups) = markup_reports rejected_block_text
  val _ = require "rejected block import replays no import reports"
    (is_none (Exn.get_res rejected_block_result) andalso
      not (exists (fn markup => entity_kind markup = SOME "urust_import") rejected_block_markups))
in
  val _ = ()
end
\<close>

ML_val\<open>
local
  open Parser_Use_Test
  val thy = \<^theory>
  fun inventory ctxt =
    (length (URust_Item_Scope.dump_types ctxt), length (URust_Item_Scope.dump_constructors ctxt),
     length (URust_Item_Scope.dump_functions ctxt), length (URust_Type_Mappings.dump ctxt),
     length (Micro_Rust_Names.dump ctxt))
  fun output_of action =
    let
      val captured = Synchronized.var "use_pretty_output" ([]: string list)
      fun capture chunks = Synchronized.change captured (append chunks)
      val result =
        Parser_Test_Report_Lock.run (fn () =>
          Unsynchronized.setmp Private_Output.writeln_fn capture
            (Unsynchronized.setmp Private_Output.writeln_urgent_fn capture action) ())
    in (result, Synchronized.value captured |> map (XML.content_of o YXML.parse_body) |> cat_lines) end
  val start_state = initial thy
  val imported = run_from start_state "use-inventory" ("urust_use " ^ cartouche " use demo::value as inventory_value; ")
  val _ = require "imports leave item, type and notation registries unchanged"
    (inventory (Toplevel.context_of start_state) = inventory (Toplevel.context_of imported) andalso
      length (S.dump_persistent (Toplevel.context_of imported)) =
        length (S.dump_persistent (Toplevel.context_of start_state)) + 1)
  val (replayed, output) =
    output_of (fn () =>
      run_from imported "use-pretty"
        ("urust_fn [pretty, verbosity = 2] _ " ^
          cartouche " fn pretty_imports(x: u32) -> u32 { use demo::increment as step; step(inventory_value()) } "))
  val _ = require "pretty replay prints the body import"
    (String.isSubstring "use demo::increment as step;" output)
  val _ = require "pretty replay leaves every inventory unchanged"
    (inventory (Toplevel.context_of replayed) = inventory (Toplevel.context_of imported) andalso
      length (S.dump_persistent (Toplevel.context_of replayed)) =
        length (S.dump_persistent (Toplevel.context_of imported)))
in
  val _ = ()
end
\<close>

end
