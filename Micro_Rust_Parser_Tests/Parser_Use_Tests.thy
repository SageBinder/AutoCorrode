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
    (aliases = ["left_value", "merged_width", "right_value", "shared_increment"])
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

end
