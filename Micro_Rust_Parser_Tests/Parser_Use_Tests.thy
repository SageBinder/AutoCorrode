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

end
