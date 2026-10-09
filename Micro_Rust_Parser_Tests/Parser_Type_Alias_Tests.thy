theory Parser_Type_Alias_Tests
  imports Parser_Type_Alias_Registry_Tests Parser_Type_Alias_Syntax_Tests
    Parser_Cast_Target_Aliases_Tests
begin

urust_type_alias \<open> type CommandWidth = u16; \<close>
urust_type_alias \<open> type CommandChain = CommandWidth; \<close>
urust_type_alias "command_types::QualifiedWidth" \<open> type QualifiedWidth = CommandChain; \<close>
urust_type_alias \<open> type CommandIdentity<T> = T; \<close>
urust_type_alias \<open> type CommandPair<T> = (T, T); \<close>
urust_type_alias \<open> type CommandPtr<T> = *const T; \<close>
urust_type_alias \<open> type CommandSigned = i32; \<close>
urust_type "CommandMapped" = \<open> nat list \<close>
urust_type_alias \<open> type CommandMappedAlias = CommandMapped; \<close>

urust_fn \<open>
  fn CommandNarrow(value: u32) -> command_types::QualifiedWidth {
    value as CommandIdentity<CommandChain>
  }
\<close>

urust_fn \<open>
  fn CommandPairs(left: CommandIdentity<u8>, right: CommandIdentity<u16>) -> (u8, u16) {
    (left, right)
  }
\<close>

urust_fn \<open>
  fn CommandPairIdentity(value: CommandPair<u8>) -> (u8, u8) {
    value
  }
\<close>

urust_fn \<open>
  fn CommandMappedIdentity(value: CommandMappedAlias) -> CommandMapped {
    value
  }
\<close>

urust_fn \<open>
  fn CommandPointerIdentity(value: CommandPtr<u8>) -> *const u8 {
    value
  }
\<close>

urust_expr command_generic_cast \<open> 5u32 as CommandIdentity<u16> \<close>
urust_expr command_generic_cast_expanded \<open> 5u32 as u16 \<close>
urust_expr command_signed_cast \<open> 5u64 as CommandSigned \<close>
urust_expr command_signed_cast_expanded \<open> 5u64 as i32 \<close>

lemma command_generic_cast_equal:
  \<open> command_generic_cast = command_generic_cast_expanded \<close>
  unfolding command_generic_cast_def command_generic_cast_expanded_def by (rule refl)

lemma command_signed_cast_equal:
  \<open> command_signed_cast = command_signed_cast_expanded \<close>
  unfolding command_signed_cast_def command_signed_cast_expanded_def by (rule refl)

ML_val\<open>
local
  val thy = \<^theory>
  val _ =
    if Keyword.is_command (Thy_Header.get_keywords thy) "urust_cast_alias"
    then error "retired urust_cast_alias keyword remains installed"
    else ()
  val retired = Exn.result (fn () =>
    Outer_Syntax.parse_text thy (K thy)
      (Position.line_file 1 "retired-type-alias-command")
      "urust_cast_alias \"RetiredWidth\" = \"u16\""
    |> (fn transitions => fold (Toplevel.command_exception false)
      transitions (Toplevel.make_state (SOME thy)))) ()
  val _ =
    (case retired of
       Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn else ()
     | Exn.Res _ => error "retired urust_cast_alias command accepted")
  val pointer_type =
    Consts.the_constraint (Proof_Context.consts_of \<^context>)
      \<^const_name>\<open>command_pointer_identity\<close>
  val _ =
    if length (Term.add_tvarsT (hd (binder_types pointer_type)) []) = 2 then ()
    else error "pointer alias signature did not generalize both backend parameters"
in
  val _ = writeln "alias command and existing primitive cast equivalences passed"
end
\<close>

section\<open> Command failures, dependency capture and recovery \<close>

urust_type "CommandOrdered<'value>" = \<open> 'value::linorder list \<close>
urust_type_alias \<open> type CommandSorted<T> = CommandOrdered<T>; \<close>
urust_type_alias \<open> type CommandIdentity<Value> = Value; \<close>

ML_val\<open>
local
  val thy = \<^theory>
  val ctxt = \<^context>
  fun require message condition =
    if condition then () else error ("alias command audit: " ^ message)
  fun cartouche text = Symbol.open_ ^ " " ^ text ^ " " ^ Symbol.close
  fun command file text =
    Outer_Syntax.parse_text thy (K thy)
      (Position.make0 1 1 0 "" file ""
        |> Position.copy_id (Position.thread_data ())) text
    |> (fn transitions => fold (Toplevel.command_exception false)
         transitions (Toplevel.make_state (SOME thy)))
  fun declaration text = "urust_type_alias " ^ cartouche text
  fun reject (label, text, expected) =
    (case Exn.result (fn () => command label text) () of
       Exn.Res _ => error ("invalid alias command accepted: " ^ label)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else require ("wrong diagnostic: " ^ label)
           (String.isSubstring expected (Runtime.exn_message exn)))
  val _ = List.app reject
    [("alias-duplicate", declaration "type Duplicate<T, T> = T;",
       "duplicate type parameter"),
     ("alias-unused", declaration "type Unused<T> = u16;",
       "unused type parameters"),
     ("alias-recursive", declaration "type Recursive = Recursive;",
       "recursive alias dependency"),
     ("alias-unknown", declaration "type Unknown = UnknownDependency;",
       "unknown Rust type"),
     ("alias-arity", declaration "type WrongArity = CommandIdentity<u8, u16>;",
       "generic arities"),
     ("alias-sort", declaration ("type WrongSort = CommandSorted<" ^
        "\<tau>" ^ cartouche "nat \<Rightarrow> nat" ^ ">;"),
       "does not satisfy sort"),
     ("alias-variable", declaration ("type FreeEscape = \<tau>" ^
        cartouche "'unrelated" ^ ";"), "unrelated HOL type variables"),
     ("alias-terminal", "urust_type_alias \"types::Different\" " ^
        cartouche "type Declared = u16;", "must match item name"),
     ("alias-manual-collision", declaration "type CommandMapped = u16;",
       "alias and direct/generated mapping collide"),
     ("manual-alias-collision", "urust_type \"CommandWidth\" = " ^
        cartouche "16 word", "alias and direct/generated mapping collide"),
     ("generated-alias-collision", "urust_datatype " ^
        cartouche "struct CommandWidth(u16);",
       "alias and direct/generated mapping collide"),
     ("alias-mutability-conflict", declaration "type CommandPtr<T> = *mut T;",
       "different Rust meanings")]
  val alias = the (URust_Type_Mappings.lookup ctxt "CommandChain")
  val _ = require "dependency was not captured as a checked HOL template"
    (URust_Type_Mappings.entry_template alias = \<^typ>\<open>16 word\<close>)
  val _ = reject
    ("captured-dependency-conflict", declaration "type CommandWidth = u8;",
     "conflicting active mappings")
  val recovered =
    command "alias-command-recovery" (declaration "type RecoveredAlias = CommandChain;")
    |> Toplevel.context_of
  val _ = require "recovery changed captured meaning"
    (Parser_Test_Elaboration.expression recovered
       (Parser_Lex_Util.text_source "5u32 as RecoveredAlias")
     aconv
     Parser_Test_Elaboration.expression ctxt
       (Parser_Lex_Util.text_source "5u32 as u16"))
  val _ = require "failed declarations installed a registry entry"
    (forall (is_none o URust_Type_Mappings.lookup ctxt)
      ["Duplicate", "Unused", "Recursive", "Unknown", "WrongArity",
       "WrongSort", "FreeEscape", "Declared"])
  val (navigation_state, markup) =
    Parser_Test_Reports.markup (fn () =>
      command "alias-dependency-navigation"
        (declaration "type NavigationAlias<T> = CommandIdentity<T>;"))
  fun entities property alias reports =
    map_filter
      (fn (name, props) =>
        if name = Markup.entityN andalso
           Properties.get props Markup.kindN = SOME "micro_rust_type_mapping" andalso
           Properties.get props Markup.nameN = SOME alias
        then Properties.get props property else NONE)
      reports
  val identity = the (URust_Type_Mappings.lookup ctxt "CommandIdentity")
  val installed =
    the (URust_Type_Mappings.lookup (Toplevel.context_of navigation_state) "NavigationAlias")
  val _ = require "alias declaration lost its entity identity"
    (entities Markup.defN "NavigationAlias" markup =
      [string_of_int (URust_Type_Mappings.entry_identity installed)])
  val _ = require "alias dependency did not navigate to its captured declaration"
    (entities Markup.refN "CommandIdentity" markup =
      [string_of_int (URust_Type_Mappings.entry_identity identity)])
  val _ = require "alias parameters lost their declaration and use markup"
    (length (filter (fn (name, _) => name = Markup.tfreeN) markup) >= 2)
  val (_, failed_markup) =
    Parser_Test_Reports.markup (fn () =>
      Exn.result (fn () =>
        command "alias-failed-navigation"
          (declaration "type FailedNavigation<T> = (CommandIdentity<T>, MissingType);")) ())
  val _ = require "failed declaration replayed successful semantic reports"
    (null (entities Markup.defN "FailedNavigation" failed_markup) andalso
     null (entities Markup.refN "CommandIdentity" failed_markup))
in
  val _ = writeln "alias command failures, capture and recovery passed"
end
\<close>

section\<open> Definition-time capture across dependency scopes \<close>

bundle capture_dependency_left
begin
urust_type "CaptureDependency" = \<open> 16 word \<close>
end

bundle capture_dependency_right
begin
urust_type "CaptureDependency" = \<open> 8 word \<close>
end

context includes capture_dependency_left
begin
urust_type_alias \<open> type CapturedDependency = CaptureDependency; \<close>
end

context includes capture_dependency_right
begin

ML_val\<open>
  val captured = the (URust_Type_Mappings.lookup \<^context> "CapturedDependency")
  val dependency = the (URust_Type_Mappings.lookup \<^context> "CaptureDependency")
  val _ =
    if URust_Type_Mappings.entry_template captured = \<^typ>\<open>16 word\<close> andalso
       URust_Type_Mappings.entry_template dependency = \<^typ>\<open>8 word\<close>
    then ()
    else error "alias meaning changed with its dependency's active scope"
\<close>

urust_fn \<open>
  fn CapturedWidths(left: CapturedDependency, right: CaptureDependency) -> (u16, u8) {
    (left, right)
  }
\<close>

end

end
