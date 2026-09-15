theory Parser_Impl_Cast_Aliases
  imports Parser_Impl_AST
  keywords "urust_cast_alias" :: thy_decl
begin

section\<open> Scoped cast-target aliases \<close>

text\<open>
Named cast targets are explicit context declarations. Isabelle bundles may capture these
declarations and replay them in a confined context, providing an intentional approximation of a Rust
file or module scope without changing the primitive cast semantics.
\<close>

ML\<open>
signature URUST_CAST_ALIASES =
sig
  val resolve:
    Proof.context ->
      URust_AST.source_cast_target -> URust_AST.cast_target
end

structure URust_Cast_Aliases :> URUST_CAST_ALIASES =
struct
  open URust_AST

  val aliasN = "micro_rust_cast_alias"

  type entry =
    {target: cast_target, declaration_pos: Position.T, serial: serial}

  (* The serial is allocated at the original declaration, before any bundle replay. Keeping the
     earlier identity makes identical registrations idempotent and context merges commutative. *)
  fun target_name (CT_Unsigned UT_U8) = "u8"
    | target_name (CT_Unsigned UT_U16) = "u16"
    | target_name (CT_Unsigned UT_U32) = "u32"
    | target_name (CT_Unsigned UT_U64) = "u64"
    | target_name (CT_Unsigned UT_Usize) = "usize"
    | target_name (CT_Signed ST_I32) = "i32"
    | target_name (CT_Signed ST_I64) = "i64"
    | target_name (CT_RawPointer (RPM_Const, target)) =
        "*const " ^ target_name (CT_Unsigned target)
    | target_name (CT_RawPointer (RPM_Mut, target)) =
        "*mut " ^ target_name (CT_Unsigned target)

  fun ordered_entries (left: entry, right: entry) =
    if #serial left <= #serial right then (left, right)
    else (right, left)

  fun conflict alias entries =
    let
      val (first, second) = ordered_entries entries
    in
      error
        ("urust_cast_alias: conflicting active definitions for " ^
          quote alias ^ "\n  " ^
          quote (target_name (#target first)) ^
          Position.here (#declaration_pos first) ^ "\n  " ^
          quote (target_name (#target second)) ^
          Position.here (#declaration_pos second))
    end

  fun join_entry alias (left: entry, right: entry) =
    if #target left = #target right
    then #1 (ordered_entries (left, right))
    else conflict alias (left, right)

  (* Generic_Data contains only aliases active in the current context. A bundle definition records
     the declaration callback without leaking that callback into its surrounding theory context. *)
  structure Data = Generic_Data
  (
    type T = entry Symtab.table
    val empty = Symtab.empty
    fun merge (left, right) =
      Symtab.join join_entry (left, right)
  )

  fun add_entry alias entry =
    Data.map
      (fn table =>
        (case Symtab.lookup table alias of
           NONE => Symtab.update (alias, entry) table
         | SOME active =>
             Symtab.update
               (alias, join_entry alias (active, entry))
               table))

  fun ascii_letter character =
    (#"A" <= character andalso character <= #"Z") orelse
    (#"a" <= character andalso character <= #"z")

  fun alias_identifier name =
    (case String.explode name of
       [] => false
     | first :: rest =>
         (ascii_letter first orelse first = #"_") andalso
         forall
           (fn character =>
             ascii_letter character orelse Char.isDigit character orelse
             character = #"_" orelse character = #"'")
           rest)

  val reserved_segments =
    ["true", "false", "as", "u8", "u16", "u32", "u64", "usize",
     "i32", "i64", "let", "const", "return", "if", "else", "fuel",
     "while", "loop", "for", "in", "unsafe", "match", "match_switch",
     "match_case", "mut"]

  fun split_alias_path name =
    let
      fun split input =
        let
          val (segment, rest) =
            Substring.position "::" input
        in
          if Substring.isEmpty rest
          then [Substring.string segment]
          else
            Substring.string segment ::
              split (Substring.triml 2 rest)
        end
    in split (Substring.full name) end

  fun check_alias_name (name, pos) =
    let
      val segments = split_alias_path name
      fun invalid reason =
        error
          ("urust_cast_alias: invalid alias path " ^ quote name ^
            " (" ^ reason ^ ")" ^ Position.here pos)
      val _ =
        if null segments orelse exists (fn segment => segment = "") segments
        then invalid "expected a nonempty qualified path"
        else ()
      val _ =
        if forall alias_identifier segments then ()
        else invalid "expected parser identifiers separated by `::`"
      val _ =
        (case find_first (member (op =) reserved_segments) segments of
           NONE => ()
         | SOME segment =>
             invalid
               ("reserved segment " ^ quote segment ^
                 " cannot occur in a cast-target alias"))
    in name end

  fun unsigned_target "u8" = SOME UT_U8
    | unsigned_target "u16" = SOME UT_U16
    | unsigned_target "u32" = SOME UT_U32
    | unsigned_target "u64" = SOME UT_U64
    | unsigned_target "usize" = SOME UT_Usize
    | unsigned_target _ = NONE

  fun parse_target (raw, pos) =
    let
      val tokens =
        String.tokens
          (fn character =>
            character = #" " orelse character = #"\t" orelse
            character = #"\r" orelse character = #"\n")
          raw
      fun invalid () =
        error
          ("urust_cast_alias: malformed primitive cast target " ^
            quote raw ^
            " (expected u8, u16, u32, u64, usize, i32, i64, " ^
            "*const u8/u16/u32/u64/usize, or " ^
            "*mut u8/u16/u32/u64/usize)" ^
            Position.here pos)
      fun pointer mutability width =
        (case unsigned_target width of
           SOME target => CT_RawPointer (mutability, target)
         | NONE => invalid ())
    in
      (case tokens of
         ["u8"] => CT_Unsigned UT_U8
       | ["u16"] => CT_Unsigned UT_U16
       | ["u32"] => CT_Unsigned UT_U32
       | ["u64"] => CT_Unsigned UT_U64
       | ["usize"] => CT_Unsigned UT_Usize
       | ["i32"] => CT_Signed ST_I32
       | ["i64"] => CT_Signed ST_I64
       | ["*const", width] => pointer RPM_Const width
       | ["*", "const", width] => pointer RPM_Const width
       | ["*mut", width] => pointer RPM_Mut width
       | ["*", "mut", width] => pointer RPM_Mut width
       | _ => invalid ())
    end

  fun report_declaration ctxt alias pos identity =
    (Context_Position.report ctxt pos
       (Position.make_entity_markup {def = true} identity aliasN
         (alias, pos));
     Context_Position.report_text ctxt pos Markup.typing
       "uRust cast-target alias declaration")

  fun report_use ctxt alias path
      ({declaration_pos, serial, ...}: entry) =
    let
      val segments = path_segments path
      val _ =
        List.app
          (fn segment =>
            let val (_, pos) = segment_identifier segment in
              Context_Position.report ctxt pos Markup.keyword3;
              Context_Position.report_text ctxt pos Markup.typing
                "uRust cast-target alias"
            end)
          segments
      val (_, terminal_pos) = segment_identifier (final_segment path)
    in
      Context_Position.report ctxt terminal_pos
        (Position.make_entity_markup {def = false} serial aliasN
          (alias, declaration_pos))
    end

  fun reject_generics path =
    (case
        get_first
          (fn segment =>
            (case segment_generic_args segment of
               NONE => NONE
             | SOME (Generic_Args (_, pos)) => SOME pos))
          (path_segments path) of
       NONE => ()
     | SOME pos =>
         error
           ("urust_expr: generic arguments are not allowed in " ^
             "cast-target aliases" ^ Position.here pos))

  fun resolve _ (SCT_Primitive target) = target
    | resolve ctxt (SCT_Named path) =
        let
          val _ =
            if is_primitive_path path then
              error
                ("urust_expr: primitive associated-item paths cannot be " ^
                  "cast-target aliases" ^
                  Position.here (path_position path))
            else ()
          val _ = reject_generics path
          val alias = render_path path
        in
          (case Symtab.lookup (Data.get (Context.Proof ctxt)) alias of
             NONE =>
               error
                 ("urust_expr: unknown cast-target alias " ^
                   quote alias ^ Position.here (path_position path))
           | SOME (entry as {target, ...}) =>
               (report_use ctxt alias path entry; target))
        end

  fun declare_alias ((raw_alias, alias_pos), target_spec) lthy =
    let
      val alias = check_alias_name (raw_alias, alias_pos)
      val target = parse_target target_spec
      (* Allocate and report the stable entity before Local_Theory captures the declaration for
         bundle replay; every later use can therefore link back to this source declaration. *)
      val identity = serial ()
      val entry =
        {target = target, declaration_pos = alias_pos, serial = identity}
      val _ = report_declaration lthy alias alias_pos identity
    in
      Local_Theory.declaration
        {pervasive = false, syntax = true, pos = alias_pos}
        (fn _ => add_entry alias entry)
        lthy
    end

  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>urust_cast_alias\<close>
      "declare a context-local alias for a primitive uRust cast target"
      ((Parse.string_position --| \<^keyword>\<open>=\<close>) --
        Parse.string_position >> declare_alias)
end
\<close>

end
