theory Parser_Tests_Cast_Target_Aliases
  imports Parser_Test_Cast_Alias_Fixtures
begin

chapter\<open>Scoped cast-target aliases\<close>

declare [[urust_conformance = false]]
declare [[urust_pp_test = true]]
declare [[urust_verbosity = 0]]

section\<open>Imported bundles remain inactive\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_rejection ctxt text expected =
      (case
          Exn.result
            (Parser_Test_Elaboration.expression ctxt)
            (Parser_Lex_Util.text_source text) of
         Exn.Res term =>
           error
             ("cast-target alias unexpectedly active for " ^ quote text ^
               ": " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if String.isSubstring expected message then ()
               else
                 error
                   ("wrong cast-target alias diagnostic:\n" ^ message ^
                     "\nexpected: " ^ quote expected)
             end)
  in
    val _ =
      expect_rejection \<^context> "0_u64 as U8Alias"
        "unknown cast-target alias"
  end
\<close>

section\<open>Primitive equivalence and grammar composition\<close>

context includes module_cast_aliases
begin

context
  fixes cast_alias_word :: "64 word"
begin

urust_expr cast_alias_u8
  \<open> cast_alias_word as U8Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as u8 \<rbrakk> \<close>

urust_expr cast_alias_u16
  \<open> cast_alias_word as types::U16Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as u16 \<rbrakk> \<close>

urust_expr cast_alias_u32
  \<open> cast_alias_word as U32Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as u32 \<rbrakk> \<close>

urust_expr cast_alias_u64
  \<open> cast_alias_word as U64Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as u64 \<rbrakk> \<close>

urust_expr cast_alias_usize
  \<open> cast_alias_word as UsizeAlias \<close>
  against \<open> \<lbrakk> cast_alias_word as usize \<rbrakk> \<close>

urust_expr cast_alias_i32
  \<open> cast_alias_word as I32Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as i32 \<rbrakk> \<close>

urust_expr cast_alias_i64
  \<open> cast_alias_word as I64Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as i64 \<rbrakk> \<close>

urust_expr cast_alias_chain
  \<open> cast_alias_word as U64Alias as U8Alias as I32Alias \<close>
  against \<open> \<lbrakk> cast_alias_word as u64 as u8 as i32 \<rbrakk> \<close>

urust_expr cast_alias_precedence
  \<open> cast_alias_word as U32Alias + 1_u32 \<close>
  against \<open> \<lbrakk> cast_alias_word as u32 + 1_u32 \<rbrakk> \<close>

urust_expr cast_alias_no_struct
  \<open>
    if cast_alias_word as U32Alias ==
        cast_alias_word as U32Alias {
      cast_alias_word as types::U16Alias
    } else {
      cast_alias_word as types::U16Alias
    }
  \<close>
  against \<open>
    \<lbrakk>
      if cast_alias_word as u32 ==
          cast_alias_word as u32 {
        cast_alias_word as u16
      } else {
        cast_alias_word as u16
      }
    \<rbrakk>
  \<close>

end

context
  fixes cast_alias_raw :: "('address, 'global) gref"
begin

urust_expr cast_alias_const_u8_pointer
  \<open> cast_alias_raw as ConstU8Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *const u8 \<rbrakk> \<close>

urust_expr cast_alias_const_u16_pointer
  \<open> cast_alias_raw as ConstU16Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *const u16 \<rbrakk> \<close>

urust_expr cast_alias_const_u32_pointer
  \<open> cast_alias_raw as ConstU32Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *const u32 \<rbrakk> \<close>

urust_expr cast_alias_const_u64_pointer
  \<open> cast_alias_raw as ConstU64Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *const u64 \<rbrakk> \<close>

urust_expr cast_alias_const_usize_pointer
  \<open> cast_alias_raw as ConstUsizePointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *const usize \<rbrakk> \<close>

urust_expr cast_alias_mut_u8_pointer
  \<open> cast_alias_raw as MutU8Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *mut u8 \<rbrakk> \<close>

urust_expr cast_alias_mut_u16_pointer
  \<open> cast_alias_raw as MutU16Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *mut u16 \<rbrakk> \<close>

urust_expr cast_alias_mut_u32_pointer
  \<open> cast_alias_raw as MutU32Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *mut u32 \<rbrakk> \<close>

urust_expr cast_alias_mut_u64_pointer
  \<open> cast_alias_raw as MutU64Pointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *mut u64 \<rbrakk> \<close>

urust_expr cast_alias_mut_usize_pointer
  \<open> cast_alias_raw as MutUsizePointer \<close>
  against \<open> \<lbrakk> cast_alias_raw as *mut usize \<rbrakk> \<close>

end

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun parse text =
      (case
          URust_Parser.parse_source ctxt
            (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "cast-target alias audit: empty parse")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun assert message condition =
      if condition then ()
      else error ("cast-target alias audit: " ^ message)
  in
    val _ =
      (case parse "value as types::U16Alias" of
         UE_Cast
           (UE_Path _,
            SCT_Named path, _) =>
           assert "named cast target lost its exact qualified path"
             (render_path path = "types::U16Alias")
       | _ =>
           error
             "cast-target alias audit: named cast AST shape changed")
    val _ =
      assert "unchecked integral alias changed the generated term"
        (Term.aconv
          (unchecked "value as U8Alias",
           unchecked "value as u8"))
    val _ =
      assert "unchecked qualified alias changed the generated term"
        (Term.aconv
          (unchecked "value as types::U16Alias",
           unchecked "value as u16"))
    val _ =
      assert "unchecked pointer alias changed the generated term"
        (Term.aconv
          (unchecked "value as MutUsizePointer",
           unchecked "value as *mut usize"))
    val _ =
      assert "unchecked alias chain changed the generated term"
        (Term.aconv
          (unchecked "value as U64Alias as U8Alias as I32Alias",
           unchecked "value as u64 as u8 as i32"))
  end
\<close>

ML_val\<open>
  local
    fun plain_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))
        handle Fail _ => Runtime.exn_message exn

    fun expect_failure label action expected =
      (case Exn.result action () of
         Exn.Res _ =>
           error
             ("cast-target alias " ^ label ^
               " unexpectedly succeeded")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = plain_message exn in
               if String.isSubstring expected message then ()
               else
                 error
                   ("cast-target alias " ^ label ^
                     " produced the wrong diagnostic:\n" ^ message)
             end)

    val _ =
      expect_failure "generic use"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source
              "0_u64 as U8Alias::<Width>"))
        "generic arguments are not allowed in cast-target aliases"
  in
    val _ = ()
  end
\<close>

end

section\<open>Confined direct and locale activation\<close>

experiment
begin

urust_cast_alias "ExperimentWidth" = "u32"

urust_expr cast_alias_direct_activation
  \<open> 0_u64 as ExperimentWidth \<close>
  against \<open> \<lbrakk> 0_u64 as u32 \<rbrakk> \<close>

end

context cast_alias_scope opening module_cast_aliases
begin

urust_expr cast_alias_locale_use
  \<open> scope_word as types::U16Alias \<close>
  against \<open> \<lbrakk> scope_word as u16 \<rbrakk> \<close>

end

context cast_alias_scope
begin

ML_val\<open>
  local
    val result =
      Exn.result
        (Parser_Test_Elaboration.expression \<^context>)
        (Parser_Lex_Util.text_source
          "scope_word as types::U16Alias")
  in
    val _ =
      (case result of
         Exn.Res term =>
           error
             ("cast-target alias permanently modified its locale: " ^
               Syntax.string_of_term \<^context> term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             if String.isSubstring "unknown cast-target alias"
                 (Runtime.exn_message exn)
             then ()
             else Exn.reraise exn)
  end
\<close>

end

ML_val\<open>
  local
    fun rejected text =
      (case
          Exn.result
            (Parser_Test_Elaboration.expression \<^context>)
            (Parser_Lex_Util.text_source text) of
         Exn.Res _ => false
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             String.isSubstring "unknown cast-target alias"
               (Runtime.exn_message exn))
  in
    val _ =
      if rejected "0_u64 as U8Alias" andalso
         rejected "0_u64 as ExperimentWidth"
      then ()
      else
        error
          "cast-target alias remained active after its confined context"
  end
\<close>

section\<open>Conflicts and idempotence\<close>

context includes conflict_u8_aliases
begin

urust_expr cast_alias_conflict_left_alone
  \<open> 0_u64 as SharedWidth \<close>
  against \<open> \<lbrakk> 0_u64 as u8 \<rbrakk> \<close>

end

context includes conflict_u16_aliases
begin

urust_expr cast_alias_conflict_right_alone
  \<open> 0_u64 as SharedWidth \<close>
  against \<open> \<lbrakk> 0_u64 as u16 \<rbrakk> \<close>

end

context includes idempotent_cast_aliases
begin

urust_expr cast_alias_idempotent_registration
  \<open> 0_u64 as StableWidth \<close>
  against \<open> \<lbrakk> 0_u64 as u16 \<rbrakk> \<close>

end

ML_val\<open>
  local
    fun include_bundle ctxt name =
      Bundle.includes
        [(true, Bundle.check ctxt (name, Position.none))]
        ctxt

    fun collect_markup (XML.Text _) result = result
      | collect_markup
          (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    val conflict =
      Exn.result
        (fn () =>
          include_bundle
            (include_bundle \<^context> "conflict_u8_aliases")
            "conflict_u16_aliases")
        ()

    val _ =
      (case conflict of
         Exn.Res _ =>
           error "conflicting cast-target alias bundles were accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val raw_message = Runtime.exn_message exn
               val message =
                 XML.content_of (YXML.parse_body raw_message)
                   handle Fail _ => raw_message
               val positions =
                 maps YXML.parse_body [raw_message]
                 |> (fn trees => fold collect_markup trees [])
                 |> map_filter
                     (fn (name, properties) =>
                       if name = Markup.positionN
                       then SOME properties
                       else NONE)
                 |> distinct (op =)
             in
               if String.isSubstring
                    "conflicting active definitions for \"SharedWidth\""
                    message andalso
                  String.isSubstring "\"u8\"" message andalso
                  String.isSubstring "\"u16\"" message andalso
                  length positions = 2
               then ()
               else
                 error
                   ("conflicting cast-target alias diagnostic did not " ^
                     "report both declarations:\n" ^ message)
             end)

    val repeated_context =
      include_bundle
        (include_bundle \<^context> "idempotent_cast_aliases")
        "idempotent_cast_aliases"
    val _ =
      ignore
        (Parser_Test_Elaboration.expression repeated_context
          (Parser_Lex_Util.text_source
            "0_u64 as StableWidth"))
  in
    val _ = ()
  end
\<close>

section\<open>Declaration and use diagnostics\<close>

ML_val\<open>
  local
    fun run_command source_name command_text () =
      let
        val thy = \<^theory>
        val transitions =
          Outer_Syntax.parse_text thy (K thy)
            (Position.line_file 1 source_name) command_text
      in
        fold (Toplevel.command_exception false) transitions
          (Toplevel.make_state (SOME thy))
      end

    fun assert_rejected source_name command_text expected =
      (case
          Exn.result
            (run_command source_name command_text) () of
         Exn.Res _ =>
           error
             ("invalid cast-target alias declaration was accepted" ^
               Position.here (Position.file source_name))
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn in
               if String.isSubstring expected message andalso
                  String.isSubstring source_name message
               then ()
               else
                 error
                   ("wrong cast-target alias declaration diagnostic:\n" ^
                     message)
             end)

    val _ =
      assert_rejected "cast-alias-chain"
        "urust_cast_alias \"AliasChain\" = \"U8Alias\""
        "malformed primitive cast target"
    val _ =
      assert_rejected "cast-alias-malformed-target"
        "urust_cast_alias \"BrokenPointer\" = \"*const\""
        "malformed primitive cast target"
    val _ =
      assert_rejected "cast-alias-generic-name"
        "urust_cast_alias \"Types::Alias::<Width>\" = \"u16\""
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-empty-segment"
        "urust_cast_alias \"Types::\" = \"u16\""
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-reserved-segment"
        "urust_cast_alias \"Types::u16\" = \"u16\""
        "reserved segment"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val base_ctxt = \<^context>
    val ctxt =
      Bundle.includes
        [(true,
          Bundle.check base_ctxt
            ("module_cast_aliases", Position.none))]
        base_ctxt
    val text =
      "value as U8Alias; value as U8Alias; " ^
      "value as types::U16Alias"
    val start =
      Position.make0 17 4 0 "" ""
        "cast-target-alias-markup"
    val reports =
      Synchronized.var "cast_target_alias_reports" ([]: string list)

    fun capture chunks =
      Synchronized.change reports (append chunks)

    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                let
                  val source =
                    Parser_Lex_Util.positioned_content_source
                      text start
                  val expression =
                    (case URust_Parser.parse_source ctxt source of
                       SOME parsed => parsed
                     | NONE =>
                         error
                           "cast-target alias markup audit: empty parse")
                in
                  ignore
                    (URust_Translate.mk_expression ctxt [] expression)
                end)
              ())
          ())

    fun collect (XML.Text _) result = result
      | collect (XML.Elem (markup, body)) result =
          fold collect body (markup :: result)

    val markup =
      fold collect
        (maps YXML.parse_body (Synchronized.value reports)) []

    fun alias_references alias =
      map_filter
        (fn (name, properties) =>
          if name = Markup.entityN andalso
             Properties.get properties Markup.kindN =
               SOME "micro_rust_cast_alias" andalso
             Properties.get properties Markup.nameN = SOME alias
          then Properties.get properties Markup.refN
          else NONE)
        markup

    fun count_markup name =
      length (filter (fn (actual, _) => actual = name) markup)

    val u8_references = alias_references "U8Alias"
    val qualified_references =
      alias_references "types::U16Alias"
    val _ =
      if length u8_references = 2 andalso
         length (distinct (op =) u8_references) = 1
      then ()
      else
        error
          "cast-target alias uses did not retain one stable declaration identity"
    val _ =
      if length qualified_references = 1 then ()
      else
        error
          "qualified cast-target alias lost its declaration reference"
    val _ =
      if count_markup Markup.keyword3N >= 4 andalso
         count_markup Markup.typingN >= 4
      then ()
      else
        error
          "cast-target alias segments lost semantic or typing markup"
  in
    val _ =
      writeln
        "Scoped cast-target alias term, scope, diagnostic, and markup regressions passed"
  end
\<close>

end
