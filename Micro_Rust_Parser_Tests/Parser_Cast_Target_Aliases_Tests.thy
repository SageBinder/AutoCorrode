theory Parser_Cast_Target_Aliases_Tests
  imports
    Parser_Cast_Alias_Fixtures
begin

chapter\<open> Rust type aliases in cast targets \<close>

declare [[urust_verbosity = 0]]

section\<open> Imported aliases are available \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val alias =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "0_u64 as U8Alias")
    val primitive =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "0_u64 as u8")
  in
    val _ =
      if Term.aconv (alias, primitive) then ()
      else error "imported Rust alias did not retain its declared meaning"
  end
\<close>

section\<open> Primitive equivalence and grammar composition \<close>

context
  fixes cast_alias_word :: "64 word"
begin

urust_expr cast_alias_u8
  \<open> cast_alias_word as U8Alias \<close>

urust_expr cast_alias_u8_primitive
  \<open> cast_alias_word as u8 \<close>

lemma cast_alias_u8_equal:
  \<open> cast_alias_u8 = cast_alias_u8_primitive \<close>
  unfolding cast_alias_u8_def cast_alias_u8_primitive_def
  by (rule refl)

urust_expr cast_alias_u16
  \<open> cast_alias_word as types::U16Alias \<close>

urust_expr cast_alias_u16_primitive
  \<open> cast_alias_word as u16 \<close>

lemma cast_alias_u16_equal:
  \<open> cast_alias_u16 = cast_alias_u16_primitive \<close>
  unfolding cast_alias_u16_def cast_alias_u16_primitive_def
  by (rule refl)

urust_expr cast_alias_u32
  \<open> cast_alias_word as U32Alias \<close>

urust_expr cast_alias_u32_primitive
  \<open> cast_alias_word as u32 \<close>

lemma cast_alias_u32_equal:
  \<open> cast_alias_u32 = cast_alias_u32_primitive \<close>
  unfolding cast_alias_u32_def cast_alias_u32_primitive_def
  by (rule refl)

urust_expr cast_alias_u64
  \<open> cast_alias_word as U64Alias \<close>

urust_expr cast_alias_u64_primitive
  \<open> cast_alias_word as u64 \<close>

lemma cast_alias_u64_equal:
  \<open> cast_alias_u64 = cast_alias_u64_primitive \<close>
  unfolding cast_alias_u64_def cast_alias_u64_primitive_def
  by (rule refl)

urust_expr cast_alias_usize
  \<open> cast_alias_word as UsizeAlias \<close>

urust_expr cast_alias_usize_primitive
  \<open> cast_alias_word as usize \<close>

lemma cast_alias_usize_equal:
  \<open> cast_alias_usize = cast_alias_usize_primitive \<close>
  unfolding cast_alias_usize_def cast_alias_usize_primitive_def
  by (rule refl)

urust_expr cast_alias_i32
  \<open> cast_alias_word as I32Alias \<close>

urust_expr cast_alias_i32_primitive
  \<open> cast_alias_word as i32 \<close>

lemma cast_alias_i32_equal:
  \<open> cast_alias_i32 = cast_alias_i32_primitive \<close>
  unfolding cast_alias_i32_def cast_alias_i32_primitive_def
  by (rule refl)

urust_expr cast_alias_i64
  \<open> cast_alias_word as I64Alias \<close>

urust_expr cast_alias_i64_primitive
  \<open> cast_alias_word as i64 \<close>

lemma cast_alias_i64_equal:
  \<open> cast_alias_i64 = cast_alias_i64_primitive \<close>
  unfolding cast_alias_i64_def cast_alias_i64_primitive_def
  by (rule refl)

urust_expr cast_alias_chain
  \<open> cast_alias_word as U64Alias as U8Alias as I32Alias \<close>

urust_expr cast_alias_chain_primitive
  \<open> cast_alias_word as u64 as u8 as i32 \<close>

lemma cast_alias_chain_equal:
  \<open> cast_alias_chain = cast_alias_chain_primitive \<close>
  unfolding cast_alias_chain_def cast_alias_chain_primitive_def
  by (rule refl)

urust_expr cast_alias_precedence
  \<open> cast_alias_word as U32Alias + 1_u32 \<close>

urust_expr cast_alias_precedence_primitive
  \<open> cast_alias_word as u32 + 1_u32 \<close>

lemma cast_alias_precedence_equal:
  \<open> cast_alias_precedence = cast_alias_precedence_primitive \<close>
  unfolding cast_alias_precedence_def cast_alias_precedence_primitive_def
  by (rule refl)

urust_expr cast_alias_no_struct
  \<open>
    if cast_alias_word as U32Alias ==
        cast_alias_word as U32Alias {
      cast_alias_word as types::U16Alias
    } else {
      cast_alias_word as types::U16Alias
    }
  \<close>

urust_expr cast_alias_no_struct_primitive
  \<open>
      if cast_alias_word as u32 ==
          cast_alias_word as u32 {
        cast_alias_word as u16
      } else {
        cast_alias_word as u16
      }

  \<close>

lemma cast_alias_no_struct_equal:
  \<open> cast_alias_no_struct = cast_alias_no_struct_primitive \<close>
  unfolding cast_alias_no_struct_def cast_alias_no_struct_primitive_def
  by (rule refl)

end

context
  fixes cast_alias_word :: "64 word"
    and cast_alias_length :: "64 word"
begin

urust_expr cast_alias_repeats
  \<open>
    ([cast_alias_word as types::U16Alias; (1 + 1) as usize],
     [const { cast_alias_word as U8Alias }; 3 as usize],
     [cast_alias_word as U32Alias; cast_alias_length],
     [const { cast_alias_word as types::U16Alias }; cast_alias_length as usize])
  \<close>

urust_expr cast_alias_repeats_primitive
  \<open>
    ([cast_alias_word as u16; (1 + 1) as usize],
     [const { cast_alias_word as u8 }; 3 as usize],
     [cast_alias_word as u32; cast_alias_length],
     [const { cast_alias_word as u16 }; cast_alias_length as usize])
  \<close>

lemma cast_alias_repeats_equal:
  \<open> cast_alias_repeats = cast_alias_repeats_primitive \<close>
  unfolding cast_alias_repeats_def cast_alias_repeats_primitive_def
  by (rule refl)

end

urust_expr_rejects \<open> [0u64 as U8Alias; 2 as UsizeAlias] \<close>
  \<open> array repeat length supports only \<close>

urust_expr_rejects \<open> [const { 0u64 as U8Alias }; 2 as UsizeAlias] \<close>
  \<open> array repeat length supports only \<close>

context
  fixes cast_alias_raw :: "('address, 'global) gref"
begin

urust_expr cast_alias_const_u8_pointer
  \<open> cast_alias_raw as ConstU8Pointer \<close>

urust_expr cast_alias_const_u8_pointer_primitive
  \<open> cast_alias_raw as *const u8 \<close>

lemma cast_alias_const_u8_pointer_equal:
  \<open> cast_alias_const_u8_pointer = cast_alias_const_u8_pointer_primitive \<close>
  unfolding cast_alias_const_u8_pointer_def cast_alias_const_u8_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u16_pointer
  \<open> cast_alias_raw as ConstU16Pointer \<close>

urust_expr cast_alias_const_u16_pointer_primitive
  \<open> cast_alias_raw as *const u16 \<close>

lemma cast_alias_const_u16_pointer_equal:
  \<open> cast_alias_const_u16_pointer = cast_alias_const_u16_pointer_primitive \<close>
  unfolding cast_alias_const_u16_pointer_def cast_alias_const_u16_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u32_pointer
  \<open> cast_alias_raw as ConstU32Pointer \<close>

urust_expr cast_alias_const_u32_pointer_primitive
  \<open> cast_alias_raw as *const u32 \<close>

lemma cast_alias_const_u32_pointer_equal:
  \<open> cast_alias_const_u32_pointer = cast_alias_const_u32_pointer_primitive \<close>
  unfolding cast_alias_const_u32_pointer_def cast_alias_const_u32_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_u64_pointer
  \<open> cast_alias_raw as ConstU64Pointer \<close>

urust_expr cast_alias_const_u64_pointer_primitive
  \<open> cast_alias_raw as *const u64 \<close>

lemma cast_alias_const_u64_pointer_equal:
  \<open> cast_alias_const_u64_pointer = cast_alias_const_u64_pointer_primitive \<close>
  unfolding cast_alias_const_u64_pointer_def cast_alias_const_u64_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_const_usize_pointer
  \<open> cast_alias_raw as ConstUsizePointer \<close>

urust_expr cast_alias_const_usize_pointer_primitive
  \<open> cast_alias_raw as *const usize \<close>

lemma cast_alias_const_usize_pointer_equal:
  \<open> cast_alias_const_usize_pointer = cast_alias_const_usize_pointer_primitive \<close>
  unfolding cast_alias_const_usize_pointer_def cast_alias_const_usize_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u8_pointer
  \<open> cast_alias_raw as MutU8Pointer \<close>

urust_expr cast_alias_mut_u8_pointer_primitive
  \<open> cast_alias_raw as *mut u8 \<close>

lemma cast_alias_mut_u8_pointer_equal:
  \<open> cast_alias_mut_u8_pointer = cast_alias_mut_u8_pointer_primitive \<close>
  unfolding cast_alias_mut_u8_pointer_def cast_alias_mut_u8_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u16_pointer
  \<open> cast_alias_raw as MutU16Pointer \<close>

urust_expr cast_alias_mut_u16_pointer_primitive
  \<open> cast_alias_raw as *mut u16 \<close>

lemma cast_alias_mut_u16_pointer_equal:
  \<open> cast_alias_mut_u16_pointer = cast_alias_mut_u16_pointer_primitive \<close>
  unfolding cast_alias_mut_u16_pointer_def cast_alias_mut_u16_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u32_pointer
  \<open> cast_alias_raw as MutU32Pointer \<close>

urust_expr cast_alias_mut_u32_pointer_primitive
  \<open> cast_alias_raw as *mut u32 \<close>

lemma cast_alias_mut_u32_pointer_equal:
  \<open> cast_alias_mut_u32_pointer = cast_alias_mut_u32_pointer_primitive \<close>
  unfolding cast_alias_mut_u32_pointer_def cast_alias_mut_u32_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_u64_pointer
  \<open> cast_alias_raw as MutU64Pointer \<close>

urust_expr cast_alias_mut_u64_pointer_primitive
  \<open> cast_alias_raw as *mut u64 \<close>

lemma cast_alias_mut_u64_pointer_equal:
  \<open> cast_alias_mut_u64_pointer = cast_alias_mut_u64_pointer_primitive \<close>
  unfolding cast_alias_mut_u64_pointer_def cast_alias_mut_u64_pointer_primitive_def
  by (rule refl)

urust_expr cast_alias_mut_usize_pointer
  \<open> cast_alias_raw as MutUsizePointer \<close>

urust_expr cast_alias_mut_usize_pointer_primitive
  \<open> cast_alias_raw as *mut usize \<close>

lemma cast_alias_mut_usize_pointer_equal:
  \<open> cast_alias_mut_usize_pointer = cast_alias_mut_usize_pointer_primitive \<close>
  unfolding cast_alias_mut_usize_pointer_def cast_alias_mut_usize_pointer_primitive_def
  by (rule refl)

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
        "syntax error"

    val _ =
      expect_failure "inexact qualified use"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source "0u64 as U16Alias"))
        "unknown Rust type"

    val _ =
      expect_failure "wrong qualifier"
        (fn () =>
          Parser_Test_Elaboration.expression \<^context>
            (Parser_Lex_Util.text_source "0u64 as other::U16Alias"))
        "unknown Rust type"

  in
    val _ = ()
  end
\<close>

section\<open> Direct declarations and locale scope \<close>

experiment
begin

urust_type_alias \<open> type ExperimentWidth = u32; \<close>

urust_expr cast_alias_direct_activation
  \<open> 0_u64 as ExperimentWidth \<close>

urust_expr cast_alias_direct_activation_primitive
  \<open> 0_u64 as u32 \<close>

lemma cast_alias_direct_activation_equal:
  \<open> cast_alias_direct_activation = cast_alias_direct_activation_primitive \<close>
  unfolding cast_alias_direct_activation_def cast_alias_direct_activation_primitive_def
  by (rule refl)

end

context cast_alias_scope
begin

urust_expr cast_alias_locale_use
  \<open> scope_word as LocaleWidth \<close>

urust_expr cast_alias_locale_use_primitive
  \<open> scope_word as u16 \<close>

lemma cast_alias_locale_use_equal:
  \<open> cast_alias_locale_use = cast_alias_locale_use_primitive \<close>
  unfolding cast_alias_locale_use_def cast_alias_locale_use_primitive_def
  by (rule refl)

end

context cast_alias_scope
begin

ML_val\<open>
  local
    val ctxt = \<^context>
    val alias =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "scope_word as LocaleWidth")
    val primitive =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "scope_word as u16")
  in
    val _ =
      if Term.aconv (alias, primitive) then ()
      else error "locale alias did not persist in its declaration context"
  end
\<close>

end

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then () else error ("cast-target alias diagnostics: " ^ message)

    fun reject_then_recover (text, prefix, expected) =
      let
        val start = Position.make0 23 7 0 "" "" "cast-alias-positioned-use"
        val expected_pos = Position.symbol_explode prefix start
        val source = Parser_Lex_Util.positioned_content_source text start
        val _ =
          (case Exn.result (Parser_Test_Elaboration.expression ctxt) source of
             Exn.Res _ => error ("invalid cast-target alias accepted: " ^ quote text)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let
                   val raw_message = Runtime.exn_message exn
                   val message = XML.content_of (YXML.parse_body raw_message)
                   val markup =
                     fold Parser_Test_Reports.collect_markup
                       (YXML.parse_body raw_message) []
                   val positions =
                     map_filter
                       (fn (name, props) =>
                         if name = Markup.positionN
                         then SOME (Position.of_properties props)
                         else NONE)
                       markup
                 in
                   assert "wrong rejection reason" (String.isSubstring expected message);
                   assert "error lost its smallest source position"
                     (exists
                       (fn pos =>
                         Position.file_of pos = Position.file_of expected_pos andalso
                         Position.offset_of pos = Position.offset_of expected_pos)
                       positions)
                 end)
        val alias =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source "0u64 as types::U16Alias")
        val primitive =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source "0u64 as u16")
      in
        assert "failed declaration/use poisoned subsequent elaboration"
          (Term.aconv (alias, primitive))
      end
  in
    val _ = List.app reject_then_recover
      [("0u64 as UnknownWidth", "0u64 as ", "unknown Rust type"),
       ("0u64 as types::UnknownWidth", "0u64 as ", "unknown Rust type"),
       ("0u64 as U8Alias::<Width>", "0u64 as U8Alias",
        "syntax error")]
  end
\<close>

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
             String.isSubstring "unknown Rust type"
               (Runtime.exn_message exn))
    val imported_alias =
      Parser_Test_Elaboration.expression \<^context>
        (Parser_Lex_Util.text_source "0_u64 as U8Alias")
    val primitive =
      Parser_Test_Elaboration.expression \<^context>
        (Parser_Lex_Util.text_source "0_u64 as u8")
  in
    val _ =
      if rejected "0_u64 as ExperimentWidth" andalso
         rejected "0_u64 as LocaleWidth" andalso
         Term.aconv (imported_alias, primitive)
      then ()
      else
        error
          "cast-target alias remained active after its confined context"
  end
\<close>

section\<open> Conflicts and idempotence \<close>

experiment
begin

urust_type_alias \<open> type SharedWidth = u8; \<close>

urust_expr cast_alias_conflict_left_alone
  \<open> 0_u64 as SharedWidth \<close>

urust_expr cast_alias_conflict_left_alone_primitive
  \<open> 0_u64 as u8 \<close>

lemma cast_alias_conflict_left_alone_equal:
  \<open> cast_alias_conflict_left_alone = cast_alias_conflict_left_alone_primitive \<close>
  unfolding cast_alias_conflict_left_alone_def cast_alias_conflict_left_alone_primitive_def
  by (rule refl)

end

experiment
begin

urust_type_alias \<open> type SharedWidth = u16; \<close>

urust_expr cast_alias_conflict_right_alone
  \<open> 0_u64 as SharedWidth \<close>

urust_expr cast_alias_conflict_right_alone_primitive
  \<open> 0_u64 as u16 \<close>

lemma cast_alias_conflict_right_alone_equal:
  \<open> cast_alias_conflict_right_alone = cast_alias_conflict_right_alone_primitive \<close>
  unfolding cast_alias_conflict_right_alone_def cast_alias_conflict_right_alone_primitive_def
  by (rule refl)

end

urust_expr cast_alias_idempotent_registration
  \<open> 0_u64 as StableWidth \<close>

urust_expr cast_alias_idempotent_registration_primitive
  \<open> 0_u64 as u16 \<close>

lemma cast_alias_idempotent_registration_equal:
  \<open> cast_alias_idempotent_registration = cast_alias_idempotent_registration_primitive \<close>
  unfolding cast_alias_idempotent_registration_def cast_alias_idempotent_registration_primitive_def
  by (rule refl)

ML_val\<open>
  local
    fun declare source_name text lthy =
      #1 (Micro_Rust_Semantic_Navigation.capture (fn () =>
        let
          val source =
            Parser_Lex_Util.positioned_content_source text
              (Position.line_file 1 source_name)
          val item =
            (case URust_Parser.parse_type_alias_source lthy source of
               SOME item => item
             | NONE => error "direct alias audit: empty declaration")
        in
          URust_Type_Mappings.declare_alias
            {registration = NONE,
             item_name = URust_AST.type_alias_name item,
             parameters = URust_AST.type_alias_parameters item,
             rhs = URust_AST.type_alias_rhs item}
            lthy
        end))

    fun collect_markup (XML.Text _) result = result
      | collect_markup
          (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    val base_lthy = Named_Target.theory_init \<^theory>
    val left_context =
      declare "cast-alias-conflict-left" "type SharedWidth = u8;" base_lthy
    val conflict =
      Exn.result
        (fn () =>
          declare "cast-alias-conflict-right" "type SharedWidth = u16;"
            left_context)
        ()

    val _ =
      (case conflict of
         Exn.Res _ =>
           error "conflicting direct Rust alias declarations were accepted"
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
                    "conflicting active mappings for \"SharedWidth\""
                    message andalso
                  String.isSubstring "different Rust meanings" message andalso
                  String.isSubstring "urust_type_alias declaration" message andalso
                  length positions = 2 andalso
                  member (op =)
                    (map (Position.file_of o Position.of_properties) positions)
                    (SOME "cast-alias-conflict-left") andalso
                  member (op =)
                    (map (Position.file_of o Position.of_properties) positions)
                    (SOME "cast-alias-conflict-right")
               then ()
               else
                 error
                   ("conflicting direct Rust alias diagnostic did not " ^
                     "report both declarations:\n" ^ message)
             end)

    val SOME original = URust_Type_Mappings.lookup base_lthy "StableWidth"
    val repeated_context =
      base_lthy
      |> declare "cast-alias-idempotent-first" "type StableWidth = u16;"
      |> declare "cast-alias-idempotent-second" "type StableWidth = u16;"
    val SOME repeated = URust_Type_Mappings.lookup repeated_context "StableWidth"
    val _ =
      if URust_Type_Mappings.entry_identity original =
          URust_Type_Mappings.entry_identity repeated
      then ()
      else error "idempotent direct alias registration changed navigation identity"
    val _ =
      ignore
        (Parser_Test_Elaboration.expression repeated_context
          (Parser_Lex_Util.text_source
            "0_u64 as StableWidth"))
  in
    val _ = ()
  end
\<close>

section\<open> Declaration and use diagnostics \<close>

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
      assert_rejected "cast-alias-unknown-dependency"
        ("urust_type_alias " ^ Symbol.open_ ^ " type AliasChain = MissingAliasDependency; " ^ Symbol.close)
        "unknown Rust type"
    val _ =
      assert_rejected "cast-alias-malformed-target"
        ("urust_type_alias " ^ Symbol.open_ ^ " type BrokenPointer = *const; " ^ Symbol.close)
        "syntax error"
    val _ =
      assert_rejected "cast-alias-generic-name"
        ("urust_type_alias \"Types::Alias::<Width>\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-empty-segment"
        ("urust_type_alias \"Types::\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "invalid alias path"
    val _ =
      assert_rejected "cast-alias-reserved-segment"
        ("urust_type_alias \"Types::u16\" " ^ Symbol.open_ ^ " type Alias = u16; " ^ Symbol.close)
        "reserved segment"
  in
    val _ = ()
  end
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
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
               SOME "micro_rust_type_mapping" andalso
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
        "Direct Rust alias term, scope, diagnostic, and markup regressions passed"
  end
\<close>

end
