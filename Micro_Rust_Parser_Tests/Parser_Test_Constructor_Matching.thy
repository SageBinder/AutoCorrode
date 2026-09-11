theory Parser_Test_Constructor_Matching
  imports
    Parser_Test_Utils
    Constructor_Ambiguity_Left
    Constructor_Ambiguity_Right
    Misc.Simple_Word_Enums
begin

declare [[urust_conformance_check = true]]

section\<open>Native constructor metadata\<close>

datatype parser_ordinary_constructor =
    ParserOrdinaryPayload nat
  | ParserOrdinaryEmpty

urust_expr parser_ordinary_constructor_match
  \<open>
    match \<llangle>ParserOrdinaryPayload 7\<rrangle> {
      ParserOrdinaryPayload(value) \<Rightarrow> value,
      ParserOrdinaryEmpty \<Rightarrow> 0
    }
  \<close>

enum parser_native_case =
    ParserNativeEmpty
  | ParserNativePayload nat
  | ParserNativeOther

micro_rust_notation (literal)
  parser_native_case.ParserNativeEmpty
  ("ParserNative::Empty")
micro_rust_notation (literal)
  parser_native_case.ParserNativePayload
  ("ParserNative::Payload")
micro_rust_notation (literal)
  parser_native_case.ParserNativeOther
  ("ParserNative::Other")

urust_expr parser_native_case_exhaustive
  \<open>
    match \<llangle>ParserNativePayload 7\<rrangle> {
      ParserNative::Empty \<Rightarrow> 0,
      ParserNative::Payload(value) \<Rightarrow> value,
      ParserNative::Other \<Rightarrow> 1
    }
  \<close>

urust_expr parser_native_case_sparse
  \<open>
    match \<llangle>ParserNativeOther\<rrangle> {
      ParserNative::Payload(value) \<Rightarrow> value,
      _ \<Rightarrow> 9
    }
  \<close>

urust_expr parser_native_case_unregistered
  \<open>
    match \<llangle>ParserNativePayload 8\<rrangle> {
      ParserNativeEmpty \<Rightarrow> 0,
      ParserNativePayload(value) \<Rightarrow> value,
      ParserNativeOther \<Rightarrow> 1
    }
  \<close>

urust_expr parser_native_case_guarded
  \<open>
    match \<llangle>ParserNativePayload 8\<rrangle> {
      ParserNative::Payload(value) if True \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr parser_native_case_or_pattern
  \<open>
    match \<llangle>ParserNativeOther\<rrangle> {
      ParserNative::Empty | ParserNative::Other \<Rightarrow> 1,
      ParserNative::Payload(_) \<Rightarrow> 0
    }
  \<close>

simple_word_enum (8) parser_word_family =
    ParserWordFirst = 1
  | ParserWordSecond = 2
  | ParserWordThird = 3

micro_rust_notation (literal)
  ParserWordFirst
  ("ParserWordFamily::First")
micro_rust_notation (literal)
  ParserWordSecond
  ("ParserWordFamily::Second")
micro_rust_notation (literal)
  ParserWordThird
  ("ParserWordFamily::Third")

urust_expr parser_word_family_sparse
  \<open>
    match ParserWordFamily::Second {
      ParserWordFamily::First \<Rightarrow> 1,
      ParserWordFamily::Second \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

section\<open>Metadata-free registered values\<close>

typedef parser_raw_value = \<open>UNIV :: nat set\<close>
  by auto

definition ParserRawFirst :: parser_raw_value where
  \<open> ParserRawFirst \<equiv> Abs_parser_raw_value 1 \<close>

definition ParserRawSecond :: parser_raw_value where
  \<open> ParserRawSecond \<equiv> Abs_parser_raw_value 2 \<close>

consts parser_raw_scrutinee :: parser_raw_value

micro_rust_notation (literal) ParserRawFirst ("ParserRaw::First")
micro_rust_notation (literal) ParserRawSecond ("ParserRaw::Second")

declare [[urust_conformance_check = false]]

urust_expr parser_metadata_free_switch
  \<open>
    match \<llangle>parser_raw_scrutinee\<rrangle> {
      ParserRaw::First \<Rightarrow> 1,
      ParserRaw::Second \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

section\<open>Nested registered nullary normalization\<close>

datatype parser_nested_status =
    ParserPrimaryStatus
  | ParserSecondaryStatus

micro_rust_notation (literal)
  parser_nested_status.ParserPrimaryStatus
  ("NestedStatus::Primary")
micro_rust_notation (literal)
  parser_nested_status.ParserSecondaryStatus
  ("NestedStatus::Secondary")

urust_expr [conformance_check = true] parser_nested_registered_nullary
  \<open>
    match
      \<llangle>
        Err ParserPrimaryStatus ::
          (unit, parser_nested_status) result
      \<rrangle>
    {
      Err(NestedStatus::Primary) \<Rightarrow> Ok(()),
      res \<Rightarrow> res
    }
  \<close>
  against
    \<open>
      bind (literal (Err ParserPrimaryStatus))
        (\<lambda>value.
          case value of
            Ok result \<Rightarrow> literal (Ok result)
          | Err error \<Rightarrow>
              two_armed_conditional
                (urust_eq
                  (literal error)
                  (literal ParserPrimaryStatus))
                (funcall1 (lift_fun1 Ok) (literal ()))
                undefined)
    \<close>

thm parser_nested_registered_nullary_conformance

urust_expr parser_nested_registered_ordered ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match
      \<llangle>
        Err ParserSecondaryStatus ::
          (unit, parser_nested_status) result
      \<rrangle>
    {
      Err(NestedStatus::Primary) \<Rightarrow> 1,
      Err(NestedStatus::Secondary) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_registered_or_ordered ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match
      \<llangle>
        Err ParserPrimaryStatus ::
          (unit, parser_nested_status) result
      \<rrangle>
    {
      Err(NestedStatus::Primary) |
        Err(NestedStatus::Secondary) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

declare [[urust_conformance_check = false]]

urust_expr parser_nested_registered_payload
  \<open>
    match \<llangle>Some (ParserNativePayload 7)\<rrangle> {
      Some(ParserNative::Payload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

section\<open>Resolution and term-shape audit\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val theory = Proof_Context.theory_of ctxt

    fun assert message condition =
      if condition then () else error ("constructor matching audit: " ^ message)

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun equation_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals

    fun rhs_of name = snd (equation_of name)

    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "constructor matching audit: expected constant")

    fun make_path text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME (URust_AST.UE_Path path) => path
       | _ => error ("constructor matching audit: expected path " ^ quote text))

    fun resolve text =
      let
        val path = make_path text
        val resolver =
          URust_Resolution.make_constructor_resolver ctxt
            (URust_AST.path_position path)
      in
        the (URust_Resolution.resolve_constructor ctxt resolver path)
      end

    val native_payload = resolve "ParserNative::Payload"
    val native_family =
      the (URust_Resolution.constructor_family native_payload)
    val word_second = resolve "ParserWordFamily::Second"
    val word_family =
      the (URust_Resolution.constructor_family word_second)
    val raw_path = make_path "ParserRaw::First"
    val raw_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position raw_path)

    val (_, native_members) = native_family
    val (_, word_members) = word_family
    val _ =
      assert "custom enum positional arity was not recovered"
        (URust_Resolution.constructor_arity native_payload = 1)
    val _ =
      assert "custom enum registration was not marked exact"
        (URust_Resolution.constructor_is_exact_registered native_payload)
    val _ =
      assert "custom enum unexpectedly acquired Ctr_Sugar metadata"
        (is_none
          (Ctr_Sugar.ctr_sugar_of ctxt
            (fst (dest_Type \<^typ>\<open>parser_native_case\<close>))))
    val _ =
      assert "custom enum is not an authentic Code constructor"
        (Code.is_constr theory
          (dest_Const_name \<^term>\<open>ParserNativePayload\<close>))
    val _ =
      assert "custom enum family order changed"
        (map constant_name native_members =
          map constant_name
            [\<^term>\<open>ParserNativeEmpty\<close>,
             \<^term>\<open>ParserNativePayload\<close>,
             \<^term>\<open>ParserNativeOther\<close>])
    val _ =
      assert "simple_word_enum family order changed"
        (map constant_name word_members =
          map constant_name
            [\<^term>\<open>ParserWordFirst\<close>,
             \<^term>\<open>ParserWordSecond\<close>,
             \<^term>\<open>ParserWordThird\<close>])
    val _ =
      assert "simple_word_enum unexpectedly became a Code constructor"
        (not (Code.is_constr theory
          (dest_Const_name \<^term>\<open>ParserWordSecond\<close>)))
    val _ =
      assert "metadata-free value acquired constructor identity"
        (URust_Resolution.classify_registered_literal ctxt
          raw_resolver raw_path =
            URust_Resolution.Registered_Value_Literal)
    val _ =
      assert "metadata-free value unexpectedly acquired native case metadata"
        (is_none
          (Case_Translation.lookup_by_constr_permissive ctxt
            (dest_Const_name \<^term>\<open>ParserRawFirst\<close>,
             fastype_of \<^term>\<open>ParserRawFirst\<close>)))

    val metadata_free = rhs_of "parser_metadata_free_switch"
    val _ =
      assert "metadata-free values did not use switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          metadata_free = 1)
    val _ =
      assert "metadata-free switch duplicated its scrutinee"
        (count_constant \<^const_name>\<open>parser_raw_scrutinee\<close>
          metadata_free = 1)

    val (nested_lhs, nested) =
      equation_of "parser_nested_registered_nullary"
    val nested_conformance =
      Proof_Context.get_thm ctxt
        "parser_nested_registered_nullary_conformance"
    val (conformance_lhs, conformance_rhs) =
      nested_conformance
      |> Thm.prop_of
      |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq
    val (_, nested_lhs_arguments) = Term.strip_comb nested_lhs
    val _ =
      assert "nested fixture acquired an unintended definition argument"
        (null nested_lhs_arguments)
    val _ =
      assert "nested fixture acquired an unintended function type"
        (null (binder_types (fastype_of nested_lhs)))
    val _ =
      assert "nested fixture retained a schematic term variable"
        (null (Term.add_vars nested []))
    val _ =
      assert "nested fixture retained a local free binder"
        (null (Term.add_frees nested []))
    val _ =
      assert "nested fixture conformance theorem has premises"
        (Thm.nprems_of nested_conformance = 0)
    val _ =
      assert "nested fixture conformance theorem changed its definition head"
        (Term.aconv (nested_lhs, conformance_lhs))
    val _ =
      assert "nested fixture differs from its complete legacy term"
        (Term.aconv (nested, conformance_rhs))
    val _ =
      assert "nested fixture conformance target retained schematic variables"
        (null (Term.add_vars conformance_rhs []))
    val _ =
      assert "nested fixture conformance target retained local free binders"
        (null (Term.add_frees conformance_rhs []))
    val SOME (inner_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserPrimaryStatus\<close>,
         fastype_of \<^term>\<open>ParserPrimaryStatus\<close>)
    val inner_case_name = constant_name inner_case
    val result_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt
          (fst (dest_Type
            \<^typ>\<open>(unit, parser_nested_status) result\<close>)) of
         SOME {casex, ...} => constant_name casex
       | NONE => error "constructor matching audit: missing result case sugar")
    val _ =
      assert "nested normalization lost the enclosing authentic case"
        (count_constant result_case_name nested > 0)
    val _ =
      assert "nested exact nullary constructor retained a native inner case"
        (count_constant inner_case_name nested = 0)
    val _ =
      assert "nested exact nullary constructor lost its equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close> nested = 1)

    fun checked_ordered_term name expected =
      let
        val rhs = rhs_of name
        val _ =
          assert (name ^ " has the wrong completed type")
            (fastype_of rhs = fastype_of expected)
        val _ =
          assert (name ^ " differs from its complete ordered term")
            (Term.aconv_untyped (rhs, expected))
        val _ =
          assert (name ^ " retained schematic variables")
            (null (Term.add_vars rhs []))
        val _ =
          assert (name ^ " retained local free binders")
            (null (Term.add_frees rhs []))
      in rhs end

    fun equality_constructor_order term =
      let
        fun collect
              (Const (name, _) $
                (Const (equality, _) $ _ $
                  (Const (literal, _) $ constructor)) $
                _ $ else_branch) =
              if name = \<^const_name>\<open>two_armed_conditional\<close> andalso
                 equality = \<^const_name>\<open>urust_eq\<close> andalso
                 literal = \<^const_name>\<open>literal\<close>
              then
                constant_name constructor ::
                  collect else_branch
              else []
          | collect _ = []

        fun find
              (candidate as
                Const (name, _) $ _ $ _ $ _) =
              if name = \<^const_name>\<open>two_armed_conditional\<close>
              then
                let val result = collect candidate
                in if null result then NONE else SOME result end
              else NONE
          | find _ = NONE

        fun first_some [] = NONE
          | first_some (NONE :: rest) = first_some rest
          | first_some (SOME value :: _) = SOME value

        fun walk (left $ right) =
              (case find (left $ right) of
                 SOME result => SOME result
               | NONE => first_some [walk left, walk right])
          | walk (Abs (_, _, body)) = walk body
          | walk term = find term
      in the (walk term) end

    val ordered_expected =
      \<^term>\<open>
        (bind (literal (Err ParserSecondaryStatus))
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow> literal (3 :: nat)
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserPrimaryStatus))
                  (literal (1 :: nat))
                  (two_armed_conditional
                    (urust_eq
                      (literal error)
                      (literal ParserSecondaryStatus))
                    (literal (2 :: nat))
                    undefined))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val ordered_or_expected =
      \<^term>\<open>
        (bind (literal (Err ParserPrimaryStatus))
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow> literal (0 :: nat)
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserPrimaryStatus))
                  (literal (1 :: nat))
                  (two_armed_conditional
                    (urust_eq
                      (literal error)
                      (literal ParserSecondaryStatus))
                    (literal (1 :: nat))
                    undefined))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val ordered =
      checked_ordered_term
        "parser_nested_registered_ordered" ordered_expected
    val ordered_or =
      checked_ordered_term
        "parser_nested_registered_or_ordered" ordered_or_expected
    val expected_equality_order =
      map constant_name
        [\<^term>\<open>ParserPrimaryStatus\<close>,
         \<^term>\<open>ParserSecondaryStatus\<close>]
    val _ =
      assert "separate same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered = 1)
    val _ =
      assert "separate same-outer alternatives lost an equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered = 2)
    val _ =
      assert "separate same-outer alternative order changed"
        (equality_constructor_order ordered =
          expected_equality_order)
    val _ =
      assert "or-pattern same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered_or = 1)
    val _ =
      assert "or-pattern same-outer alternatives lost an equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered_or = 2)
    val _ =
      assert "or-pattern alternative order changed"
        (equality_constructor_order ordered_or =
          expected_equality_order)

    val nested_payload = rhs_of "parser_nested_registered_payload"
    val SOME (native_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserNativePayload\<close>,
         fastype_of \<^term>\<open>ParserNativePayload\<close>)
    val native_case_name = constant_name native_case
    val _ =
      assert "argument-bearing nested constructor lost recursive case lowering"
        (count_constant native_case_name nested_payload > 0)
    val _ =
      assert "argument-bearing nested constructor was normalized as equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nested_payload = 0)

    val ambiguity_path = make_path "Shared"
    val ambiguity_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position ambiguity_path)
    val ambiguity =
      (URust_Resolution.resolve_constructor ctxt
         ambiguity_resolver ambiguity_path;
       NONE)
      handle ERROR message => SOME message
    val ambiguity_message =
      (case ambiguity of
         SOME message => message
       | NONE =>
           error "constructor matching audit: expected constructor ambiguity")
    val left_name =
      dest_Const_name
        \<^term>\<open>Constructor_Ambiguity_Left.Shared\<close>
    val right_name =
      dest_Const_name
        \<^term>\<open>Constructor_Ambiguity_Right.Shared\<close>
    val _ =
      assert "ambiguity diagnostic omitted the left qualified candidate"
        (String.isSubstring left_name ambiguity_message)
    val _ =
      assert "ambiguity diagnostic omitted the right qualified candidate"
        (String.isSubstring right_name ambiguity_message)

    val switch_constructor =
      (Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_switch \<llangle>ParserNativeOther\<rrangle> { \
          \ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }");
       NONE)
      handle ERROR message => SOME message
    val _ =
      assert "explicit switch accepted an authentic constructor"
        (case switch_constructor of
           SOME message =>
             String.isSubstring "requires case-pattern lowering" message
         | NONE => false)

    val markup_reports =
      Synchronized.var
        "constructor_matching_native_case_markup"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change markup_reports (append chunks)
    val markup_start =
      Position.make0 70 4000 0 "" ""
        "constructor-matching-native-case-markup"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        ("match \<llangle>ParserNativeOther\<rrangle> { " ^
         "ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }")
        markup_start
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression
                    ctxt markup_source)) ())
          ())
    val markup_text =
      String.concat (Synchronized.value markup_reports)
    val _ =
      assert "native case qualifier lost constructor markup"
        (String.isSubstring Markup.keyword3N markup_text)
    val _ =
      assert "native case markup lost its recovered family identity"
        (String.isSubstring (#1 native_family) markup_text)

    val recovered =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_case \<llangle>ParserNativeOther\<rrangle> { \
          \ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }")
    val _ =
      assert "constructor rejection did not recover"
        (count_constant
          (constant_name
            (fst (the
              (Case_Translation.lookup_by_constr_permissive ctxt
                (dest_Const_name \<^term>\<open>ParserNativeOther\<close>,
                 fastype_of \<^term>\<open>ParserNativeOther\<close>)))))
          recovered > 0)
  in
    val _ = ()
  end
\<close>

end
