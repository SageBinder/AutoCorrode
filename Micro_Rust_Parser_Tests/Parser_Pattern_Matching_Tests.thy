theory Parser_Pattern_Matching_Tests
  imports
    Parser_Syntax_Tests
    Parser_Constructor_Ambiguity_Left_Fixtures
    Parser_Constructor_Ambiguity_Right_Fixtures
    Misc.Simple_Word_Enums
    Shallow_Micro_Rust.Core_Expression_Lemmas
begin

declare [[urust_conformance = true]]

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

urust_expr parser_word_family_exhaustive ::
  \<open>
    parser_word_family \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      ParserWordFamily::Third \<Rightarrow> 30,
      ParserWordFamily::First \<Rightarrow> 10,
      ParserWordFamily::Second \<Rightarrow> 20
    }
  \<close>

urust_expr parser_word_family_partial ::
  \<open>
    parser_word_family \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      ParserWordFamily::Second \<Rightarrow> 2
    }
  \<close>

urust_expr parser_word_family_guarded ::
  \<open>
    parser_word_family \<Rightarrow> bool \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, enabled)
  \<open>
    match scrutinee {
      ParserWordFamily::First if enabled \<Rightarrow> 10,
      ParserWordFamily::First \<Rightarrow> 11,
      ParserWordFamily::Second | ParserWordFamily::Third \<Rightarrow> 20
    }
  \<close>

urust_expr parser_word_family_matches ::
  \<open>
    parser_word_family \<Rightarrow>
      (unit, bool, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open> matches!(scrutinee, ParserWordFamily::Second) \<close>

text\<open>
The legacy frontend's nested-pattern path asks \<open>Basic_Case_Expression\<close> whether a free
identifier is a \<open>Code.is_constr\<close> constructor. A \<open>simple_word_enum\<close> variant instead receives
native case metadata through \<open>Case_Translation\<close>. Unlike the other qualification-sensitive legacy
bug, this failure also occurs with the unqualified variant name: the legacy frontend silently treats
both that spelling and the fully qualified nested variant below as binders. The dedicated parser
resolves the same metadata before calling the shared case backend and therefore preserves the
constructor test.
\<close>

definition parser_word_family_legacy_nested ::
  \<open>
    parser_word_family option \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_word_family_legacy_nested scrutinee \<equiv>
        \<lbrakk>
          match scrutinee {
            Some(ParserWordFamily::First) \<Rightarrow> 1,
            _ \<Rightarrow> 0
          }
        \<rbrakk>
    \<close>

urust_expr [conformance = false] parser_word_family_nested ::
  \<open>
    parser_word_family option \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      Some(ParserWordFamily::First | ParserWordFamily::Third) \<Rightarrow> 13,
      Some(ParserWordFamily::Second) \<Rightarrow> 2,
      None \<Rightarrow> 0
    }
  \<close>

simple_word_enum (plugins del: word_conversion) (8)
  parser_single_word_family =
    ParserWordOnly = 173

micro_rust_notation (literal)
  ParserWordOnly ("ParserSingleWordFamily::ParserWordOnly")

urust_expr parser_single_word_family_exhaustive ::
  \<open>
    parser_single_word_family \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserSingleWordFamily::ParserWordOnly \<Rightarrow> 1
    }
  \<close>

lemma parser_word_family_results:
  shows
    \<open>
      parser_word_family_exhaustive ParserWordFirst =
        literal (10 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_exhaustive ParserWordSecond =
        literal (20 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_exhaustive ParserWordThird =
        literal (30 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_guarded ParserWordFirst True =
        literal (10 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_guarded ParserWordFirst False =
        literal (11 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_guarded ParserWordSecond True =
        literal (20 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_guarded ParserWordThird False =
        literal (20 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_matches ParserWordSecond =
        literal True
    \<close>
    and
    \<open>
      parser_word_family_matches ParserWordFirst =
        literal False
    \<close>
    and
    \<open>
      parser_word_family_matches ParserWordThird =
        literal False
    \<close>
  by
    (simp_all add:
      parser_word_family_exhaustive_def
      parser_word_family_guarded_def
      parser_word_family_matches_def
      micro_rust_simps)

lemma parser_word_family_nested_results:
  shows
    \<open>
      parser_word_family_nested (Some ParserWordFirst) =
        literal (13 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_nested (Some ParserWordSecond) =
        literal (2 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_nested (Some ParserWordThird) =
        literal (13 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_nested None =
        literal (0 :: nat)
    \<close>
  by
    (simp_all add:
      parser_word_family_nested_def
      micro_rust_simps)

lemma parser_word_family_legacy_nested_is_catchall:
  shows
    \<open>
      parser_word_family_legacy_nested (Some ParserWordFirst) =
        literal (1 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_legacy_nested (Some ParserWordSecond) =
        literal (1 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_legacy_nested None =
        literal (0 :: nat)
    \<close>
  by
    (simp_all add:
      parser_word_family_legacy_nested_def
      micro_rust_simps)

lemma parser_single_word_family_result:
  \<open>
    parser_single_word_family_exhaustive ParserWordOnly =
      literal (1 :: nat)
  \<close>
  by
    (simp add:
      parser_single_word_family_exhaustive_def
      micro_rust_simps)

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

declare [[urust_conformance = false]]

urust_expr parser_metadata_free_switch
  \<open>
    match \<llangle>parser_raw_scrutinee\<rrangle> {
      ParserRaw::First \<Rightarrow> 1,
      ParserRaw::Second \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_metadata_free_case
  \<open>
    match_case \<llangle>parser_raw_scrutinee\<rrangle> {
      ParserRaw::First \<Rightarrow> 1,
      _ \<Rightarrow> 2
    }
  \<close>

urust_expr parser_literal_switch
  \<open>
    match \<llangle>2 :: nat\<rrangle> {
      1 \<Rightarrow> 1,
      _ \<Rightarrow> 2
    }
  \<close>

section\<open>Deep registered nullary constructor matching\<close>

datatype parser_nested_status =
    ParserPrimaryStatus
  | ParserSecondaryStatus
  | ParserTertiaryStatus

type_synonym parser_nested_overlap_input =
  \<open>
    (unit, parser_nested_status) result \<times>
      ((unit, parser_nested_status) result \<times> tnil)
  \<close>

type_synonym parser_nested_different_depth_input =
  \<open>
    (unit, parser_nested_status) result \<times>
      (((unit, parser_nested_status) result \<times>
          (nat \<times> tnil)) \<times> tnil)
  \<close>

type_synonym parser_recursive_coverage_pair =
  \<open>
    (unit, parser_nested_status) result \<times>
      (nat \<times> tnil)
  \<close>

type_synonym parser_recursive_coverage_input =
  \<open>
    parser_recursive_coverage_pair \<times>
      (parser_recursive_coverage_pair \<times> tnil)
  \<close>

micro_rust_notation (literal)
  parser_nested_status.ParserPrimaryStatus
  ("NestedStatus::Primary")
micro_rust_notation (literal)
  parser_nested_status.ParserSecondaryStatus
  ("NestedStatus::Secondary")
micro_rust_notation (literal)
  parser_nested_status.ParserTertiaryStatus
  ("NestedStatus::Tertiary")

urust_expr [conformance = true] parser_nested_registered_nullary
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
      \<lbrakk>
        match
          \<llangle>
            Err ParserPrimaryStatus ::
              (unit, parser_nested_status) result
          \<rrangle>
        {
          Err(ParserPrimaryStatus) \<Rightarrow> Ok(()),
          res \<Rightarrow> res
        }
      \<rbrakk>
    \<close>

thm parser_nested_registered_nullary_conformance

urust_expr [conformance = true]
  parser_nested_registered_nullary_open ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (unit, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      Err(NestedStatus::Primary) \<Rightarrow> Ok(()),
      res \<Rightarrow> res
    }
  \<close>
  against
    \<open>
      \<lbrakk>
        match scrutinee {
          Err(ParserPrimaryStatus) \<Rightarrow> Ok(()),
          res \<Rightarrow> res
        }
      \<rbrakk>
    \<close>

thm parser_nested_registered_nullary_open_conformance

lemma parser_nested_registered_nullary_matches:
  \<open>
    parser_nested_registered_nullary_open
        (Err ParserPrimaryStatus) =
      literal (Ok ())
  \<close>
  by
    (simp add:
      parser_nested_registered_nullary_open_def
      micro_rust_simps)

lemma parser_nested_registered_nullary_falls_through:
  \<open>
    parser_nested_registered_nullary_open
        (Err ParserSecondaryStatus) =
      literal (Err ParserSecondaryStatus)
  \<close>
  by
    (simp add:
      parser_nested_registered_nullary_open_def
      micro_rust_simps)

section\<open>Direct structural matrices\<close>

datatype parser_matrix_bit =
    ParserMatrixLow
  | ParserMatrixHigh

datatype parser_matrix_input =
  ParserMatrixInput
    parser_matrix_bit parser_matrix_bit
    parser_matrix_bit parser_matrix_bit

datatype parser_matrix_choice =
    ParserMatrixLeft
  | ParserMatrixPayload nat
  | ParserMatrixRight

urust_expr parser_four_axis_structural_matrix ::
  \<open>
    parser_matrix_input \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserMatrixInput(ParserMatrixLow, ParserMatrixLow,
        ParserMatrixLow, ParserMatrixLow) \<Rightarrow> 0,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixLow,
        ParserMatrixLow, ParserMatrixHigh) \<Rightarrow> 1,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixLow,
        ParserMatrixHigh, ParserMatrixLow) \<Rightarrow> 2,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixLow,
        ParserMatrixHigh, ParserMatrixHigh) \<Rightarrow> 3,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixHigh,
        ParserMatrixLow, ParserMatrixLow) \<Rightarrow> 4,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixHigh,
        ParserMatrixLow, ParserMatrixHigh) \<Rightarrow> 5,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixHigh,
        ParserMatrixHigh, ParserMatrixLow) \<Rightarrow> 6,
      ParserMatrixInput(ParserMatrixLow, ParserMatrixHigh,
        ParserMatrixHigh, ParserMatrixHigh) \<Rightarrow> 7,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixLow,
        ParserMatrixLow, ParserMatrixLow) \<Rightarrow> 8,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixLow,
        ParserMatrixLow, ParserMatrixHigh) \<Rightarrow> 9,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixLow,
        ParserMatrixHigh, ParserMatrixLow) \<Rightarrow> 10,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixLow,
        ParserMatrixHigh, ParserMatrixHigh) \<Rightarrow> 11,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixHigh,
        ParserMatrixLow, ParserMatrixLow) \<Rightarrow> 12,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixHigh,
        ParserMatrixLow, ParserMatrixHigh) \<Rightarrow> 13,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixHigh,
        ParserMatrixHigh, ParserMatrixLow) \<Rightarrow> 14,
      ParserMatrixInput(ParserMatrixHigh, ParserMatrixHigh,
        ParserMatrixHigh, ParserMatrixHigh) \<Rightarrow> 15
    }
  \<close>

urust_expr parser_small_structural_matrix ::
  \<open>
    parser_matrix_choice \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserMatrixLeft \<Rightarrow> 1,
      ParserMatrixPayload(value) \<Rightarrow> value,
      ParserMatrixRight \<Rightarrow> 2
    }
  \<close>

urust_expr parser_closed_structural_matrix
  \<open>
    match \<llangle>ParserMatrixPayload 7\<rrangle> {
      ParserMatrixLeft \<Rightarrow> 1,
      ParserMatrixPayload(value) \<Rightarrow> value,
      ParserMatrixRight \<Rightarrow> 2
    }
  \<close>

urust_expr parser_structural_or_matrix ::
  \<open>
    parser_matrix_choice \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserMatrixLeft | ParserMatrixRight \<Rightarrow> 1,
      ParserMatrixPayload(value) \<Rightarrow> value
    }
  \<close>

urust_expr parser_partial_structural_matrix ::
  \<open>
    parser_matrix_choice \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserMatrixPayload(value) \<Rightarrow> value
    }
  \<close>

urust_expr parser_explicit_fallback_structural_matrix ::
  \<open>
    parser_matrix_choice \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ParserMatrixLeft \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

definition parser_matrix_effectful_scrutinee ::
  \<open>
    (nat, parser_matrix_choice, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_matrix_effectful_scrutinee =
        sequence (put Suc) (literal ParserMatrixRight)
    \<close>

urust_expr [conformance = false]
  parser_effectful_structural_matrix ::
  \<open>(nat, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<epsilon>\<open>parser_matrix_effectful_scrutinee\<close> {
      ParserMatrixLeft \<Rightarrow> 1,
      ParserMatrixPayload(value) \<Rightarrow> value,
      ParserMatrixRight \<Rightarrow> 2
    }
  \<close>

lemma parser_four_axis_structural_matrix_results:
  \<open>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixLow
        ParserMatrixLow ParserMatrixLow) = literal (0 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixLow
        ParserMatrixLow ParserMatrixHigh) = literal (1 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixLow
        ParserMatrixHigh ParserMatrixLow) = literal (2 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixLow
        ParserMatrixHigh ParserMatrixHigh) = literal (3 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixHigh
        ParserMatrixLow ParserMatrixLow) = literal (4 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixHigh
        ParserMatrixLow ParserMatrixHigh) = literal (5 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixHigh
        ParserMatrixHigh ParserMatrixLow) = literal (6 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixLow ParserMatrixHigh
        ParserMatrixHigh ParserMatrixHigh) = literal (7 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixLow
        ParserMatrixLow ParserMatrixLow) = literal (8 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixLow
        ParserMatrixLow ParserMatrixHigh) = literal (9 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixLow
        ParserMatrixHigh ParserMatrixLow) = literal (10 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixLow
        ParserMatrixHigh ParserMatrixHigh) = literal (11 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixHigh
        ParserMatrixLow ParserMatrixLow) = literal (12 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixHigh
        ParserMatrixLow ParserMatrixHigh) = literal (13 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixHigh
        ParserMatrixHigh ParserMatrixLow) = literal (14 :: nat) \<and>
    parser_four_axis_structural_matrix
      (ParserMatrixInput ParserMatrixHigh ParserMatrixHigh
        ParserMatrixHigh ParserMatrixHigh) = literal (15 :: nat)
  \<close>
  by (simp add: parser_four_axis_structural_matrix_def micro_rust_simps)

lemma parser_small_structural_matrix_results:
  \<open>
    parser_small_structural_matrix ParserMatrixLeft =
      literal (1 :: nat) \<and>
    parser_small_structural_matrix (ParserMatrixPayload 7) =
      literal (7 :: nat) \<and>
    parser_small_structural_matrix ParserMatrixRight =
      literal (2 :: nat) \<and>
    parser_closed_structural_matrix = literal (7 :: nat) \<and>
    parser_structural_or_matrix ParserMatrixLeft =
      literal (1 :: nat) \<and>
    parser_structural_or_matrix ParserMatrixRight =
      literal (1 :: nat) \<and>
    parser_structural_or_matrix (ParserMatrixPayload 9) =
      literal (9 :: nat) \<and>
    parser_explicit_fallback_structural_matrix ParserMatrixLeft =
      literal (1 :: nat) \<and>
    parser_explicit_fallback_structural_matrix ParserMatrixRight =
      literal (0 :: nat)
  \<close>
  by
    (simp add:
      parser_small_structural_matrix_def
      parser_closed_structural_matrix_def
      parser_structural_or_matrix_def
      parser_explicit_fallback_structural_matrix_def
      micro_rust_simps)

lemma parser_effectful_structural_matrix_evaluates_once:
  \<open>
    evaluate parser_effectful_structural_matrix 0 =
      Success (2 :: nat) 1
  \<close>
  by
    (simp add:
      parser_effectful_structural_matrix_def
      parser_matrix_effectful_scrutinee_def
      evaluate_def sequence_def put_def literal_def
      micro_rust_simps Core_Expression.bind.simps)

section\<open>Nested structural totality\<close>

datatype parser_registered_singleton =
  ParserRegisteredSingleton nat

datatype parser_native_singleton =
  ParserNativeSingleton nat

micro_rust_notation (literal)
  parser_registered_singleton.ParserRegisteredSingleton
  ("ParserFixture::RegisteredSingleton")

urust_expr [conformance = false]
  parser_nested_registered_singleton
  \<open>
    match \<llangle>Some (ParserRegisteredSingleton 7)\<rrangle> {
      Some(ParserFixture::RegisteredSingleton(whole @ _)) \<Rightarrow>
        whole,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_native_singleton
  \<open>
    match \<llangle>Some (ParserNativeSingleton 8)\<rrangle> {
      Some(ParserNativeSingleton(whole @ _)) \<Rightarrow> whole,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_partial_constructor_alias
  \<open>
    match \<llangle>Some (ParserMatrixPayload 7)\<rrangle> {
      Some(whole @ ParserMatrixPayload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_value_fallback
  \<open>
    match \<llangle>Some ParserRawFirst\<rrangle> {
      Some(ParserRaw::First) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_range_fallback
  \<open>
    match \<llangle>Some (6 :: nat)\<rrangle> {
      Some(5..=7) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_slice_fallback ::
  \<open>
    nat list option \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      Some([head, ..]) \<Rightarrow> head,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr [conformance = false]
  parser_nested_guarded_fallback
  \<open>
    match \<llangle>Some (ParserMatrixPayload 7)\<rrangle> {
      Some(ParserMatrixPayload(value)) if False \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

lemma parser_nested_singleton_and_fallback_results:
  \<open>
    parser_nested_registered_singleton = literal (7 :: nat) \<and>
    parser_nested_native_singleton = literal (8 :: nat) \<and>
    parser_nested_partial_constructor_alias = literal (7 :: nat) \<and>
    parser_nested_value_fallback = literal (1 :: nat) \<and>
    parser_nested_range_fallback = literal (1 :: nat) \<and>
    parser_nested_slice_fallback (Some [1, 2, 3]) =
      literal (1 :: nat) \<and>
    parser_nested_slice_fallback (Some []) =
      literal (0 :: nat) \<and>
    parser_nested_guarded_fallback = literal (0 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_registered_singleton_def
      parser_nested_native_singleton_def
      parser_nested_partial_constructor_alias_def
      parser_nested_value_fallback_def
      parser_nested_range_fallback_def
      parser_nested_slice_fallback_def
      parser_nested_guarded_fallback_def
      two_armed_conditional_def urust_eq_def
      comp_ge_def comp_le_def urust_conj_def false_def
      micro_rust_simps)

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

consts
  parser_nested_mixed_scrutinee :: \<open>parser_native_case option\<close>
  parser_nested_guarded_scrutinee ::
    \<open>(unit, parser_nested_status) result\<close>
  parser_nested_interleaved_scrutinee ::
    \<open>(unit, parser_nested_status) result\<close>
  parser_nested_alias_wild_scrutinee ::
    \<open>(unit, parser_nested_status) result\<close>
  parser_nested_alias_binder_scrutinee ::
    \<open>(unit, parser_nested_status) result\<close>
  parser_nested_alias_tag ::
    \<open>(unit, parser_nested_status) result \<Rightarrow> nat\<close>
  parser_nested_alias_rewrite ::
    \<open>
      (unit, parser_nested_status) result \<Rightarrow>
        (unit, parser_nested_status) result
    \<close>
  parser_nested_alias_probe_result ::
    \<open>(unit, parser_nested_status) result\<close>
  parser_nested_guard_marker :: bool
  parser_nested_interleaved_guard :: bool

urust_expr parser_nested_registered_mixed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<llangle>parser_nested_mixed_scrutinee\<rrangle> {
      Some(ParserNative::Empty) \<Rightarrow> 1,
      Some(ParserNative::Payload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr parser_nested_registered_guard_order ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<llangle>parser_nested_guarded_scrutinee\<rrangle> {
      Err(NestedStatus::Primary)
        if \<llangle>parser_nested_guard_marker\<rrangle> \<Rightarrow> 1,
      _ \<Rightarrow> 2
    }
  \<close>

urust_expr parser_nested_global_source_order ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<llangle>parser_nested_interleaved_scrutinee\<rrangle> {
      Err(NestedStatus::Primary) \<Rightarrow> 1,
      res if \<llangle>parser_nested_interleaved_guard\<rrangle> \<Rightarrow> 2,
      Err(NestedStatus::Secondary) \<Rightarrow> 3,
      _ \<Rightarrow> 4
    }
  \<close>

definition parser_nested_overlap_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_overlap_scrutinee =
        (Err ParserSecondaryStatus,
          (Err ParserSecondaryStatus, TNil))
    \<close>

urust_expr parser_nested_overlapping_tuple ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<llangle>parser_nested_overlap_scrutinee\<rrangle> {
      (Err(NestedStatus::Primary), _) \<Rightarrow> 1,
      (_, Err(NestedStatus::Secondary)) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

lemma parser_nested_overlapping_tuple_evaluation:
  \<open> parser_nested_overlapping_tuple = literal (2 :: nat) \<close>
  by
    (simp add:
      parser_nested_overlapping_tuple_def
      parser_nested_overlap_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

definition parser_nested_or_overlap_reverse_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_or_overlap_reverse_scrutinee =
        (Err ParserPrimaryStatus,
          (Err ParserSecondaryStatus, TNil))
    \<close>

definition parser_nested_or_overlap_later_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_or_overlap_later_scrutinee =
        (Err ParserSecondaryStatus,
          (Err ParserPrimaryStatus, TNil))
    \<close>

definition parser_nested_or_overlap_wildcard_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_or_overlap_wildcard_scrutinee =
        (Ok (), (Ok (), TNil))
    \<close>

definition parser_nested_or_overlap_reversed_second_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_or_overlap_reversed_second_scrutinee =
        (Err ParserPrimaryStatus,
          (Err ParserPrimaryStatus, TNil))
    \<close>

definition parser_nested_or_overlap_both_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_or_overlap_both_scrutinee =
        (Err ParserPrimaryStatus,
          (Err ParserSecondaryStatus, TNil))
    \<close>

definition parser_nested_alias_binder_first_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_alias_binder_first_scrutinee =
        (Err ParserPrimaryStatus,
          (Err ParserTertiaryStatus, TNil))
    \<close>

definition parser_nested_alias_binder_second_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_alias_binder_second_scrutinee =
        (Err ParserTertiaryStatus,
          (Err ParserSecondaryStatus, TNil))
    \<close>

definition parser_nested_different_depth_first_scrutinee ::
  \<open>parser_nested_different_depth_input\<close>
  where
    \<open>
      parser_nested_different_depth_first_scrutinee =
        (Err ParserPrimaryStatus,
          ((Err ParserTertiaryStatus, (11, TNil)), TNil))
    \<close>

definition parser_nested_different_depth_second_scrutinee ::
  \<open>parser_nested_different_depth_input\<close>
  where
    \<open>
      parser_nested_different_depth_second_scrutinee =
        (Err ParserTertiaryStatus,
          ((Err ParserSecondaryStatus, (22, TNil)), TNil))
    \<close>

definition parser_nested_different_depth_both_scrutinee ::
  \<open>parser_nested_different_depth_input\<close>
  where
    \<open>
      parser_nested_different_depth_both_scrutinee =
        (Err ParserPrimaryStatus,
          ((Err ParserSecondaryStatus, (33, TNil)), TNil))
    \<close>

definition parser_nested_different_depth_miss_scrutinee ::
  \<open>parser_nested_different_depth_input\<close>
  where
    \<open>
      parser_nested_different_depth_miss_scrutinee =
        (Ok (), ((Ok (), (44, TNil)), TNil))
    \<close>

definition parser_recursive_coverage_left_match ::
  \<open>parser_recursive_coverage_input\<close>
  where
    \<open>
      parser_recursive_coverage_left_match =
        ((Err ParserPrimaryStatus, (11, TNil)),
          ((Err ParserSecondaryStatus, (12, TNil)), TNil))
    \<close>

definition parser_recursive_coverage_right_match ::
  \<open>parser_recursive_coverage_input\<close>
  where
    \<open>
      parser_recursive_coverage_right_match =
        ((Err ParserSecondaryStatus, (21, TNil)),
          ((Err ParserPrimaryStatus, (22, TNil)), TNil))
    \<close>

definition parser_recursive_coverage_fallback ::
  \<open>parser_recursive_coverage_input\<close>
  where
    \<open>
      parser_recursive_coverage_fallback =
        ((Err ParserSecondaryStatus, (31, TNil)),
          ((Err ParserTertiaryStatus, (32, TNil)), TNil))
    \<close>

definition parser_nested_exhaustive_first_miss_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_exhaustive_first_miss_scrutinee =
        (Err ParserSecondaryStatus, (Ok (), TNil))
    \<close>

definition parser_nested_exhaustive_third_miss_scrutinee ::
  \<open>parser_nested_overlap_input\<close>
  where
    \<open>
      parser_nested_exhaustive_third_miss_scrutinee =
        (Ok (),
          (Err ParserPrimaryStatus, TNil))
    \<close>

definition parser_nested_source_guard_true ::
  \<open>(nat, bool, unit, unit, unit, unit) expression\<close>
  where
    \<open>
      parser_nested_source_guard_true =
        sequence (put Suc) (literal True)
    \<close>

definition parser_nested_source_guard_false ::
  \<open>(nat, bool, unit, unit, unit, unit) expression\<close>
  where
    \<open>
      parser_nested_source_guard_false =
        sequence (put Suc) (literal False)
    \<close>

definition parser_nested_binder_source_guard ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_nested_binder_source_guard observed =
        sequence (put Suc)
          (literal (observed = Err ParserSecondaryStatus))
    \<close>

definition parser_nested_binder_source_guard_inhomogeneous ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_nested_binder_source_guard_inhomogeneous observed =
        sequence (put Suc)
          (literal
            (observed = Err ParserPrimaryStatus))
    \<close>

definition parser_nested_alias_source_guard ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_nested_alias_source_guard expected whole =
        sequence (put Suc) (literal (whole = expected))
    \<close>

definition parser_nested_alias_binder_source_guard ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression
  \<close>
  where
    \<open>
      parser_nested_alias_binder_source_guard
          expected_whole expected_observed whole observed =
        sequence (put Suc)
          (literal
            (whole = expected_whole \<and>
              observed = expected_observed))
    \<close>

urust_expr parser_nested_overlapping_or_alternatives ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _) |
        (_, Err(NestedStatus::Secondary)) \<Rightarrow> 1,
      (Err(NestedStatus::Secondary), _) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_guarded_or_alternatives ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _) |
        (_, Err(NestedStatus::Secondary))
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> 1,
      (Err(NestedStatus::Secondary), _) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_guarded_or_alternatives_reversed ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (_, Err(NestedStatus::Secondary)) |
        (Err(NestedStatus::Primary), _)
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> 1,
      (Err(NestedStatus::Secondary), _) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_guarded_or_binder ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), observed) |
        (observed, Err(NestedStatus::Secondary))
        if \<epsilon>\<open>
            parser_nested_binder_source_guard observed
          \<close> \<Rightarrow> 1,
      (Err(NestedStatus::Secondary), _) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_guarded_or_differing_binding ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), observed) |
        (observed, Err(NestedStatus::Secondary))
        if \<epsilon>\<open>
            parser_nested_binder_source_guard_inhomogeneous observed
          \<close> \<Rightarrow> 1,
      (Err(NestedStatus::Secondary), _) \<Rightarrow> 2,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_alias_source_guard_match ::
  \<open>
    (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, expected)
  \<open>
    match scrutinee {
      whole @ Err(NestedStatus::Primary)
        if \<epsilon>\<open>
            parser_nested_alias_source_guard expected whole
          \<close> \<Rightarrow> 1,
      _ \<Rightarrow> 2
    }
  \<close>

urust_expr parser_nested_guarded_or_alias_binder ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, expected_whole, expected_observed)
  \<open>
    match scrutinee {
      (whole @ Err(NestedStatus::Primary), observed) |
        (observed, whole @ Err(NestedStatus::Secondary))
        if \<epsilon>\<open>
            parser_nested_alias_binder_source_guard
              expected_whole expected_observed whole observed
          \<close> \<Rightarrow> 1,
      _ \<Rightarrow> 2
    }
  \<close>

urust_expr parser_nested_guarded_different_depth_alias ::
  \<open>
    parser_nested_different_depth_input \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, expected_whole, expected_observed)
  \<open>
    match scrutinee {
      (whole @ Err(NestedStatus::Primary),
        (observed, marker)) |
        (observed, (whole @ Err(NestedStatus::Secondary), marker))
        if \<epsilon>\<open>
            parser_nested_alias_binder_source_guard
              expected_whole expected_observed whole observed
          \<close> \<Rightarrow> marker,
      _ \<Rightarrow> 99
    }
  \<close>

urust_expr parser_nested_guarded_different_depth_alias_reversed ::
  \<open>
    parser_nested_different_depth_input \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (unit, parser_nested_status) result \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, expected_whole, expected_observed)
  \<open>
    match scrutinee {
      (observed, (whole @ Err(NestedStatus::Secondary), marker)) |
        (whole @ Err(NestedStatus::Primary),
          (observed, marker))
        if \<epsilon>\<open>
            parser_nested_alias_binder_source_guard
              expected_whole expected_observed whole observed
          \<close> \<Rightarrow> marker,
      _ \<Rightarrow> 99
    }
  \<close>

urust_expr parser_root_suffix_unguarded_left ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (unit, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _) \<Rightarrow> Ok(()),
      (fallback, _) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_root_suffix_unguarded_right ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (unit, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (_, Err(NestedStatus::Primary)) \<Rightarrow> Ok(()),
      (_, fallback) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_root_suffix_guarded_left ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _)
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> Ok(()),
      (fallback, _) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_root_suffix_guarded_right ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (_, Err(NestedStatus::Primary))
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> Ok(()),
      (_, fallback) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_recursive_coverage_unguarded_left ::
  \<open>
    parser_recursive_coverage_input \<Rightarrow>
      (unit, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      ((Err(NestedStatus::Primary), _), _) \<Rightarrow> Ok(()),
      ((fallback, left_marker), (other, right_marker)) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_recursive_coverage_unguarded_right ::
  \<open>
    parser_recursive_coverage_input \<Rightarrow>
      (unit, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (_, (Err(NestedStatus::Primary), _)) \<Rightarrow> Ok(()),
      ((other, left_marker), (fallback, right_marker)) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_recursive_coverage_guarded_left ::
  \<open>
    parser_recursive_coverage_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      ((Err(NestedStatus::Primary), _), _)
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> Ok(()),
      ((fallback, left_marker), (other, right_marker)) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_recursive_coverage_guarded_right ::
  \<open>
    parser_recursive_coverage_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, (unit, parser_nested_status) result,
        unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (_, (Err(NestedStatus::Primary), _))
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> Ok(()),
      ((other, left_marker), (fallback, right_marker)) \<Rightarrow> fallback
    }
  \<close>

urust_expr parser_nested_exhaustive_outer_shapes ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _) |
        (Ok(_), Ok(_)) |
        (_, Err(NestedStatus::Secondary)) \<Rightarrow> 1,
      _ \<Rightarrow> 3
    }
  \<close>

urust_expr parser_nested_exhaustive_outer_shapes_guarded ::
  \<open>
    parser_nested_overlap_input \<Rightarrow>
      (nat, bool, unit, unit, unit, unit) expression \<Rightarrow>
      (nat, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee, source_guard)
  \<open>
    match scrutinee {
      (Err(NestedStatus::Primary), _) |
        (Ok(_), Ok(_)) |
        (_, Err(NestedStatus::Secondary))
        if \<epsilon>\<open>source_guard\<close> \<Rightarrow> 1,
      _ \<Rightarrow> 3
    }
  \<close>

lemma parser_nested_overlapping_or_second_alternative:
  \<open>
    parser_nested_overlapping_or_alternatives
        parser_nested_overlap_scrutinee =
      literal (1 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_overlapping_or_alternatives_def
      parser_nested_overlap_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_overlapping_or_first_alternative:
  \<open>
    parser_nested_overlapping_or_alternatives
        parser_nested_or_overlap_reverse_scrutinee =
      literal (1 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_overlapping_or_alternatives_def
      parser_nested_or_overlap_reverse_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_overlapping_or_later_arm:
  \<open>
    parser_nested_overlapping_or_alternatives
        parser_nested_or_overlap_later_scrutinee =
      literal (2 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_overlapping_or_alternatives_def
      parser_nested_or_overlap_later_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_overlapping_or_wildcard:
  \<open>
    parser_nested_overlapping_or_alternatives
        parser_nested_or_overlap_wildcard_scrutinee =
      literal (3 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_overlapping_or_alternatives_def
      parser_nested_or_overlap_wildcard_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_guarded_or_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives
        parser_nested_overlap_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_def
      parser_nested_overlap_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_reversed_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives_reversed
        parser_nested_or_overlap_reversed_second_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_reversed_def
      parser_nested_or_overlap_reversed_second_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_both_miss:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives
        parser_nested_or_overlap_later_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (2 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_def
      parser_nested_or_overlap_later_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_false:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives
        parser_nested_overlap_scrutinee
        parser_nested_source_guard_false)
      0 =
    Success (2 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_def
      parser_nested_overlap_scrutinee_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_first_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives
        parser_nested_or_overlap_reverse_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_def
      parser_nested_or_overlap_reverse_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_wildcard:
  \<open>
    evaluate
      (parser_nested_guarded_or_alternatives
        parser_nested_or_overlap_wildcard_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (3 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alternatives_def
      parser_nested_or_overlap_wildcard_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_binder_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_binder
        parser_nested_overlap_scrutinee)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_binder_def
      parser_nested_overlap_scrutinee_def
      parser_nested_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_binder_overlapping_first_binding:
  \<open>
    evaluate
      (parser_nested_guarded_or_binder
        parser_nested_or_overlap_both_scrutinee)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_binder_def
      parser_nested_or_overlap_both_scrutinee_def
      parser_nested_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_guarded_or_differing_binding_once:
  \<open>
    evaluate
      (parser_nested_guarded_or_differing_binding
        parser_nested_or_overlap_both_scrutinee)
      0 =
    Success (3 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_differing_binding_def
      parser_nested_or_overlap_both_scrutinee_def
      parser_nested_binder_source_guard_inhomogeneous_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_source_guard_hit:
  \<open>
    evaluate
      (parser_nested_alias_source_guard_match
        (Err ParserPrimaryStatus)
        (Err ParserPrimaryStatus))
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_alias_source_guard_match_def
      parser_nested_alias_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_source_guard_false:
  \<open>
    evaluate
      (parser_nested_alias_source_guard_match
        (Err ParserPrimaryStatus)
        (Err ParserSecondaryStatus))
      0 =
    Success (2 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_alias_source_guard_match_def
      parser_nested_alias_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_source_guard_pattern_miss:
  \<open>
    evaluate
      (parser_nested_alias_source_guard_match
        (Err ParserSecondaryStatus)
        (Err ParserSecondaryStatus))
      0 =
    Success (2 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_alias_source_guard_match_def
      parser_nested_alias_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_binder_first_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_alias_binder
        parser_nested_alias_binder_first_scrutinee
        (Err ParserPrimaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alias_binder_def
      parser_nested_alias_binder_first_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_binder_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_or_alias_binder
        parser_nested_alias_binder_second_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alias_binder_def
      parser_nested_alias_binder_second_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_alias_binder_false_skips_arm:
  \<open>
    evaluate
      (parser_nested_guarded_or_alias_binder
        parser_nested_or_overlap_both_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserPrimaryStatus))
      0 =
    Success (2 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_or_alias_binder_def
      parser_nested_or_overlap_both_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_first_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias
        parser_nested_different_depth_first_scrutinee
        (Err ParserPrimaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (11 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_def
      parser_nested_different_depth_first_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias
        parser_nested_different_depth_second_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (22 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_def
      parser_nested_different_depth_second_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_reversed_first_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias_reversed
        parser_nested_different_depth_second_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (22 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_reversed_def
      parser_nested_different_depth_second_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_reversed_second_alternative:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias_reversed
        parser_nested_different_depth_first_scrutinee
        (Err ParserPrimaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (11 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_reversed_def
      parser_nested_different_depth_first_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_false_skips_arm:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias
        parser_nested_different_depth_both_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserPrimaryStatus))
      0 =
    Success (99 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_def
      parser_nested_different_depth_both_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_reversed_false_skips_arm:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias_reversed
        parser_nested_different_depth_both_scrutinee
        (Err ParserPrimaryStatus)
        (Err ParserSecondaryStatus))
      0 =
    Success (99 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_reversed_def
      parser_nested_different_depth_both_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_miss:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias
        parser_nested_different_depth_miss_scrutinee
        (Err ParserPrimaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (99 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_def
      parser_nested_different_depth_miss_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_different_depth_reversed_miss:
  \<open>
    evaluate
      (parser_nested_guarded_different_depth_alias_reversed
        parser_nested_different_depth_miss_scrutinee
        (Err ParserSecondaryStatus)
        (Err ParserTertiaryStatus))
      0 =
    Success (99 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_guarded_different_depth_alias_reversed_def
      parser_nested_different_depth_miss_scrutinee_def
      parser_nested_alias_binder_source_guard_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_unguarded_left_match:
  \<open>
    parser_root_suffix_unguarded_left
        parser_nested_or_overlap_reverse_scrutinee =
      literal (Ok ())
  \<close>
  by
    (simp add:
      parser_root_suffix_unguarded_left_def
      parser_nested_or_overlap_reverse_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_root_suffix_unguarded_left_fallback:
  \<open>
    parser_root_suffix_unguarded_left
        parser_nested_overlap_scrutinee =
      literal (Err ParserSecondaryStatus)
  \<close>
  by
    (simp add:
      parser_root_suffix_unguarded_left_def
      parser_nested_overlap_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_root_suffix_unguarded_right_match:
  \<open>
    parser_root_suffix_unguarded_right
        parser_nested_or_overlap_later_scrutinee =
      literal (Ok ())
  \<close>
  by
    (simp add:
      parser_root_suffix_unguarded_right_def
      parser_nested_or_overlap_later_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_root_suffix_unguarded_right_fallback:
  \<open>
    parser_root_suffix_unguarded_right
        parser_nested_overlap_scrutinee =
      literal (Err ParserSecondaryStatus)
  \<close>
  by
    (simp add:
      parser_root_suffix_unguarded_right_def
      parser_nested_overlap_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_root_suffix_guarded_left_true:
  \<open>
    evaluate
      (parser_root_suffix_guarded_left
        parser_nested_or_overlap_reverse_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (Ok ()) 1
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_left_def
      parser_nested_or_overlap_reverse_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_guarded_left_false:
  \<open>
    evaluate
      (parser_root_suffix_guarded_left
        parser_nested_or_overlap_reverse_scrutinee
        parser_nested_source_guard_false)
      0 =
    Success (Err ParserPrimaryStatus) 1
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_left_def
      parser_nested_or_overlap_reverse_scrutinee_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_guarded_left_structural_miss:
  \<open>
    evaluate
      (parser_root_suffix_guarded_left
        parser_nested_overlap_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (Err ParserSecondaryStatus) 0
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_left_def
      parser_nested_overlap_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_guarded_right_true:
  \<open>
    evaluate
      (parser_root_suffix_guarded_right
        parser_nested_or_overlap_later_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (Ok ()) 1
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_right_def
      parser_nested_or_overlap_later_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_guarded_right_false:
  \<open>
    evaluate
      (parser_root_suffix_guarded_right
        parser_nested_or_overlap_later_scrutinee
        parser_nested_source_guard_false)
      0 =
    Success (Err ParserPrimaryStatus) 1
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_right_def
      parser_nested_or_overlap_later_scrutinee_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_root_suffix_guarded_right_structural_miss:
  \<open>
    evaluate
      (parser_root_suffix_guarded_right
        parser_nested_overlap_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (Err ParserSecondaryStatus) 0
  \<close>
  by
    (simp add:
      parser_root_suffix_guarded_right_def
      parser_nested_overlap_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_unguarded_left_match:
  \<open>
    parser_recursive_coverage_unguarded_left
        parser_recursive_coverage_left_match =
      literal (Ok ())
  \<close>
  by
    (simp add:
      parser_recursive_coverage_unguarded_left_def
      parser_recursive_coverage_left_match_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_recursive_coverage_unguarded_left_fallback:
  \<open>
    parser_recursive_coverage_unguarded_left
        parser_recursive_coverage_fallback =
      literal (Err ParserSecondaryStatus)
  \<close>
  by
    (simp add:
      parser_recursive_coverage_unguarded_left_def
      parser_recursive_coverage_fallback_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_recursive_coverage_unguarded_right_match:
  \<open>
    parser_recursive_coverage_unguarded_right
        parser_recursive_coverage_right_match =
      literal (Ok ())
  \<close>
  by
    (simp add:
      parser_recursive_coverage_unguarded_right_def
      parser_recursive_coverage_right_match_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_recursive_coverage_unguarded_right_fallback:
  \<open>
    parser_recursive_coverage_unguarded_right
        parser_recursive_coverage_fallback =
      literal (Err ParserTertiaryStatus)
  \<close>
  by
    (simp add:
      parser_recursive_coverage_unguarded_right_def
      parser_recursive_coverage_fallback_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_recursive_coverage_guarded_left_true:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_left
        parser_recursive_coverage_left_match
        parser_nested_source_guard_true)
      0 =
    Success (Ok ()) 1
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_left_def
      parser_recursive_coverage_left_match_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_guarded_left_false:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_left
        parser_recursive_coverage_left_match
        parser_nested_source_guard_false)
      0 =
    Success (Err ParserPrimaryStatus) 1
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_left_def
      parser_recursive_coverage_left_match_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_guarded_left_structural_miss:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_left
        parser_recursive_coverage_fallback
        parser_nested_source_guard_true)
      0 =
    Success (Err ParserSecondaryStatus) 0
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_left_def
      parser_recursive_coverage_fallback_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_guarded_right_true:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_right
        parser_recursive_coverage_right_match
        parser_nested_source_guard_true)
      0 =
    Success (Ok ()) 1
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_right_def
      parser_recursive_coverage_right_match_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_guarded_right_false:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_right
        parser_recursive_coverage_right_match
        parser_nested_source_guard_false)
      0 =
    Success (Err ParserPrimaryStatus) 1
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_right_def
      parser_recursive_coverage_right_match_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_recursive_coverage_guarded_right_structural_miss:
  \<open>
    evaluate
      (parser_recursive_coverage_guarded_right
        parser_recursive_coverage_fallback
        parser_nested_source_guard_true)
      0 =
    Success (Err ParserTertiaryStatus) 0
  \<close>
  by
    (simp add:
      parser_recursive_coverage_guarded_right_def
      parser_recursive_coverage_fallback_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_exhaustive_first_miss:
  \<open>
    parser_nested_exhaustive_outer_shapes
        parser_nested_exhaustive_first_miss_scrutinee =
      literal (3 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_def
      parser_nested_exhaustive_first_miss_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_exhaustive_third_miss:
  \<open>
    parser_nested_exhaustive_outer_shapes
        parser_nested_exhaustive_third_miss_scrutinee =
      literal (3 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_def
      parser_nested_exhaustive_third_miss_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_exhaustive_middle_match:
  \<open>
    parser_nested_exhaustive_outer_shapes
        parser_nested_or_overlap_wildcard_scrutinee =
      literal (1 :: nat)
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_def
      parser_nested_or_overlap_wildcard_scrutinee_def
      two_armed_conditional_def
      micro_rust_simps)

lemma parser_nested_exhaustive_guarded_first_miss:
  \<open>
    evaluate
      (parser_nested_exhaustive_outer_shapes_guarded
        parser_nested_exhaustive_first_miss_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (3 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_guarded_def
      parser_nested_exhaustive_first_miss_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_exhaustive_guarded_third_miss:
  \<open>
    evaluate
      (parser_nested_exhaustive_outer_shapes_guarded
        parser_nested_exhaustive_third_miss_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (3 :: nat) 0
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_guarded_def
      parser_nested_exhaustive_third_miss_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_exhaustive_guarded_middle_match:
  \<open>
    evaluate
      (parser_nested_exhaustive_outer_shapes_guarded
        parser_nested_or_overlap_wildcard_scrutinee
        parser_nested_source_guard_true)
      0 =
    Success (1 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_guarded_def
      parser_nested_or_overlap_wildcard_scrutinee_def
      parser_nested_source_guard_true_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

lemma parser_nested_exhaustive_guarded_false:
  \<open>
    evaluate
      (parser_nested_exhaustive_outer_shapes_guarded
        parser_nested_or_overlap_wildcard_scrutinee
        parser_nested_source_guard_false)
      0 =
    Success (3 :: nat) 1
  \<close>
  by
    (simp add:
      parser_nested_exhaustive_outer_shapes_guarded_def
      parser_nested_or_overlap_wildcard_scrutinee_def
      parser_nested_source_guard_false_def
      two_armed_conditional_def
      micro_rust_simps
      evaluate_def
      sequence_def
      put_def
      literal_def
      Core_Expression.bind.simps)

urust_expr parser_nested_alias_wildcard ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<llangle>parser_nested_alias_wild_scrutinee\<rrangle> {
      Err(NestedStatus::Tertiary) \<Rightarrow> 0,
      whole @ Err(NestedStatus::Primary) \<Rightarrow>
        \<llangle>parser_nested_alias_tag whole\<rrangle>,
      _ \<Rightarrow> 2
    }
  \<close>

urust_expr parser_nested_alias_binder ::
  \<open>
    (unit, (unit, parser_nested_status) result,
      unit, unit, unit, unit) expression
  \<close>
  \<open>
    match \<llangle>parser_nested_alias_binder_scrutinee\<rrangle> {
      Err(NestedStatus::Tertiary) \<Rightarrow>
        \<llangle>parser_nested_alias_probe_result\<rrangle>,
      whole @ Err(NestedStatus::Primary) \<Rightarrow>
        \<llangle>parser_nested_alias_rewrite whole\<rrangle>,
      res \<Rightarrow> res
    }
  \<close>

lemma parser_nested_registered_ordered_evaluation:
  \<open>parser_nested_registered_ordered = literal (2 :: nat)\<close>
  by (simp add: parser_nested_registered_ordered_def micro_rust_simps)

lemma parser_nested_registered_or_ordered_evaluation:
  \<open>parser_nested_registered_or_ordered = literal (1 :: nat)\<close>
  by (simp add: parser_nested_registered_or_ordered_def micro_rust_simps)

lemma parser_nested_registered_guard_order_evaluation:
  assumes \<open>parser_nested_guarded_scrutinee = Err ParserPrimaryStatus\<close>
      and \<open>parser_nested_guard_marker\<close>
  shows \<open>parser_nested_registered_guard_order = literal (1 :: nat)\<close>
  by (simp add: assms parser_nested_registered_guard_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_registered_guard_fallback_evaluation:
  assumes \<open>parser_nested_guarded_scrutinee = Err ParserPrimaryStatus\<close>
      and \<open>\<not> parser_nested_guard_marker\<close>
  shows \<open>parser_nested_registered_guard_order = literal (2 :: nat)\<close>
  by (simp add: assms parser_nested_registered_guard_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_global_primary_evaluation:
  assumes \<open>parser_nested_interleaved_scrutinee = Err ParserPrimaryStatus\<close>
  shows \<open>parser_nested_global_source_order = literal (1 :: nat)\<close>
  by (simp add: assms parser_nested_global_source_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_global_guard_evaluation:
  assumes \<open>parser_nested_interleaved_scrutinee = Err ParserSecondaryStatus\<close>
      and \<open>parser_nested_interleaved_guard\<close>
  shows \<open>parser_nested_global_source_order = literal (2 :: nat)\<close>
  by (simp add: assms parser_nested_global_source_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_global_secondary_evaluation:
  assumes \<open>parser_nested_interleaved_scrutinee = Err ParserSecondaryStatus\<close>
      and \<open>\<not> parser_nested_interleaved_guard\<close>
  shows \<open>parser_nested_global_source_order = literal (3 :: nat)\<close>
  by (simp add: assms parser_nested_global_source_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_global_fallback_evaluation:
  assumes \<open>parser_nested_interleaved_scrutinee = Ok ()\<close>
      and \<open>\<not> parser_nested_interleaved_guard\<close>
  shows \<open>parser_nested_global_source_order = literal (4 :: nat)\<close>
  by (simp add: assms parser_nested_global_source_order_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_alias_wildcard_evaluations:
  assumes \<open>parser_nested_alias_wild_scrutinee = Err ParserPrimaryStatus\<close>
  shows
    \<open>parser_nested_alias_wildcard =
      literal (parser_nested_alias_tag (Err ParserPrimaryStatus))\<close>
  by (simp add: assms parser_nested_alias_wildcard_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_alias_wildcard_fallback_evaluations:
  assumes \<open>parser_nested_alias_wild_scrutinee = Err ParserSecondaryStatus\<close>
  shows \<open>parser_nested_alias_wildcard = literal (2 :: nat)\<close>
  by (simp add: assms parser_nested_alias_wildcard_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_alias_binder_evaluations:
  assumes \<open>parser_nested_alias_binder_scrutinee = Err ParserPrimaryStatus\<close>
  shows
    \<open>parser_nested_alias_binder =
      literal (parser_nested_alias_rewrite (Err ParserPrimaryStatus))\<close>
  by (simp add: assms parser_nested_alias_binder_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_nested_alias_binder_fallback_evaluations:
  assumes \<open>parser_nested_alias_binder_scrutinee = Err ParserSecondaryStatus\<close>
  shows
    \<open>parser_nested_alias_binder = literal (Err ParserSecondaryStatus)\<close>
  by (simp add: assms parser_nested_alias_binder_def
      two_armed_conditional_def micro_rust_simps)

declare [[urust_conformance = false]]

urust_expr parser_nested_registered_payload
  \<open>
    match \<llangle>Some (ParserNativePayload 7)\<rrangle> {
      Some(ParserNative::Payload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

section\<open>Matcher mechanism regression audit\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("matcher mechanism audit: " ^ message)

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun rhs_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals
      |> snd

    fun outer_case_clauses rhs =
      let
        val (parameters, body) = Term.strip_abs rhs
        val names =
          Name.variants Name.context
            (map (fn (name, _) =>
              if name = "" then "parameter" else name)
              parameters)
        val frees = map Free (names ~~ map snd parameters)
        val body' = subst_bounds (rev frees, body)
        val selector =
          (case body' of
             Const (name, _) $ _ $ continuation =>
               if name = \<^const_name>\<open>bind\<close>
               then snd (Term.dest_abs_global continuation)
               else error "expected outer scrutinee bind"
           | _ => error "expected outer scrutinee bind")
      in
        (case Case_Translation.strip_case ctxt false selector of
           SOME (_, clauses) => clauses
         | NONE => error "expected outer structural case")
      end

    val direct_names =
      ["parser_four_axis_structural_matrix",
       "parser_small_structural_matrix",
       "parser_closed_structural_matrix",
       "parser_structural_or_matrix",
       "parser_partial_structural_matrix",
       "parser_explicit_fallback_structural_matrix",
       "parser_effectful_structural_matrix"]

    fun audit_direct name =
      let val rhs = rhs_of name
      in
        (assert (name ^ " duplicated its outer scrutinee bind")
          (count_constant \<^const_name>\<open>bind\<close> rhs = 1);
         assert (name ^ " generated a structural equality test")
          (count_constant \<^const_name>\<open>urust_eq\<close> rhs = 0);
         assert (name ^ " retained schematic variables")
          (null (Term.add_vars rhs []));
         assert (name ^ " retained local free binders")
          (null (Term.add_frees rhs [])))
      end

    val _ = List.app audit_direct direct_names
    val _ =
      assert "four-axis matrix changed its 16-clause source expansion"
        (length
          (outer_case_clauses
            (rhs_of "parser_four_axis_structural_matrix")) = 16)
    val _ =
      assert "small open matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_small_structural_matrix")) = 3)
    val _ =
      assert "small closed matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_closed_structural_matrix")) = 3)
    val _ =
      assert "structural or-pattern changed its normalized clause shape"
        (length
          (outer_case_clauses
            (rhs_of "parser_structural_or_matrix")) = 2)
    val _ =
      assert "explicit fallback matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_explicit_fallback_structural_matrix")) = 2)
    val _ =
      assert "complete structural matrices retained undefined fallbacks"
        (List.all
          (fn name =>
            count_constant \<^const_name>\<open>undefined\<close>
              (rhs_of name) = 0)
          ["parser_four_axis_structural_matrix",
           "parser_small_structural_matrix",
           "parser_closed_structural_matrix",
           "parser_structural_or_matrix",
           "parser_explicit_fallback_structural_matrix",
           "parser_effectful_structural_matrix"])
    val _ =
      assert "partial structural matrix lost its terminal fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          (rhs_of "parser_partial_structural_matrix") > 0)

    val open_b1 = rhs_of "parser_nested_registered_nullary_open"
    val SOME (nested_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserPrimaryStatus\<close>,
         fastype_of \<^term>\<open>ParserPrimaryStatus\<close>)
    val nested_case_name =
      (case Term.head_of nested_case of
         Const (name, _) => name
       | _ => error "expected nested constructor case constant")
    val _ =
      assert "open B1 fixture retained a constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> open_b1 = 0)
    val _ =
      assert "open B1 fixture lost its nested constructor case"
        (count_constant nested_case_name open_b1 > 0)
    val _ =
      assert "open B1 fixture duplicated its scrutinee bind"
        (count_constant \<^const_name>\<open>bind\<close> open_b1 = 1)
    val _ =
      assert "open B1 fixture retained synthetic variables or frees"
        (null (Term.add_vars open_b1 []) andalso
         null (Term.add_frees open_b1 []))

    val metadata_free_switch =
      rhs_of "parser_metadata_free_switch"
    val metadata_free_case =
      rhs_of "parser_metadata_free_case"
    val literal_switch =
      rhs_of "parser_literal_switch"
    val _ =
      assert "metadata-free registered values lost switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          metadata_free_switch = 1)
    val _ =
      assert "metadata-free registered values lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          metadata_free_case = 1)
    val _ =
      assert "integer literals lost switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          literal_switch = 1)

    val registered_singleton =
      rhs_of "parser_nested_registered_singleton"
    val native_singleton =
      rhs_of "parser_nested_native_singleton"
    val _ =
      assert "registered singleton retained a redundant nested fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          registered_singleton = 0)
    val _ =
      assert "native singleton retained a redundant nested fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          native_singleton = 0)
    val _ =
      assert "singleton payloads were converted to equality tests"
        (count_constant \<^const_name>\<open>urust_eq\<close>
            registered_singleton = 0 andalso
         count_constant \<^const_name>\<open>urust_eq\<close>
            native_singleton = 0)

    val _ =
      assert "partial and rich nested patterns lost necessary fallbacks"
        (List.all
          (fn name =>
            count_constant \<^const_name>\<open>undefined\<close>
              (rhs_of name) > 0)
          ["parser_nested_partial_constructor_alias",
           "parser_nested_value_fallback",
           "parser_nested_range_fallback"])
  in
    val _ = ()
  end
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
    val word_path = make_path "ParserWordFamily::Second"
    val word_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position word_path)
    val word_second = resolve "ParserWordFamily::Second"
    val word_family =
      the (URust_Resolution.constructor_family word_second)
    val single_word_only =
      resolve "ParserSingleWordFamily::ParserWordOnly"
    val single_word_family =
      the (URust_Resolution.constructor_family single_word_only)
    val (word_case, word_case_members) =
      the
        (Case_Translation.lookup_by_constr_permissive ctxt
          (dest_Const_name \<^term>\<open>ParserWordSecond\<close>,
           fastype_of \<^term>\<open>ParserWordSecond\<close>))
    val raw_path = make_path "ParserRaw::First"
    val raw_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position raw_path)

    val (_, native_members) = native_family
    val (_, word_members) = word_family
    val (_, single_word_members) = single_word_family
    val word_case_name =
      dest_Const_name \<^term>\<open>case_parser_word_family\<close>
    val single_word_case_name =
      dest_Const_name \<^term>\<open>case_parser_single_word_family\<close>
    val _ =
      assert "custom enum positional arity was not recovered"
        (URust_Resolution.constructor_arity native_payload = 1)
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
      assert "simple_word_enum native case registration changed"
        (constant_name word_case = word_case_name andalso
          map constant_name word_case_members =
            map constant_name
              [\<^term>\<open>ParserWordFirst\<close>,
               \<^term>\<open>ParserWordSecond\<close>,
               \<^term>\<open>ParserWordThird\<close>])
    val _ =
      assert "simple_word_enum was not classified as a registered constructor"
        (URust_Resolution.classify_registered_literal ctxt
          word_resolver word_path =
            URust_Resolution.Registered_Constructor_Literal)
    val _ =
      assert "simple_word_enum constructor arity changed"
        (URust_Resolution.constructor_arity word_second = 0)
    val _ =
      assert "simple_word_enum unexpectedly became a Code constructor"
        (not (Code.is_constr theory
          (dest_Const_name \<^term>\<open>ParserWordSecond\<close>)))
    val _ =
      assert "singleton simple_word_enum family changed"
        (map constant_name single_word_members =
          [constant_name \<^term>\<open>ParserWordOnly\<close>])
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

    val word_exhaustive =
      rhs_of "parser_word_family_exhaustive"
    val word_partial =
      rhs_of "parser_word_family_partial"
    val word_guarded =
      rhs_of "parser_word_family_guarded"
    val word_matches =
      rhs_of "parser_word_family_matches"
    val word_nested =
      rhs_of "parser_word_family_nested"
    val word_legacy_nested =
      rhs_of "parser_word_family_legacy_nested"
    val single_word_exhaustive =
      rhs_of "parser_single_word_family_exhaustive"
    val _ =
      assert "exhaustive simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_exhaustive = 1)
    val _ =
      assert "exhaustive simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_exhaustive = 0)
    val _ =
      assert "exhaustive simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_exhaustive = 0)
    val _ =
      assert "partial simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_partial = 1)
    val _ =
      assert "partial simple_word_enum match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_partial > 0)
    val _ =
      assert "partial simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_partial = 0)
    val _ =
      assert "guarded simple_word_enum match lost structural lowering"
        (count_constant word_case_name word_guarded > 0)
    val _ =
      assert "guarded simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_guarded = 0)
    val _ =
      assert "simple_word_enum matches! lost structural lowering"
        (count_constant word_case_name word_matches = 1)
    val _ =
      assert "simple_word_enum matches! retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_matches = 0)
    val _ =
      assert "nested simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_nested = 1)
    val _ =
      assert "nested exhaustive simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_nested = 0)
    val _ =
      assert "nested simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_nested = 0)
    val _ =
      assert "legacy nested simple_word_enum unexpectedly retained its constructor"
        (count_constant \<^const_name>\<open>ParserWordFirst\<close>
          word_legacy_nested = 0)
    val _ =
      assert "legacy nested simple_word_enum unexpectedly used its native case"
        (count_constant word_case_name word_legacy_nested = 0)
    val _ =
      assert "singleton simple_word_enum match lost its case combinator"
        (count_constant single_word_case_name
          single_word_exhaustive = 1)
    val _ =
      assert "singleton simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          single_word_exhaustive = 0)

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
      assert "nested fixture differs from its complete conformance term"
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
    fun result_case_branches term =
      let
        fun seek candidate =
          (case Term.strip_comb candidate of
             (Const (name, _), [ok_branch, err_branch, _]) =>
               if name = result_case_name
               then SOME (ok_branch, err_branch)
               else seek_arguments candidate
           | _ => seek_arguments candidate)
        and seek_arguments (left $ right) =
              (case seek left of
                 SOME result => SOME result
               | NONE => seek right)
          | seek_arguments (Abs (_, _, body)) = seek body
          | seek_arguments _ = NONE
      in
        (case seek term of
           SOME branches => branches
         | NONE =>
             error
               "constructor matching audit: missing outer result case")
      end
    val _ =
      assert "nested normalization lost the enclosing authentic case"
        (count_constant result_case_name nested > 0)
    val _ =
      assert "nested exact nullary constructor lost its native inner case"
        (count_constant inner_case_name nested > 0)
    val _ =
      assert "nested exact nullary constructor retained an equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close> nested = 0)

    fun checked_structural_term name =
      let
        val rhs = rhs_of name
        val _ =
          assert (name ^ " retained a constructor equality")
            (count_constant \<^const_name>\<open>urust_eq\<close> rhs = 0)
        val _ =
          assert (name ^ " lost structural constructor matching")
            (count_constant inner_case_name rhs > 0)
        val _ =
          assert (name ^ " retained schematic variables")
            (null (Term.add_vars rhs []))
        val _ =
          assert (name ^ " retained local free binders")
            (null (Term.add_frees rhs []))
      in rhs end

    fun instantiate_definition rhs arguments =
      Envir.beta_eta_contract
        (Term.list_comb (rhs, arguments))

    fun outer_case_selector rhs =
      let
        val (parameters, body) = Term.strip_abs rhs
        val names =
          Name.variants Name.context
            (map (fn (name, _) =>
              if name = "" then "parameter" else name)
              parameters)
        val frees =
          map Free (names ~~ map snd parameters)
        val body' = subst_bounds (rev frees, body)
      in
        (case body' of
           Const (name, _) $ _ $ continuation =>
             if name = \<^const_name>\<open>bind\<close>
             then snd (Term.dest_abs_global continuation)
             else
               error
                 "constructor matching audit: expected outer scrutinee bind"
         | _ =>
             error
               "constructor matching audit: expected outer scrutinee bind")
      end

    fun outer_case_clauses rhs =
      (case Case_Translation.strip_case ctxt false
          (outer_case_selector rhs) of
         SOME (_, clauses) => clauses
       | NONE =>
           error
             "constructor matching audit: expected outer case")

    val status_constructor_names =
      map constant_name
        [\<^term>\<open>ParserPrimaryStatus\<close>,
         \<^term>\<open>ParserSecondaryStatus\<close>,
         \<^term>\<open>ParserTertiaryStatus\<close>]

    fun selected_constructors selected term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if member (op =) selected name
              then cons name
              else I
          | _ => I)
        term []
      |> rev

    fun structural_constructor_rows selected rhs =
      map (selected_constructors selected o fst)
        (outer_case_clauses rhs)

    fun structural_status_rows rhs =
      structural_constructor_rows status_constructor_names rhs

    val ordered =
      checked_structural_term
        "parser_nested_registered_ordered"
    val ordered_or =
      checked_structural_term
        "parser_nested_registered_or_ordered"
    val guarded_order =
      checked_structural_term
        "parser_nested_registered_guard_order"
    val global_source_order =
      checked_structural_term
        "parser_nested_global_source_order"
    val overlapping_tuple =
      checked_structural_term
        "parser_nested_overlapping_tuple"
    val (overlapping_or_lhs, overlapping_or) =
      equation_of "parser_nested_overlapping_or_alternatives"
    val (guarded_or_lhs, guarded_or) =
      equation_of "parser_nested_guarded_or_alternatives"
    val (guarded_or_reversed_lhs, guarded_or_reversed) =
      equation_of "parser_nested_guarded_or_alternatives_reversed"
    val (guarded_or_binder_lhs, guarded_or_binder) =
      equation_of "parser_nested_guarded_or_binder"
    val (differing_binding_lhs, differing_binding) =
      equation_of "parser_nested_guarded_or_differing_binding"
    val (alias_source_guard_lhs, alias_source_guard) =
      equation_of "parser_nested_alias_source_guard_match"
    val (alias_binder_guard_lhs, alias_binder_guard) =
      equation_of "parser_nested_guarded_or_alias_binder"
    val (different_depth_lhs, different_depth) =
      equation_of "parser_nested_guarded_different_depth_alias"
    val (different_depth_reversed_lhs,
         different_depth_reversed) =
      equation_of
        "parser_nested_guarded_different_depth_alias_reversed"
    val (exhaustive_lhs, exhaustive) =
      equation_of "parser_nested_exhaustive_outer_shapes"
    val (exhaustive_guarded_lhs, exhaustive_guarded) =
      equation_of "parser_nested_exhaustive_outer_shapes_guarded"
    val (root_unguarded_left_lhs, root_unguarded_left) =
      equation_of "parser_root_suffix_unguarded_left"
    val (root_unguarded_right_lhs, root_unguarded_right) =
      equation_of "parser_root_suffix_unguarded_right"
    val (root_guarded_left_lhs, root_guarded_left) =
      equation_of "parser_root_suffix_guarded_left"
    val (root_guarded_right_lhs, root_guarded_right) =
      equation_of "parser_root_suffix_guarded_right"
    val (recursive_unguarded_left_lhs,
         recursive_unguarded_left) =
      equation_of "parser_recursive_coverage_unguarded_left"
    val (recursive_unguarded_right_lhs,
         recursive_unguarded_right) =
      equation_of "parser_recursive_coverage_unguarded_right"
    val (recursive_guarded_left_lhs,
         recursive_guarded_left) =
      equation_of "parser_recursive_coverage_guarded_left"
    val (recursive_guarded_right_lhs,
         recursive_guarded_right) =
      equation_of "parser_recursive_coverage_guarded_right"
    val guarded_or_instantiated =
      instantiate_definition guarded_or
        [\<^term>\<open>parser_nested_overlap_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val guarded_or_reversed_instantiated =
      instantiate_definition guarded_or_reversed
        [\<^term>\<open>
            parser_nested_or_overlap_reversed_second_scrutinee
          \<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val guarded_or_binder_instantiated =
      instantiate_definition guarded_or_binder
        [\<^term>\<open>parser_nested_overlap_scrutinee\<close>]
    val alias_binder_guard_instantiated =
      instantiate_definition alias_binder_guard
        [\<^term>\<open>parser_nested_alias_binder_first_scrutinee\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>,
         \<^term>\<open>Err ParserTertiaryStatus\<close>]
    val different_depth_instantiated =
      instantiate_definition different_depth
        [\<^term>\<open>parser_nested_different_depth_both_scrutinee\<close>,
         \<^term>\<open>Err ParserSecondaryStatus\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>]
    val different_depth_reversed_instantiated =
      instantiate_definition different_depth_reversed
        [\<^term>\<open>parser_nested_different_depth_both_scrutinee\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>,
         \<^term>\<open>Err ParserSecondaryStatus\<close>]
    val exhaustive_guarded_instantiated =
      instantiate_definition exhaustive_guarded
        [\<^term>\<open>
            parser_nested_exhaustive_first_miss_scrutinee
          \<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val root_unguarded_left_instantiated =
      instantiate_definition root_unguarded_left
        [\<^term>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>]
    val root_unguarded_right_instantiated =
      instantiate_definition root_unguarded_right
        [\<^term>\<open>parser_nested_or_overlap_later_scrutinee\<close>]
    val root_guarded_left_instantiated =
      instantiate_definition root_guarded_left
        [\<^term>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_false\<close>]
    val root_guarded_right_instantiated =
      instantiate_definition root_guarded_right
        [\<^term>\<open>parser_nested_or_overlap_later_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val recursive_unguarded_left_instantiated =
      instantiate_definition recursive_unguarded_left
        [\<^term>\<open>parser_recursive_coverage_fallback\<close>]
    val recursive_unguarded_right_instantiated =
      instantiate_definition recursive_unguarded_right
        [\<^term>\<open>parser_recursive_coverage_fallback\<close>]
    val recursive_guarded_left_instantiated =
      instantiate_definition recursive_guarded_left
        [\<^term>\<open>parser_recursive_coverage_left_match\<close>,
         \<^term>\<open>parser_nested_source_guard_false\<close>]
    val recursive_guarded_right_instantiated =
      instantiate_definition recursive_guarded_right
        [\<^term>\<open>parser_recursive_coverage_right_match\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val (global_ok_branch, global_err_branch) =
      result_case_branches global_source_order
    val alias_wildcard =
      checked_structural_term
        "parser_nested_alias_wildcard"
    val alias_binder =
      checked_structural_term
        "parser_nested_alias_binder"
    val (alias_wildcard_lhs, _) =
      equation_of "parser_nested_alias_wildcard"
    val (alias_binder_lhs, _) =
      equation_of "parser_nested_alias_binder"
    val (global_source_order_lhs, _) =
      equation_of "parser_nested_global_source_order"
    val (overlapping_tuple_lhs, _) =
      equation_of "parser_nested_overlapping_tuple"
    val (_, alias_wildcard_arguments) =
      Term.strip_comb alias_wildcard_lhs
    val (_, alias_binder_arguments) =
      Term.strip_comb alias_binder_lhs
    val (_, global_source_order_arguments) =
      Term.strip_comb global_source_order_lhs
    val (_, overlapping_tuple_arguments) =
      Term.strip_comb overlapping_tuple_lhs
    val (_, overlapping_or_arguments) =
      Term.strip_comb overlapping_or_lhs
    val (_, guarded_or_arguments) =
      Term.strip_comb guarded_or_lhs
    val (_, guarded_or_reversed_arguments) =
      Term.strip_comb guarded_or_reversed_lhs
    val (_, guarded_or_binder_arguments) =
      Term.strip_comb guarded_or_binder_lhs
    val (_, differing_binding_arguments) =
      Term.strip_comb differing_binding_lhs
    val (_, alias_source_guard_arguments) =
      Term.strip_comb alias_source_guard_lhs
    val (_, alias_binder_guard_arguments) =
      Term.strip_comb alias_binder_guard_lhs
    val (_, different_depth_arguments) =
      Term.strip_comb different_depth_lhs
    val (_, different_depth_reversed_arguments) =
      Term.strip_comb different_depth_reversed_lhs
    val (_, exhaustive_arguments) =
      Term.strip_comb exhaustive_lhs
    val (_, exhaustive_guarded_arguments) =
      Term.strip_comb exhaustive_guarded_lhs
    fun audit_product_case_closure name rhs =
      let
        fun is_product_type (Type (type_name, _)) =
              type_name = \<^type_name>\<open>prod\<close>
          | is_product_type _ = false
        fun is_wildcard_pattern (Free _) = true
          | is_wildcard_pattern (Var _) = true
          | is_wildcard_pattern _ = false
        fun close_bounds bound_types term =
          subst_bounds
            (map_index
              (fn (index, typ) =>
                Free
                  ("_case_audit_" ^ string_of_int index,
                   typ))
              bound_types,
             term)
        fun inspect bound_types term =
          let
            val closed_term =
              close_bounds bound_types term
            val _ =
              (case Case_Translation.strip_case ctxt false
                  closed_term of
                 SOME (scrutinee, clauses) =>
                   if is_product_type (fastype_of scrutinee)
                   then
                     let
                       val wildcard_clauses =
                         filter
                           (is_wildcard_pattern o fst)
                           clauses
                     in
                       assert
                         (name ^
                           " emitted a redundant product wildcard")
                         (null wildcard_clauses)
                     end
                   else ()
               | NONE => ())
          in
            (case term of
               left $ right =>
                 (inspect bound_types left;
                  inspect bound_types right)
             | Abs (_, typ, body) =>
                 inspect (typ :: bound_types) body
             | _ => ())
          end
      in inspect [] rhs end
    fun audit_total_root_suffix
        name lhs rhs expected_argument_types instantiated
        scrutinee_name source_guard_name =
      let
        val (_, arguments) = Term.strip_comb lhs
        val clauses = outer_case_clauses rhs
        val _ =
          assert (name ^ " changed its definition head")
            (null arguments)
        val _ =
          assert (name ^ " changed its argument types")
            (binder_types (fastype_of lhs) =
              expected_argument_types)
        val _ =
          assert (name ^ " retained schematic variables")
            (null (Term.add_vars rhs []))
        val _ =
          assert (name ^ " retained local free binders")
            (null (Term.add_frees rhs []))
        val _ =
          assert (name ^ " duplicated its outer scrutinee bind")
            (count_constant \<^const_name>\<open>bind\<close> rhs = 1)
        val _ =
          assert (name ^ " reevaluated its instantiated scrutinee")
            (count_constant scrutinee_name instantiated = 1)
        val _ =
          assert
            (name ^ " lost its outer structural clauses: " ^
              string_of_int (length clauses))
            (not (null clauses))
        val _ =
          assert (name ^ " retained an undefined fallback")
            (count_constant \<^const_name>\<open>undefined\<close>
              rhs = 0)
        val _ =
          (case source_guard_name of
             NONE => ()
           | SOME guard_name =>
               assert (name ^ " duplicated or lost its source guard")
                 (count_constant guard_name instantiated = 1))
      in () end
    val unguarded_root_argument_types =
      [\<^typ>\<open>parser_nested_overlap_input\<close>]
    val guarded_root_argument_types =
      [\<^typ>\<open>parser_nested_overlap_input\<close>,
       \<^typ>\<open>
         (nat, bool, unit, unit, unit, unit) expression
       \<close>]
    val recursive_unguarded_argument_types =
      [\<^typ>\<open>parser_recursive_coverage_input\<close>]
    val recursive_guarded_argument_types =
      [\<^typ>\<open>parser_recursive_coverage_input\<close>,
       \<^typ>\<open>
         (nat, bool, unit, unit, unit, unit) expression
       \<close>]
    val _ =
      audit_total_root_suffix
        "left unguarded total-root fallback"
        root_unguarded_left_lhs root_unguarded_left
        unguarded_root_argument_types
        root_unguarded_left_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "right unguarded total-root fallback"
        root_unguarded_right_lhs root_unguarded_right
        unguarded_root_argument_types
        root_unguarded_right_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_later_scrutinee\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "left guarded total-root fallback"
        root_guarded_left_lhs root_guarded_left
        guarded_root_argument_types
        root_guarded_left_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_false\<close>)
    val _ =
      audit_total_root_suffix
        "right guarded total-root fallback"
        root_guarded_right_lhs root_guarded_right
        guarded_root_argument_types
        root_guarded_right_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_later_scrutinee\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_true\<close>)
    val _ =
      audit_product_case_closure
        "left unguarded recursive total-root fallback"
        recursive_unguarded_left
    val _ =
      audit_product_case_closure
        "right unguarded recursive total-root fallback"
        recursive_unguarded_right
    val _ =
      audit_product_case_closure
        "left guarded recursive total-root fallback"
        recursive_guarded_left
    val _ =
      audit_product_case_closure
        "right guarded recursive total-root fallback"
        recursive_guarded_right
    val _ =
      audit_total_root_suffix
        "left unguarded recursive total-root fallback"
        recursive_unguarded_left_lhs
        recursive_unguarded_left
        recursive_unguarded_argument_types
        recursive_unguarded_left_instantiated
        \<^const_name>\<open>parser_recursive_coverage_fallback\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "right unguarded recursive total-root fallback"
        recursive_unguarded_right_lhs
        recursive_unguarded_right
        recursive_unguarded_argument_types
        recursive_unguarded_right_instantiated
        \<^const_name>\<open>parser_recursive_coverage_fallback\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "left guarded recursive total-root fallback"
        recursive_guarded_left_lhs
        recursive_guarded_left
        recursive_guarded_argument_types
        recursive_guarded_left_instantiated
        \<^const_name>\<open>parser_recursive_coverage_left_match\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_false\<close>)
    val _ =
      audit_total_root_suffix
        "right guarded recursive total-root fallback"
        recursive_guarded_right_lhs
        recursive_guarded_right
        recursive_guarded_argument_types
        recursive_guarded_right_instantiated
        \<^const_name>\<open>parser_recursive_coverage_right_match\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_true\<close>)
    val _ =
      assert "alias/wildcard fixture acquired an unintended definition argument"
        (null alias_wildcard_arguments)
    val _ =
      assert "alias/wildcard fixture acquired an unintended function type"
        (null (binder_types (fastype_of alias_wildcard_lhs)))
    val _ =
      assert "alias/binder fixture acquired an unintended definition argument"
        (null alias_binder_arguments)
    val _ =
      assert "alias/binder fixture acquired an unintended function type"
        (null (binder_types (fastype_of alias_binder_lhs)))
    val _ =
      assert "global source-order fixture acquired an unintended definition argument"
        (null global_source_order_arguments)
    val _ =
      assert "global source-order fixture acquired an unintended function type"
        (null (binder_types (fastype_of global_source_order_lhs)))
    val _ =
      assert "overlapping tuple fixture acquired an unintended definition argument"
        (null overlapping_tuple_arguments)
    val _ =
      assert "overlapping tuple fixture acquired an unintended function type"
        (null (binder_types (fastype_of overlapping_tuple_lhs)))
    val _ =
      assert "overlapping or-pattern fixture changed its definition head"
        (null overlapping_or_arguments)
    val _ =
      assert "overlapping or-pattern fixture acquired an unintended argument"
        (binder_types (fastype_of overlapping_or_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "overlapping or-pattern fixture retained schematic variables"
        (null (Term.add_vars overlapping_or []))
    val _ =
      assert "overlapping or-pattern fixture retained local free binders"
        (null (Term.add_frees overlapping_or []))
    val _ =
      assert "overlapping or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          overlapping_or = 1)
    val _ =
      assert "guarded or-pattern fixture changed its definition head"
        (null guarded_or_arguments)
    val _ =
      assert "guarded or-pattern fixture changed its argument types"
        (binder_types (fastype_of guarded_or_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>
             (nat, bool, unit, unit, unit, unit) expression
           \<close>])
    val _ =
      assert "guarded or-pattern fixture retained schematic variables"
        (null (Term.add_vars guarded_or []))
    val _ =
      assert "guarded or-pattern fixture retained local free binders"
        (null (Term.add_frees guarded_or []))
    val _ =
      assert "guarded or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or = 1)
    val _ =
      assert "reversed guarded or-pattern fixture changed its definition head"
        (null guarded_or_reversed_arguments)
    val _ =
      assert "reversed guarded or-pattern fixture retained schematic variables"
        (null (Term.add_vars guarded_or_reversed []))
    val _ =
      assert "reversed guarded or-pattern fixture retained local free binders"
        (null (Term.add_frees guarded_or_reversed []))
    val _ =
      assert "reversed guarded or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or_reversed = 1)
    val _ =
      assert "binder-dependent guard fixture changed its definition head"
        (null guarded_or_binder_arguments)
    val _ =
      assert "binder-dependent guard fixture changed its argument type"
        (binder_types (fastype_of guarded_or_binder_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "binder-dependent guard fixture retained schematic variables"
        (null (Term.add_vars guarded_or_binder []))
    val _ =
      assert "binder-dependent guard fixture retained local free binders"
        (null (Term.add_frees guarded_or_binder []))
    val _ =
      assert "binder-dependent guard fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or_binder = 1)
    val _ =
      assert "differing-binding guard fixture changed its definition head"
        (null differing_binding_arguments)
    val _ =
      assert "differing-binding guard fixture changed its argument type"
        (binder_types (fastype_of differing_binding_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "differing-binding guard fixture retained schematic variables"
        (null (Term.add_vars differing_binding []))
    val _ =
      assert "differing-binding guard fixture retained local free binders"
        (null (Term.add_frees differing_binding []))
    val _ =
      assert "differing-binding guard fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_binder_source_guard_inhomogeneous\<close>
          differing_binding > 0)
    val _ =
      assert "alias source-guard fixture changed its definition head"
        (null alias_source_guard_arguments)
    val _ =
      assert "alias source-guard fixture changed its argument types"
        (binder_types (fastype_of alias_source_guard_lhs) =
          [\<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "alias source-guard fixture retained schematic variables"
        (null (Term.add_vars alias_source_guard []))
    val _ =
      assert "alias source-guard fixture retained local free binders"
        (null (Term.add_frees alias_source_guard []))
    val _ =
      assert "alias source-guard fixture lost its scoped alias use"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_source_guard\<close>
          alias_source_guard > 0)
    val _ =
      assert "alias/binder guard fixture changed its definition head"
        (null alias_binder_guard_arguments)
    val _ =
      assert "alias/binder guard fixture changed its argument types"
        (binder_types (fastype_of alias_binder_guard_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "alias/binder guard fixture retained schematic variables"
        (null (Term.add_vars alias_binder_guard []))
    val _ =
      assert "alias/binder guard fixture retained local free binders"
        (null (Term.add_frees alias_binder_guard []))
    val _ =
      assert "alias/binder guard fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          alias_binder_guard > 0)
    val _ =
      assert "alias/binder guard fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_first_scrutinee\<close>
          alias_binder_guard_instantiated = 1)
    val _ =
      assert "different-depth alias fixture changed its definition head"
        (null different_depth_arguments)
    val _ =
      assert "different-depth alias fixture changed its argument types"
        (binder_types (fastype_of different_depth_lhs) =
          [\<^typ>\<open>parser_nested_different_depth_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "different-depth alias fixture retained schematic variables"
        (null (Term.add_vars different_depth []))
    val _ =
      assert "different-depth alias fixture retained local free binders"
        (null (Term.add_frees different_depth []))
    val _ =
      assert "different-depth alias fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          different_depth > 0)
    val _ =
      assert "different-depth alias fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_different_depth_both_scrutinee\<close>
          different_depth_instantiated = 1)
    val _ =
      assert
        ("different-depth alias fixture lost its outer structural clauses: " ^
          string_of_int
            (length (outer_case_clauses different_depth)))
        (not (null (outer_case_clauses different_depth)))
    val _ =
      assert
        "reversed different-depth alias fixture changed its definition head"
        (null different_depth_reversed_arguments)
    val _ =
      assert
        "reversed different-depth alias fixture changed its argument types"
        (binder_types (fastype_of different_depth_reversed_lhs) =
          [\<^typ>\<open>parser_nested_different_depth_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert
        "reversed different-depth alias fixture retained schematic variables"
        (null (Term.add_vars different_depth_reversed []))
    val _ =
      assert
        "reversed different-depth alias fixture retained local free binders"
        (null (Term.add_frees different_depth_reversed []))
    val _ =
      assert
        "reversed different-depth alias fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          different_depth_reversed > 0)
    val _ =
      assert
        "reversed different-depth alias fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_different_depth_both_scrutinee\<close>
          different_depth_reversed_instantiated = 1)
    val _ =
      assert
        ("reversed different-depth alias fixture lost its outer structural clauses: " ^
          string_of_int
            (length
              (outer_case_clauses different_depth_reversed)))
        (not (null
          (outer_case_clauses different_depth_reversed)))
    val _ =
      assert "exhaustive outer-shape fixture changed its definition head"
        (null exhaustive_arguments)
    val _ =
      assert "exhaustive outer-shape fixture changed its argument type"
        (binder_types (fastype_of exhaustive_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "exhaustive outer-shape fixture retained schematic variables"
        (null (Term.add_vars exhaustive []))
    val _ =
      assert "exhaustive outer-shape fixture retained local free binders"
        (null (Term.add_frees exhaustive []))
    val _ =
      assert "exhaustive outer-shape fixture duplicated its scrutinee"
        (count_constant \<^const_name>\<open>bind\<close>
          exhaustive = 1)
    val _ =
      assert
        ("exhaustive outer-shape fixture changed its structural clause expansion: " ^
          string_of_int (length (outer_case_clauses exhaustive)))
        (length (outer_case_clauses exhaustive) = 9)
    val _ =
      assert "guarded exhaustive outer-shape fixture changed its definition head"
        (null exhaustive_guarded_arguments)
    val _ =
      assert "guarded exhaustive outer-shape fixture changed its argument types"
        (binder_types (fastype_of exhaustive_guarded_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>
             (nat, bool, unit, unit, unit, unit) expression
           \<close>])
    val _ =
      assert "guarded exhaustive outer-shape fixture retained schematic variables"
        (null (Term.add_vars exhaustive_guarded []))
    val _ =
      assert "guarded exhaustive outer-shape fixture retained local free binders"
        (null (Term.add_frees exhaustive_guarded []))
    val _ =
      assert "guarded exhaustive outer-shape fixture duplicated its scrutinee"
        (count_constant \<^const_name>\<open>bind\<close>
          exhaustive_guarded = 1)
    val _ =
      assert
        ("guarded exhaustive outer-shape fixture changed its structural clause expansion: " ^
          string_of_int (length
            (outer_case_clauses exhaustive_guarded)))
        (length (outer_case_clauses exhaustive_guarded) = 9)
    val [primary_name, secondary_name, tertiary_name] =
      status_constructor_names
    val ordered_structural_rows =
      [[], [primary_name], [secondary_name], [tertiary_name]]
    val ordered_or_structural_rows =
      [[], [tertiary_name], []]
    val overlapping_tuple_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [], [secondary_name], []]
    val overlapping_or_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [secondary_name],
       [secondary_name, secondary_name], [secondary_name],
       [tertiary_name], [tertiary_name, secondary_name],
       [tertiary_name]]
    val exhaustive_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [], [secondary_name], []]
    val _ =
      assert "separate same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered = 1)
    val _ =
      assert "separate same-outer alternatives retained equality guards"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered = 0)
    val _ =
      assert "separate same-outer structural clause order changed"
        (structural_status_rows ordered =
          ordered_structural_rows)
    val _ =
      assert "or-pattern same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered_or = 1)
    val _ =
      assert "or-pattern same-outer alternatives retained equality guards"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered_or = 0)
    val _ =
      assert "or-pattern structural clause order changed"
        (structural_status_rows ordered_or =
          ordered_or_structural_rows)
    val _ =
      assert "guarded same-shape arm duplicated the outer case"
        (count_constant result_case_name guarded_order = 1)
    val _ =
      assert "guarded same-shape arm duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_guarded_scrutinee\<close>
          guarded_order = 1)
    val _ =
      assert "guarded same-shape arm duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_guard_marker\<close>
          guarded_order = 1)
    val _ =
      assert "guarded same-shape arm retained a constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          guarded_order = 0)
    val _ =
      assert "guarded same-shape arm lost its nested constructor case"
        (count_constant inner_case_name guarded_order > 0)
    val _ =
      assert "global source-order fixture duplicated the outer case"
        (count_constant result_case_name global_source_order = 1)
    val _ =
      assert "global source-order fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_scrutinee\<close>
          global_source_order = 1)
    val _ =
      assert "global source-order fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          global_source_order = 0)
    val _ =
      assert "global source-order structural clauses changed order"
        (structural_status_rows global_source_order =
          ordered_structural_rows)
    val _ =
      assert "global source-order fixture changed guard evaluation count"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_source_order = 3)
    val _ =
      assert "global source-order Ok branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_ok_branch = 1)
    val _ =
      assert "global source-order Err branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_err_branch = 2)
    val _ =
      assert "overlapping tuple fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_overlap_scrutinee\<close>
          overlapping_tuple = 1)
    val _ =
      assert "overlapping tuple structural clauses changed order"
        (structural_status_rows overlapping_tuple =
          overlapping_tuple_structural_rows)
    val _ =
      assert "overlapping or-pattern structural clauses changed order"
        (structural_status_rows overlapping_or =
          overlapping_or_structural_rows)
    val _ =
      assert "exhaustive outer-shape structural clauses changed order"
        (structural_status_rows exhaustive =
          exhaustive_structural_rows)
    val _ =
      assert "guarded exhaustive structural clauses changed order"
        (structural_status_rows exhaustive_guarded =
          exhaustive_structural_rows)
    val _ =
      assert "exhaustive outer-shape fallback was removed from continuations"
        (Term.exists_subterm
          (fn term =>
            Term.aconv_untyped
              (term, \<^term>\<open>literal (3 :: nat)\<close>))
          exhaustive)
    val _ =
      assert "guarded exhaustive outer-shape fallback was removed from continuations"
        (Term.exists_subterm
          (fn term =>
            Term.aconv_untyped
              (term, \<^term>\<open>literal (3 :: nat)\<close>))
          exhaustive_guarded)
    val _ =
      assert "a later applicable source arm still terminates at undefined"
        (List.all
          (fn term =>
            count_constant \<^const_name>\<open>undefined\<close>
              term = 0)
          [nested, ordered, ordered_or, guarded_order,
           global_source_order, overlapping_tuple,
           overlapping_or, guarded_or,
           guarded_or_reversed, guarded_or_binder,
           differing_binding, alias_source_guard,
           exhaustive, exhaustive_guarded])
    val _ =
      assert "alias/wildcard fixture duplicated the outer case"
        (count_constant result_case_name alias_wildcard = 1)
    val _ =
      assert "alias/wildcard fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_wild_scrutinee\<close>
          alias_wildcard = 1)
    val _ =
      assert "alias/wildcard fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_wildcard = 0)
    val _ =
      assert "alias/wildcard fixture lost its matching alias arm"
        (count_constant \<^const_name>\<open>parser_nested_alias_tag\<close>
          alias_wildcard = 1)
    val _ =
      assert "alias/binder fixture duplicated the outer case"
        (count_constant result_case_name alias_binder = 1)
    val _ =
      assert "alias/binder fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_scrutinee\<close>
          alias_binder = 1)
    val _ =
      assert "alias/binder fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_binder = 0)
    val _ =
      assert "alias/binder fixture lost its matching alias arm"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_rewrite\<close>
          alias_binder = 1)

    val nested_payload = rhs_of "parser_nested_registered_payload"
    val SOME (native_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserNativePayload\<close>,
         fastype_of \<^term>\<open>ParserNativePayload\<close>)
    val native_case_name = constant_name native_case
    val native_payload_name =
      dest_Const_name \<^term>\<open>ParserNativePayload\<close>
    val nested_payload_clauses =
      outer_case_clauses nested_payload
    val option_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt
          (fst (dest_Type \<^typ>\<open>parser_native_case option\<close>)) of
         SOME {casex, ...} => constant_name casex
       | NONE =>
           error "constructor matching audit: missing option case sugar")
    val _ =
      assert "argument-bearing registered constructor did not remain directly structural"
        (length nested_payload_clauses = 3 andalso
         List.exists
           (fn (pattern, _) =>
             count_constant native_payload_name pattern = 1)
           nested_payload_clauses)
    val _ =
      assert "argument-bearing nested constructor lost recursive case lowering"
        (count_constant native_case_name nested_payload > 0)
    val _ =
      assert "argument-bearing nested constructor was normalized as equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nested_payload = 0)

    val mixed = rhs_of "parser_nested_registered_mixed"
    val _ =
      assert "mixed nested alternatives lost the outer option case"
        (count_constant option_case_name mixed > 0)
    val _ =
      assert "mixed nested alternatives lost the native payload case"
        (count_constant native_case_name mixed > 0)
    val _ =
      assert "mixed nested alternatives retained constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> mixed = 0)
    val _ =
      assert "mixed nested alternatives duplicated their scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_mixed_scrutinee\<close>
          mixed = 1)
    val _ =
      assert "mixed nested alternatives retained schematic variables"
        (null (Term.add_vars mixed []))
    val _ =
      assert "mixed nested alternatives retained local free binders"
        (null (Term.add_frees mixed []))
    val native_empty_name =
      dest_Const_name \<^term>\<open>ParserNativeEmpty\<close>
    val native_other_name =
      dest_Const_name \<^term>\<open>ParserNativeOther\<close>
    val _ =
      assert "mixed nested structural constructor order changed"
        (structural_constructor_rows
          [native_empty_name, native_payload_name, native_other_name]
          mixed =
         [[], [native_empty_name], [native_payload_name],
          [native_other_name]])

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
        \<^term>\<open>Parser_Constructor_Ambiguity_Left_Fixtures.Shared\<close>
    val right_name =
      dest_Const_name
        \<^term>\<open>Parser_Constructor_Ambiguity_Right_Fixtures.Shared\<close>
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


declare [[urust_conformance = false]]

section\<open> Frontend-shape structural audit \<close>

text\<open>
Guarded case compilation must reproduce the existing frontend's expanded term directly. In
particular, the scrutinee is evaluated once, source handlers are duplicated across expanded
or-alternatives exactly as in the frontend, and a false source guard enters the next source arm rather
than retrying a sibling alternative. No parser-private HOL constant may mediate that term shape.
\<close>

datatype cycle1_case =
    Cycle1_A | Cycle1_B

consts
  cycle1_scrutinee :: cycle1_case
  cycle1_guard_marker :: \<open>nat \<Rightarrow> bool\<close>
  cycle1_first_body :: nat
  cycle1_next_body :: nat
  cycle1_last_body :: nat
  cycle1_while_body_marker :: unit

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 pattern audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_constant base_name term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if Long_Name.base_name name = base_name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun conditional_branches term =
      let
        fun collect
            (Const (name, _) $ condition $ then_branch $ else_branch) branches =
              let
                val nested =
                  collect condition
                    (collect then_branch
                      (collect else_branch branches))
              in
                if name = \<^const_name>\<open>two_armed_conditional\<close>
                then (condition, then_branch, else_branch) :: nested
                else nested
              end
          | collect (left $ right) branches =
              collect left (collect right branches)
          | collect (Abs (_, _, body)) branches =
              collect body branches
          | collect _ branches = branches
      in collect term [] end

    val fallthrough =
      checked
        ("match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
         "Cycle1_A | Cycle1_B if " ^
         antiquotation "cycle1_guard_marker 99" ^ " \<Rightarrow> " ^
         antiquotation "cycle1_first_body" ^
         ", Cycle1_B \<Rightarrow> " ^ antiquotation "cycle1_next_body" ^
         ", _ \<Rightarrow> " ^ antiquotation "cycle1_last_body" ^ " }")
    val _ =
      audit_assert "the guarded match did not bind its scrutinee exactly once"
        (count_constant \<^const_name>\<open>cycle1_scrutinee\<close> fallthrough = 1)
    val _ =
      audit_assert "the guarded source body did not retain frontend expansion"
        (count_constant \<^const_name>\<open>cycle1_first_body\<close> fallthrough = 2)
    val _ =
      audit_assert "the term contains a parser-private administrative constant"
        (count_named_constant "urust_admin_let" fallthrough = 0)
    val guarded =
      filter
        (fn (_, then_branch, _) =>
          count_constant \<^const_name>\<open>cycle1_first_body\<close>
            then_branch > 0)
        (conditional_branches fallthrough)
    val _ =
      audit_assert "the direct term contains no source-guard false branch"
        (not (null guarded))
    val _ =
      List.app
        (fn (_, _, else_branch) =>
          (audit_assert
             "a false source guard retried a sibling or-alternative"
             (count_constant \<^const_name>\<open>cycle1_first_body\<close>
                else_branch = 0);
           audit_assert
             "a false source guard did not continue with the next source arm"
             (count_constant \<^const_name>\<open>cycle1_next_body\<close>
                else_branch > 0)))
        guarded
  in
    val _ = ()
  end
\<close>

section\<open> Conservative while-let coverage \<close>

text\<open>
C1-I6 removes the false continuation only for coverage proved by the resolved-pattern metadata.
The condition still sequences the source body with true, and the bounded loop body remains skip.
Partial patterns retain exactly one false fallback.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 while-let audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun loop_source pattern scrutinee =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
      pattern ^ " = " ^ scrutinee ^ " { let _ = " ^
      antiquotation "cycle1_while_body_marker" ^ "; () }"

    fun bounded_while_arguments term =
      let
        fun find
            (Const (name, _) $ fuel $ condition $ body) =
              if name = \<^const_name>\<open>bounded_while\<close>
              then SOME (fuel, condition, body)
              else
                get_first find [fuel, condition, body]
          | find (left $ right) =
              (case find left of
                 SOME result => SOME result
               | NONE => find right)
          | find (Abs (_, _, body)) = find body
          | find _ = NONE
      in
        (case find term of
           SOME result => result
         | NONE => error "Cycle 1 while-let audit: bounded_while was not generated")
      end

    fun is_skip term =
      (case Term.strip_comb term of
         (Const (literal_name, _), [Const (unit_name, _)]) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
             unit_name = \<^const_name>\<open>Product_Type.Unity\<close>
       | _ => false)

    fun check_exhaustive label source =
      let
        val term = checked source
        val (_, condition, body) = bounded_while_arguments term
      in
        audit_assert (label ^ " retained a false fallback")
          (count_constant \<^const_name>\<open>False\<close> term = 0);
        audit_assert (label ^ " moved the source body out of the condition")
          (count_constant
             \<^const_name>\<open>cycle1_while_body_marker\<close>
             condition > 0);
        audit_assert (label ^ " did not keep skip as the bounded loop body")
          (is_skip body)
      end

    val _ =
      check_exhaustive "TNil"
        (loop_source "TNil" "TNil")
    val _ =
      check_exhaustive "complete option family"
        (loop_source "Some(_) | None"
          (antiquotation "Some (1 :: nat)"))
    val _ =
      check_exhaustive "nested complete option family"
        (loop_source "Some(Some(_) | None) | None"
          (antiquotation "Some (None :: nat option)"))

    val partial =
      checked
        (loop_source "Some(_)"
          (antiquotation "None :: nat option"))
    val (_, partial_condition, partial_body) =
      bounded_while_arguments partial
    val _ =
      audit_assert "a partial while-let pattern lost its false fallback"
        (count_constant \<^const_name>\<open>False\<close> partial = 1)
    val _ =
      audit_assert "a partial while-let moved the source body out of the condition"
        (count_constant
           \<^const_name>\<open>cycle1_while_body_marker\<close>
           partial_condition > 0)
    val _ =
      audit_assert "a partial while-let did not keep skip as the bounded loop body"
        (is_skip partial_body)
  in
    val _ = writeln "Cycle 1 conservative while-let coverage audit passed"
  end
\<close>

section\<open> Conditional binding structure and markup \<close>

text\<open>
Certified-total conditional bindings use the same case shape as an explicit complete match and omit
the unreachable fallback only after lowering it. Partial patterns retain the frontend-shaped wildcard
case. These audits also pin mixed-chain pruning, the top-level tuple exception, conservative coverage,
scope, diagnostics, recovery, and editor markup.
\<close>

consts
  conditional_let_scrutinee_marker :: \<open>nat option\<close>
  conditional_let_success_marker :: nat
  conditional_let_fallback_marker :: nat
  conditional_chain_first_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_second_condition_marker :: bool
  conditional_chain_last_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_first_success_marker :: nat
  conditional_chain_second_success_marker :: nat
  conditional_chain_last_success_marker :: nat
  conditional_chain_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("conditional-binding regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "conditional-binding regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun path_named name path = render_path path = name
    fun expression_named name (UE_Path path) = path_named name path
      | expression_named _ _ = false
    fun call_named name (UE_Call (UC_Path path, _, _)) =
          path_named name path
      | call_named _ _ = false

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val if_text =
      "if let Some(value) = Some(1) { value } else { 0 }"
    val if_start =
      Position.make0 7 30 0 "" "" "conditional-binding-ast-audit"
    val if_stop =
      Position.symbol_explode if_text if_start
    val if_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          if_text if_start)
    val _ =
      (case if_ast of
         UE_IfLet
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (body, _),
            SOME (UE_Block (UE_Literal (LP_Integer ("0", _)), _)),
            position) =>
           (audit_assert "if-let path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "if-let span start moved"
              (Position.offset_of position =
                Position.offset_of if_start);
            audit_assert "if-let span end moved"
              (Position.end_offset_of position =
                Position.offset_of if_stop))
       | _ =>
           error "conditional-binding regression audit: if-let AST changed")

    val mixed_text =
      "if let Some(first) = Some(1) { first } else if false { 2 } " ^
      "else if let Some(last) = Some(3) { last } else { 4 }"
    val mixed_start =
      Position.make0 13 70 0 "" "" "conditional-chain-ast-audit"
    val mixed_stop =
      Position.symbol_explode mixed_text mixed_start
    val mixed_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          mixed_text mixed_start)
    val _ =
      (case mixed_ast of
         UE_IfLet
           (P_Constr (first_pattern_path, [P_Ident ("first", _)]),
            first_call,
            UE_Block (first_body, _),
            SOME
              (UE_If
                (UE_Literal (LP_Bool (false, _)),
                 UE_Block (UE_Literal (LP_Integer ("2", _)), _),
                 SOME
                   (UE_IfLet
                     (P_Constr (last_pattern_path, [P_Ident ("last", _)]),
                      last_call,
                      UE_Block (last_body, _),
                      SOME
                        (UE_Block
                          (UE_Literal (LP_Integer ("4", _)), _)),
                      nested_position)),
                 _)),
            position) =>
           (audit_assert "mixed-chain path structure changed"
              (path_named "Some" first_pattern_path andalso
               call_named "Some" first_call andalso
               expression_named "first" first_body andalso
               path_named "Some" last_pattern_path andalso
               call_named "Some" last_call andalso
               expression_named "last" last_body);
            audit_assert "mixed-chain span start moved"
              (Position.offset_of position =
                Position.offset_of mixed_start);
            audit_assert "mixed-chain span stopped before the final arm"
              (Position.end_offset_of position =
                Position.offset_of mixed_stop);
            audit_assert "nested if-let span stopped before its fallback"
              (Position.end_offset_of nested_position =
                Position.offset_of mixed_stop))
       | _ =>
           error
             "conditional-binding regression audit: mixed-chain AST changed")

    val let_text =
      "let Some(value) = Some(1) else { 0 }; value"
    val let_start =
      Position.make0 11 50 0 "" "" "conditional-binding-ast-audit"
    val let_stop =
      Position.symbol_explode let_text let_start
    val let_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          let_text let_start)
    val _ =
      (case let_ast of
         UE_LetElse
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (UE_Literal (LP_Integer ("0", _)), _),
            body,
            position) =>
           (audit_assert "let-else path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "let-else span start moved"
              (Position.offset_of position =
                Position.offset_of let_start);
            audit_assert "let-else span end moved"
              (Position.end_offset_of position =
                Position.offset_of let_stop))
       | _ =>
           error "conditional-binding regression audit: let-else AST changed")

    val mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val nested_mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else { if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> } } }")
    val _ =
      audit_assert "mixed chain lost right-associated branch order"
        (Term.aconv (mixed_chain, nested_mixed_chain))
    val _ =
      List.app
        (fn (name, label) =>
          audit_assert (label ^ " was not lowered exactly once")
            (count_constant name mixed_chain = 1))
        [(\<^const_name>\<open>conditional_chain_first_scrutinee_marker\<close>,
          "first mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          "mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          "last mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_first_success_marker\<close>,
          "first mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          "mixed-chain ordinary success branch"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          "last mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          "mixed-chain final fallback")]

    val total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let _ = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val explicit_total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { match_case " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> } }")
    val _ =
      audit_assert "a total mixed-chain arm retained its unreachable remainder"
        (Term.aconv (total_mixed_chain, explicit_total_mixed_chain))
    val _ =
      List.app
        (fn (name, expected, label) =>
          audit_assert (label ^ " has the wrong occurrence count")
            (count_constant name total_mixed_chain = expected))
        [(\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          1, "total mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          1, "total mixed-chain ordinary success"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          1, "total mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          1, "total mixed-chain success"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          0, "total mixed-chain unreachable fallback")]

    val two_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "two-armed if-let stopped using the explicit case shape"
        (Term.aconv (two_armed, explicit_two_armed))
    val _ =
      audit_assert "if-let lowered its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
          two_armed = 1)
    val _ =
      audit_assert "if-let lost success/fallback ordering"
        (count_constant
          \<^const_name>\<open>conditional_let_success_marker\<close>
          two_armed = 1 andalso
         count_constant
          \<^const_name>\<open>conditional_let_fallback_marker\<close>
          two_armed = 1)

    val total_two_armed =
      checked
        ("if let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_total_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total if-let did not match a complete case without fallback"
        (Term.aconv (total_two_armed, explicit_total_two_armed))
    val _ =
      audit_assert "total if-let changed scrutinee/success multiplicity"
        (count_constant
           \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
           total_two_armed = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           total_two_armed = 1)
    val _ =
      audit_assert "total if-let retained its unreachable fallback"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_two_armed = 0)

    val one_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }")
    val explicit_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }, _ \<Rightarrow> () }")
    val _ =
      audit_assert "one-armed if-let lost its skip fallback"
        (Term.aconv (one_armed, explicit_one_armed))
    val _ =
      audit_assert "partial one-armed if-let lost its synthetic skip"
        (count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           one_armed = 2)

    val total_one_armed =
      checked
        ("if let value = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "value; \<llangle>conditional_let_success_marker\<rrangle> }")
    val explicit_total_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "value \<Rightarrow> { let _ = value; " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } }")
    val _ =
      audit_assert "total one-armed if-let retained synthetic skip"
        (Term.aconv (total_one_armed, explicit_total_one_armed) andalso
         count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           total_one_armed = 0)

    val let_else =
      checked
        ("let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>")
    val explicit_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "let-else stopped placing its continuation in the success arm"
        (Term.aconv (let_else, explicit_let_else))

    val total_let_else =
      checked
        ("let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>conditional_let_success_marker\<rrangle>")
    val explicit_total_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total let-else retained its unreachable fallback"
        (Term.aconv (total_let_else, explicit_total_let_else) andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_let_else = 0)

    val tuple_if =
      checked
        ("if let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { " ^
         "\<llangle>left + right\<rrangle> } else { missing_tuple_audit }")
    val tuple_bind =
      checked
        ("let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); " ^
         "\<llangle>left + right\<rrangle>")
    val _ =
      audit_assert "top-level tuple stopped using the frontend's direct binding"
        (Term.aconv (tuple_if, tuple_bind))

    fun conditional_source pattern scrutinee =
      "if let " ^ pattern ^ " = " ^ scrutinee ^ " { " ^
      "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
      "\<llangle>conditional_let_fallback_marker\<rrangle> }"

    fun explicit_case_source pattern scrutinee fallback =
      "match_case " ^ scrutinee ^ " { " ^ pattern ^ " \<Rightarrow> " ^
      "\<llangle>conditional_let_success_marker\<rrangle>" ^
      (if fallback
       then ", _ \<Rightarrow> \<llangle>conditional_let_fallback_marker\<rrangle>"
       else "") ^ " }"

    fun check_total label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee false)
      in
        audit_assert (label ^ " did not use the complete case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " retained a fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual = 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_total label pattern scrutinee)
        [("wildcard totality", "_", "\<llangle>1 :: nat\<rrangle>"),
         ("identifier totality", "value", "\<llangle>1 :: nat\<rrangle>"),
         ("group totality", "(value)", "\<llangle>1 :: nat\<rrangle>"),
         ("alias totality", "whole @ _", "\<llangle>1 :: nat\<rrangle>"),
         ("grouped recursive tuple totality",
          "((left, (middle, right)))",
          "(\<llangle>1 :: nat\<rrangle>, " ^
            "(\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>))"),
         ("sole-constructor totality", "TNil", "TNil"),
         ("complete option totality", "Some(_) | None",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("nested complete option totality",
          "Some(Some(_) | None) | None",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("wildcard-alternative totality", "Some(_) | _",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("borrow-wrapper totality", "&_", "\<llangle>1 :: nat\<rrangle>")]

    fun check_partial label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee true)
      in
        audit_assert (label ^ " lost the explicit wildcard-case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " incorrectly discarded its fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual > 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_partial label pattern scrutinee)
        [("Some-only option coverage", "Some(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("None-only option coverage", "None",
          "\<llangle>None :: nat option\<rrangle>"),
         ("incomplete multi-constructor family",
          "ConditionalLetA(_) | ConditionalLetB(_)",
          "\<llangle>ConditionalLetA 1\<rrangle>"),
         ("internally complete but externally partial family",
          "Some(Some(_) | None)",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("literal pattern", "true", "\<llangle>True\<rrangle>"),
         ("value pattern", "\<llangle>1 :: nat\<rrangle>",
          "\<llangle>1 :: nat\<rrangle>"),
         ("range pattern", "1..=3", "\<llangle>2 :: nat\<rrangle>"),
         ("slice pattern", "[_, ..]", "\<llangle>[1 :: nat, 2]\<rrangle>"),
         ("struct pattern",
          "AdvStruct { adv_left: _, adv_right: _ }",
          "\<llangle>AdvStruct 1 2\<rrangle>"),
         ("nonconstructor path pattern", "Color::Red", "Color::Red"),
         ("constructor with a partial argument", "Some(true)",
          "\<llangle>Some True\<rrangle>"),
         ("or-pattern from different constructor families",
          "Some(_) | ConditionalLetA(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>")]

    val callback_ast =
      parse_text
        ("if let _ = callback_scrutinee { callback_success } " ^
         "else { callback_fallback }")
    val callback_count = Unsynchronized.ref 0
    fun callback_lower _ _ =
      let
        val index = !callback_count + 1
        val _ = callback_count := index
      in
        (case index of
           1 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_scrutinee_marker\<close>
         | 2 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_success_marker\<close>
         | 3 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_fallback_marker\<close>
         | _ =>
             error
               "conditional-binding regression audit: lowering callback called too often")
      end
    val callback_term =
      (case callback_ast of
         UE_IfLet (pattern, scrutinee, success, fallback, position) =>
           URust_Matching.lower_if_let callback_lower ctxt
             URust_Resolution.empty_environment
             (pattern, scrutinee, success, fallback, position)
       | _ =>
           error
             "conditional-binding regression audit: callback fixture AST changed")
    val _ =
      audit_assert "discarded total fallback was not lowered exactly once"
        (!callback_count = 3)
    val _ =
      audit_assert "discarded callback fallback leaked into the final term"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           callback_term = 0)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("conditional-binding regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun expect_positioned_rejection label text start expected needle =
      let
        val (_, position) = token_position text start needle 0
        val expected_here =
          XML.content_of (YXML.parse_body (Position.here position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("conditional-binding regression audit: " ^ label ^
                " unexpectedly elaborated")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " changed its diagnostic")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " moved its diagnostic")
                   (String.isSubstring expected_here message)
               end)
      end

    val bad_total_text =
      "if let _ = \<llangle>1 :: nat\<rrangle> { 1 } else { " ^
      "unknown_total_fallback!() }"
    val bad_total_start =
      Position.make0 19 120 900 "" ""
        "conditional-total-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "total fallback"
        bad_total_text bad_total_start
        "unknown macro \"unknown_total_fallback!\""
        "unknown_total_fallback"

    val bad_partial_text =
      "if let Some(_) = \<llangle>Some (1 :: nat)\<rrangle> { 1 } else { " ^
      "unknown_partial_fallback!() }"
    val bad_partial_start =
      Position.make0 23 160 1200 "" ""
        "conditional-partial-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "partial fallback"
        bad_partial_text bad_partial_start
        "unknown macro \"unknown_partial_fallback!\""
        "unknown_partial_fallback"

    val recovered_total =
      checked
        ("if let _ = \<llangle>1 :: nat\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "failed total fallback leaked state into the next command"
        (count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           recovered_total = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           recovered_total = 0)

    val total_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let _ = \<llangle>2 :: nat\<rrangle> { 3 } else { outer }"
    val total_markup_start =
      Position.make0 29 200 1600 "" ""
        "conditional-total-fallback-markup-audit"
    val partial_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let Some(_) = \<llangle>Some (2 :: nat)\<rrangle> { 3 } " ^
      "else { outer }"
    val partial_markup_start =
      Position.make0 31 220 2000 "" ""
        "conditional-partial-fallback-markup-audit"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      text start))) ())
          ())
    val _ = capture_elaboration total_markup_text total_markup_start
    val _ = capture_elaboration partial_markup_text partial_markup_start
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    if_text if_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    mixed_text mixed_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    let_text let_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "conditional-binding regression audit: binder entity markup changed")
      end

    val (total_outer_offset, total_outer_definition) =
      token_position total_markup_text total_markup_start "outer" 0
    val (_, total_outer_fallback) =
      token_position total_markup_text total_markup_start "outer"
        (total_outer_offset + size "outer")
    val (partial_outer_offset, partial_outer_definition) =
      token_position partial_markup_text partial_markup_start "outer" 0
    val (_, partial_outer_fallback) =
      token_position partial_markup_text partial_markup_start "outer"
        (partial_outer_offset + size "outer")
    val _ =
      audit_assert "discarded total fallback lost outer-scope resolution markup"
        (has_markup Markup.boundN total_outer_fallback andalso
         entity_id Markup.defN total_outer_definition =
           entity_id Markup.refN total_outer_fallback)
    val _ =
      audit_assert "partial fallback outer-scope resolution markup changed"
        (has_markup Markup.boundN partial_outer_fallback andalso
         entity_id Markup.defN partial_outer_definition =
           entity_id Markup.refN partial_outer_fallback)

    val (_, if_keyword) = token_position if_text if_start "if" 0
    val (if_offset, if_let_keyword) =
      token_position if_text if_start "let" 0
    val (if_let_offset, if_equals) =
      token_position if_text if_start "=" (if_offset + 2)
    val (_, if_else_keyword) =
      token_position if_text if_start "else" (if_let_offset + 3)
    val (mixed_else_offset, mixed_else_keyword) =
      token_position mixed_text mixed_start "else" 0
    val (mixed_if_offset, mixed_if_keyword) =
      token_position mixed_text mixed_start "if" (mixed_else_offset + 4)
    val (mixed_second_else_offset, mixed_second_else_keyword) =
      token_position mixed_text mixed_start "else" (mixed_if_offset + 2)
    val (mixed_if_let_offset, mixed_if_let_keyword) =
      token_position mixed_text mixed_start "if"
        (mixed_second_else_offset + 4)
    val (_, mixed_let_keyword) =
      token_position mixed_text mixed_start "let" (mixed_if_let_offset + 2)
    val (_, let_semicolon) =
      token_position let_text let_start ";" 0
    val _ =
      audit_assert "if keyword markup changed"
        (has_markup Markup.keyword1N if_keyword)
    val _ =
      audit_assert "let keyword markup changed"
        (has_markup Markup.keyword1N if_let_keyword)
    val _ =
      audit_assert "equals delimiter markup changed"
        (has_markup Markup.delimiterN if_equals)
    val _ =
      audit_assert "else keyword markup changed"
        (has_markup Markup.keyword1N if_else_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup changed")
            (has_markup Markup.keyword1N position))
        [(mixed_else_keyword, "mixed-chain else"),
         (mixed_if_keyword, "mixed-chain ordinary if"),
         (mixed_second_else_keyword, "mixed-chain second else"),
         (mixed_if_let_keyword, "mixed-chain if-let if"),
         (mixed_let_keyword, "mixed-chain if-let let")]
    val _ =
      audit_assert "let-else semicolon delimiter markup changed"
        (has_markup Markup.delimiterN let_semicolon)
  in
    val _ = writeln "Conditional-binding structure and markup regressions passed"
  end
\<close>

section\<open> Positions and pattern grammar \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("parser regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "parser regression audit: empty parse")

    fun pattern_source pattern =
      "match_case \<llangle>undefined\<rrangle> { " ^ pattern ^
      " \<Rightarrow> \<llangle>undefined\<rrangle> }"

    fun parse_pattern pattern =
      (case parse (pattern_source pattern) of
         UE_Match (_, _, [UR_Arm (result, NONE, _)], _) => result
       | _ => error "parser regression audit: unexpected pattern AST")

    fun integer text (P_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun range kind lower upper
        (P_Range (actual_kind, actual_lower, actual_upper, _)) =
          actual_kind = kind andalso
          integer lower actual_lower andalso
          integer upper actual_upper
      | range _ _ _ _ = false

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("parser regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    val _ =
      audit_assert "exclusive range shape changed"
        (range RK_Exclusive "5" "7"
          (parse_pattern "5..7"))
    val _ =
      audit_assert "inclusive range shape changed"
        (range RK_Inclusive "5" "7"
          (parse_pattern "5..=7"))

    val borrow_text = pattern_source "& mut &value"
    val outer_borrow_offset = find_from borrow_text "&" 0
    val inner_borrow_offset = find_from borrow_text "&" (outer_borrow_offset + 1)
    val borrow_start = Position.make0 11 4 0 "" "" ""
    val outer_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, outer_borrow_offset))
        borrow_start
    val inner_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, inner_borrow_offset))
        borrow_start
    val _ =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source
            borrow_text borrow_start) of
         SOME
           (UE_Match
             (_, _,
              [UR_Arm
                (P_Borrow
                  (BM_Mut,
                   P_Borrow (BM_Imm, P_Ident ("value", _), inner_pos),
                   outer_pos),
                 NONE, _)],
              _)) =>
           (audit_assert "outer borrow-pattern mode or position changed"
              (Position.offset_of outer_pos =
                Position.offset_of outer_borrow_position);
            audit_assert "inner borrow-pattern mode or position changed"
              (Position.offset_of inner_pos =
                Position.offset_of inner_borrow_position))
       | _ =>
           error
             "parser regression audit: nested borrow-pattern AST changed")

    val _ =
      (case parse_pattern "whole @ 5..=7" of
         P_Alias ("whole", _, inner, _) =>
           audit_assert "alias did not bind the whole range"
             (range RK_Inclusive "5" "7" inner)
       | _ =>
           error "parser regression audit: range alias shape changed")

    val _ =
      (case parse_pattern "outer @ inner @ 5..7" of
         P_Alias ("outer", _,
           P_Alias ("inner", _, nested, _), _) =>
             audit_assert "nested aliases lost right associativity"
               (range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: nested alias shape changed")

    val _ =
      (case parse_pattern "whole @ Some(5..=7)" of
         P_Alias ("whole", _,
           P_Constr (path, [nested]), _) =>
             audit_assert "constructor alias lost its path or range argument"
               (render_path path = "Some" andalso
                range RK_Inclusive "5" "7" nested)
       | _ =>
           error
             "parser regression audit: constructor alias shape changed")

    val _ =
      (case parse_pattern "whole @ Head { field: 5..7 }" of
         P_Alias ("whole", _,
           P_Struct (path,
             [SF_Field ("field", _, nested)]), _) =>
             audit_assert "struct alias lost its path or range field"
               (render_path path = "Head" andalso
                range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: struct alias shape changed")

    val _ =
      (case parse_pattern "left @ 1..2 | right @ 3..=4" of
         P_Or
           ([P_Alias ("left", _, left, _),
             P_Alias ("right", _, right, _)], _) =>
             (audit_assert "exclusive range lost alias precedence"
                (range RK_Exclusive "1" "2" left);
              audit_assert "inclusive range lost alias precedence"
                (range RK_Inclusive "3" "4" right))
       | _ =>
           error
             "parser regression audit: alias/range/or precedence changed")

    val chained_text =
      pattern_source "1..2..3"
    val chained_start =
      Position.make0 7 1 0 "" "" ""

    val first_range =
      find_from chained_text ".." 0
    val second_range =
      find_from chained_text ".." (first_range + 2)
    val second_range_position =
      Position.symbol_explode
        (String.substring (chained_text, 0, second_range))
        chained_start
    val second_range_here =
      XML.content_of
        (YXML.parse_body
          (Position.here second_range_position))
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source
                chained_text chained_start)) () of
         Exn.Res _ =>
           error
             "parser regression audit: chained range unexpectedly elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message =
                 XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn))
             in
               audit_assert "chained range missed semantic validation"
                 (String.isSubstring
                   "range patterns are non-associative" message);
               audit_assert "chained range diagnostic moved"
                 (String.isSubstring second_range_here message)
             end)

    fun alternative_name index =
      "regression_alt_" ^ string_of_int index

    fun audit_alternatives count =
      let
        val alternatives =
          space_implode " | "
            (map alternative_name (0 upto (count - 1)))
      in
        (case parse_pattern alternatives of
           P_Or (patterns, _) =>
             (audit_assert
                ("large or-pattern was not flattened at " ^
                  string_of_int count)
                (length patterns = count);
              audit_assert
                ("large or-pattern source order changed at " ^
                  string_of_int count)
                (case (hd patterns, List.last patterns) of
                   (P_Ident (first, _), P_Ident (last, _)) =>
                     first = alternative_name 0 andalso
                     last = alternative_name (count - 1)
                 | _ => false))
         | _ =>
             error
               ("parser regression audit: large or-pattern AST changed at " ^
                 string_of_int count))
      end

    val _ = audit_alternatives 4096
    val _ = audit_alternatives 16384

    fun expect_positioned_rejection
        label text start expected expected_position =
      let
        val expected_here =
          XML.content_of
            (YXML.parse_body (Position.here expected_position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("parser regression audit: " ^ label ^
                 " unexpectedly parsed")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body
                       (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " diagnostic changed")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " position changed")
                   (String.isSubstring expected_here message)
               end)
      end

    val operator_text = "1 + 2 ++ 3"
    val operator_start =
      Position.make0 4 10 0 "" "" ""
    val second_operator =
      Position.symbol_explode
        (String.substring (operator_text, 0, 7))
        operator_start
    val _ =
      expect_positioned_rejection
        "malformed operator"
        operator_text operator_start
        "syntax error found at +"
        second_operator

    val eof_text = "{ ()"
    val eof_start =
      Position.make0 3 12 0 "" "" ""
    val eof_stop =
      Position.symbol_explode eof_text eof_start
    val _ =
      expect_positioned_rejection
        "malformed EOF"
        eof_text eof_start
        "syntax error found at end of input"
        eof_stop
  in
    val _ = writeln "Parser position and pattern grammar regressions passed"
  end
\<close>

section\<open> Concealed registered-constructor lookup boundary \<close>

experiment
begin

datatype concealed_constructor_audit =
    ConcealedRegistered
  | ConcealedUnregistered

micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedRegistered
  ("ConcealedAudit::Registered")
micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedUnregistered
  ("ConcealedAudit::Unregistered")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("concealed constructor lookup audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source source) of
         SOME expression => expression
       | NONE => error "concealed constructor lookup audit: empty parse")

    fun path_of source =
      (case parse source of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked source =
      checked_source (Parser_Lex_Util.text_source source)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("concealed constructor lookup audit: missing case metadata for " ^
                 quote type_name))
      end

    val theory = Proof_Context.theory_of ctxt
    val registered_name =
      \<^const_name>\<open>ConcealedRegistered\<close>
    val unregistered_name =
      \<^const_name>\<open>ConcealedUnregistered\<close>
    val concealed_case_name =
      case_constant_name \<^term>\<open>ConcealedRegistered\<close>
    val _ =
      audit_assert "fixture constructor unexpectedly entered Code.is_constr"
        (not (Code.is_constr theory registered_name) andalso
         not (Code.is_constr theory unregistered_name))

    val resolver =
      URust_Resolution.make_constructor_resolver ctxt Position.none
    val registered_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "ConcealedAudit::Registered"))
    val _ =
      (case URust_Resolution.classify_registered_literal ctxt resolver
          (path_of "ConcealedAudit::Registered") of
         URust_Resolution.Registered_Constructor_Literal => ()
       | _ =>
           error
             "concealed constructor lookup audit: registered concealed literal was not classified as a constructor")
    val _ =
      audit_assert "registered concealed identity was not recovered"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term registered_info,
           \<^term>\<open>ConcealedRegistered\<close>))
    val _ =
      audit_assert "registered concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedRegistered")))
    val _ =
      audit_assert "second concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedUnregistered")))

    val registered_match =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val _ =
      audit_assert "registered concealed match lost its authentic case combinator"
        (count_constant concealed_case_name registered_match = 1)
    val _ =
      audit_assert "registered concealed exhaustive match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          registered_match = 0)

    val unregistered_binder =
      checked
        ("match_case \<llangle>ConcealedUnregistered\<rrangle> { " ^
         "ConcealedUnregistered \<Rightarrow> 0 }")
    val _ =
      audit_assert "unregistered concealed basename stopped being a binder"
        (count_constant unregistered_name unregistered_binder = 1)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    val concealed_mixed_text =
      "match \<llangle>ConcealedRegistered\<rrangle> { " ^
      "0 \<Rightarrow> (), ConcealedAudit::Registered \<Rightarrow> () }"
    val concealed_mixed_start =
      Position.make0 64 900 0 "" ""
        "concealed-constructor-mixed-match-audit"
    val concealed_mixed_position =
      Position.range_position
        (concealed_mixed_start,
         Position.symbol_explode concealed_mixed_text concealed_mixed_start)
    val concealed_mixed_source =
      Parser_Lex_Util.positioned_content_source
        concealed_mixed_text concealed_mixed_start
    val concealed_mixed_expected =
      "urust_expr: mixed numeral and constructor patterns in bare `match`" ^
      Position.here concealed_mixed_position
    val concealed_mixed_range =
      (Value.print_int
        (the (Position.offset_of concealed_mixed_position)),
       Value.print_int
        (the (Position.end_offset_of concealed_mixed_position)))
    val concealed_mixed_body =
      (case Exn.result (fn () => checked_source concealed_mixed_source) () of
         Exn.Res term =>
           error
             ("concealed constructor lookup audit: mixed numeral match " ^
              "unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val actual = Runtime.exn_message exn
             in
               audit_assert
                 "concealed constructor mixed-match diagnostic changed"
                 (actual = concealed_mixed_expected);
               YXML.parse_body actual
             end)
    val _ =
      audit_assert
        "concealed constructor mixed-match range changed"
        (diagnostic_ranges concealed_mixed_body =
          [concealed_mixed_range])

    val recovered_switch =
      checked
        ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
         "_ \<Rightarrow> 2 }")
    val recovered_case =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val recovered_unit = checked "()"
    val _ =
      audit_assert "concealed rejection lost switch recovery"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          recovered_switch = 1)
    val _ =
      audit_assert "concealed rejection lost constructor recovery"
        (count_constant concealed_case_name recovered_case = 1)
    val _ =
      audit_assert "concealed rejection lost unit recovery"
        (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
          recovered_unit = 1)
  in
    val _ =
      writeln
        "Concealed registered identity, mixed-match rejection, recovery, and filtered unregistered lookup regressions passed"
  end
\<close>

end


section\<open> Registered constructor identity audit \<close>

consts
  registered_constructor_scrutinee :: registered_constructor_fixture
  registered_constructor_guard_marker :: bool
  registered_constructor_first_marker :: nat
  registered_constructor_second_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered constructor identity audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source source)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "empty parse")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "expected constant")

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex, ...} => constant_name casex
         | NONE =>
             error
               ("registered constructor identity audit: missing case metadata for " ^
                 quote type_name))
      end

    val nullary_name =
      constant_name \<^term>\<open>RegisteredNullary\<close>
    val unary_name =
      constant_name \<^term>\<open>RegisteredUnary\<close>
    val other_name =
      constant_name \<^term>\<open>RegisteredOther\<close>
    val registered_type_name =
      fst (dest_Type \<^typ>\<open>registered_constructor_fixture\<close>)
    val phantom_a_name =
      constant_name
        \<^term>\<open>RegisteredPhantomA :: nat registered_phantom\<close>
    val phantom_b_name =
      constant_name
        \<^term>\<open>RegisteredPhantomB :: nat registered_phantom\<close>
    val negative_nullary_name =
      constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_other_name =
      constant_name \<^term>\<open>NegativeRegisteredOther\<close>
    val negative_phantom_name =
      constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>
    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_phantom_case_name =
      case_constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>

    val exhaustive =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Nullary \<Rightarrow> \<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "Registered::Unary(value) \<Rightarrow> value, " ^
         "Registered::Other \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val partial =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) \<Rightarrow> value }")
    val guarded =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) if " ^
         "\<llangle>registered_constructor_guard_marker\<rrangle> \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val nonconstructor =
      checked
        ("match_case IntegrationAudit::Value { IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val applied_nonconstructor =
      checked
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         "NegativeRegistered::Applied \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val duplicate_constructor =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::Duplicate \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val duplicate_phantom =
      checked
        ("match_case " ^
         "\<llangle>NegativeRegisteredPhantom :: " ^
         "nat negative_registered_phantom\<rrangle> { " ^
         "NegativeRegistered::Phantom \<Rightarrow> 0 }")

    val _ =
      audit_assert "exhaustive match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          exhaustive = 1)
    val _ =
      audit_assert "partial match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          partial = 1)
    val _ =
      audit_assert "guarded match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          guarded = 1)
    val _ =
      audit_assert "exhaustive match lost its authentic case combinator"
        (count_constant registered_case_name exhaustive = 1)
    val _ =
      audit_assert "exhaustive constructor match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated conditional"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close> exhaustive = 0)
    val _ =
      audit_assert "partial constructor match lost its case combinator"
        (count_constant registered_case_name partial = 1)
    val _ =
      audit_assert "partial constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> partial = 0)
    val _ =
      audit_assert "partial constructor match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close> partial > 0)
    val _ =
      audit_assert "guard marker was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>registered_constructor_guard_marker\<close>
          guarded = 1)
    val _ =
      audit_assert "guarded constructor match lost its authentic case combinator"
        (count_constant registered_case_name guarded = 1)
    val _ =
      audit_assert "guarded constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> guarded = 0)
    val _ =
      audit_assert "guarded match with wildcard fallback retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> guarded = 0)
    val _ =
      audit_assert "guarded false fall-through lost the next source arm"
        (count_constant
          \<^const_name>\<open>registered_constructor_second_marker\<close>
          guarded > 0)
    val _ =
      audit_assert "registered nonconstructor value-key count changed"
        (count_constant \<^const_name>\<open>integration_registered_value_audit\<close>
          nonconstructor = 2)
    val _ =
      audit_assert "registered nonconstructor lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nonconstructor > 0)
    val _ =
      audit_assert "registered nonconstructor lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          nonconstructor > 0)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("registered nonconstructor acquired constructor classification " ^
              quote name)
            (count_constant name nonconstructor = 0))
        [nullary_name, unary_name, other_name]
    val _ =
      audit_assert "constructor-headed registered application lost its two values"
        (count_constant
          \<^const_name>\<open>NegativeRegisteredUnary\<close>
          applied_nonconstructor = 2)
    val _ =
      audit_assert "constructor-headed registered application lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "constructor-headed registered application lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "duplicate same-constructor registrations became ambiguous"
        (count_constant negative_case_name duplicate_constructor = 1)
    val _ =
      audit_assert "phantom type-instantiated registrations became ambiguous"
        (count_constant negative_phantom_case_name duplicate_phantom = 1)

    fun path_of source =
      (case parse (Parser_Lex_Util.text_source source) of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    val resolver =
      URust_Resolution.make_constructor_resolver
        ctxt Position.none
    val unary_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "Registered::Unary"))
    val phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "RegisteredPhantom::A"))
    val duplicate_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Duplicate"))
    val duplicate_phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Phantom"))
    val _ =
      audit_assert "registered nonconstructor became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "IntegrationAudit::Value")))
    val _ =
      audit_assert "constructor-equal definition became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Value")))
    val _ =
      audit_assert "constructor-headed application became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Applied")))
    val _ =
      audit_assert "registered unary did not return catalogue identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term unary_info,
           \<^term>\<open>RegisteredUnary\<close>))
    val _ =
      (case URust_Resolution.constructor_family unary_info of
         SOME (_, members) =>
           audit_assert "registered constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [nullary_name, unary_name, other_name])
       | NONE => error "registered constructor lost family metadata")
    val _ =
      audit_assert "polymorphic phantom registration lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term phantom_info,
           \<^term>\<open>RegisteredPhantomA :: bool registered_phantom\<close>))
    val _ =
      (case URust_Resolution.constructor_family phantom_info of
         SOME (_, members) =>
           audit_assert "phantom constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [phantom_a_name, phantom_b_name])
       | NONE => error "phantom constructor lost family metadata")
    val _ =
      audit_assert "duplicate identical registrations lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_info,
           \<^term>\<open>NegativeRegisteredNullary\<close>))
    val _ =
      audit_assert "phantom registrations did not deduplicate by untyped identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_phantom_info,
           \<^term>\<open>
             NegativeRegisteredPhantom ::
               bool negative_registered_phantom
           \<close>))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val markup_text =
      "match_case \<llangle>RegisteredUnary 1\<rrangle> { " ^
      "Registered::Unary(value) \<Rightarrow> (), _ \<Rightarrow> () }"
    val markup_start =
      Position.make0 29 700 0 "" ""
        "registered-constructor-markup-audit"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
    val (path_raw, expected_path) =
      token_position markup_text markup_start
        "Registered::Unary" 0
    val (_, expected_qualifier) =
      token_position markup_text markup_start
        "Registered" path_raw
    val (_, expected_terminal) =
      token_position markup_text markup_start
        "Unary" (path_raw + size "Registered::")
    val pattern_path =
      (case parse markup_source of
         UE_Match
           (_, _, UR_Arm (P_Constr (path, [_]), NONE, _) :: _, _) =>
           path
       | _ => error "registered constructor pattern AST changed")
    val (_, terminal_position) =
      segment_identifier (final_segment pattern_path)
    val _ =
      audit_assert "registered constructor path span changed"
        (same_range (path_position pattern_path) expected_path)
    val _ =
      audit_assert "registered constructor terminal range changed"
        (same_range terminal_position expected_terminal)

    val captured_reports =
      Synchronized.var "registered_constructor_reports"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
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

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body
          (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun count_markup markup_name position =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)
    fun count_entity kind identity position =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val _ =
      audit_assert "constructor qualifier retained free markup"
        (count_markup Markup.freeN expected_qualifier = 0)
    val _ =
      audit_assert "constructor qualifier datatype entity duplicated or disappeared"
        (count_entity Markup.type_nameN registered_type_name
          expected_qualifier = 1)
    val _ =
      audit_assert "constructor qualifier keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_qualifier = 1)
    val _ =
      audit_assert "constructor qualifier retained obsolete tconst styling"
        (count_markup Markup.tconstN expected_qualifier = 0)
    val _ =
      audit_assert "constructor terminal constant entity duplicated or disappeared"
        (count_entity Markup.constantN unary_name expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal was reported as a free binder"
        (count_markup Markup.freeN expected_terminal = 0)
    val _ =
      audit_assert "constructor terminal notation entity duplicated or disappeared"
        (count_entity Micro_Rust_Names.notationN
          "Registered::Unary" expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal = 1)

    fun recovery_checks () =
      let
        val constructor_recovery =
          checked
            ("match_case \<llangle>NegativeRegisteredUnary 3\<rrangle> { " ^
             "NegativeRegistered::Nullary \<Rightarrow> 0, " ^
             "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
             "NegativeRegistered::Other \<Rightarrow> 1 }")
        val nonconstructor_recovery =
          checked
            ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
             "NegativeRegistered::Value \<Rightarrow> " ^
             "NegativeRegisteredNullary, " ^
             "_ \<Rightarrow> NegativeRegisteredOther }")
      in
        audit_assert "constructor recovery lost authentic identity"
          (count_constant
            \<^const_name>\<open>NegativeRegisteredUnary\<close>
            constructor_recovery > 0);
        audit_assert "nonconstructor recovery lost equality lowering"
          (count_constant \<^const_name>\<open>urust_eq\<close>
            nonconstructor_recovery > 0)
      end

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun expect_exact_rejection serial label text path terminal expected =
      let
        val start =
          Position.make0 (40 + serial) (900 + serial * 200) 0 "" ""
            ("registered-constructor-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (path_raw, _) =
          token_position text start path 0
        val terminal_raw =
          path_raw + size path - size terminal
        val (_, expected_position) =
          token_position text start terminal terminal_raw
        val qualifier_length = find_from path "::" 0
        val qualifier =
          String.substring (path, 0, qualifier_length)
        val (_, expected_qualifier_position) =
          token_position text start qualifier path_raw
        val expected_message =
          expected ^ Position.here expected_position
        val expected_range =
          (Value.print_int (the (Position.offset_of expected_position)),
           Value.print_int (the (Position.end_offset_of expected_position)))
        val captured =
          Synchronized.var
            ("registered_constructor_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Exn.result
                  (fn () =>
                    Parser_Test_Elaboration.expression ctxt source) ())
              ())
        val body =
          (case result of
             Exn.Res term =>
               error
                 ("registered constructor identity audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val rejection_markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ =
          audit_assert (label ^ " emitted premature qualifier free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier keyword3 markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.keyword3N andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier type entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.type_nameN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier notation entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier typing markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.typingN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal keyword3 markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.keyword3N andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal notation entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal constant entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.constantN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ = recovery_checks ()
      in () end

    val unary_path = "NegativeRegistered::Unary"
    val value_path = "NegativeRegistered::Value"
    val ambiguous_path = "NegativeRegistered::Ambiguous"
    val applied_path = "NegativeRegistered::Applied"
    val _ =
      expect_exact_rejection 0 "zero-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote "Unary" ^
         " expects 1 pattern argument(s), but got 0")
    val _ =
      expect_exact_rejection 1 "excess-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ "(left, right) \<Rightarrow> left, _ \<Rightarrow> 0 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote unary_path ^
         " expects 1 pattern argument(s), but got 2")
    val _ =
      expect_exact_rejection 2 "nonconstructor-application"
        ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
         value_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> " ^
         "NegativeRegisteredNullary }")
        value_path "Value"
        ("urust_expr: `" ^ value_path ^ "` is not a known constructor")
    val _ =
      expect_exact_rejection 3 "distinct-constructor-ambiguity"
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         ambiguous_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        ambiguous_path "Ambiguous"
        ("urust_expr: constructor pattern " ^ quote ambiguous_path ^
         " is ambiguous; candidates: " ^
         space_implode ", "
           (sort_strings [negative_nullary_name, negative_other_name]))
    val _ =
      expect_exact_rejection 4 "constructor-headed-application"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         applied_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> 0 }")
        applied_path "Applied"
        ("urust_expr: `" ^ applied_path ^ "` is not a known constructor")
  in
    val _ =
      writeln
        "Registered constructor identity, diagnostics, recovery, lowering, range, markup, and single-evaluation regressions passed"
  end
\<close>


section\<open> Contextual bare-match classification audit \<close>

consts
  mixed_match_scrutinee_marker :: nat
  mixed_match_first_body_marker :: nat
  mixed_match_second_body_marker :: nat
  mixed_match_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("contextual bare-match classification audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE =>
           error "contextual bare-match classification audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun path_of_source source =
      (case parse_source source of
         UE_Path path => path
       | _ => error "contextual bare-match classification audit: expected path")

    fun path_of text =
      path_of_source (Parser_Lex_Util.text_source text)

    fun class_matches expected actual =
      (case (expected, actual) of
         (URust_Resolution.Unregistered_Literal,
          URust_Resolution.Unregistered_Literal) => true
       | (URust_Resolution.Registered_Value_Literal,
          URust_Resolution.Registered_Value_Literal) => true
       | (URust_Resolution.Registered_Constructor_Literal,
          URust_Resolution.Registered_Constructor_Literal) => true
       | _ => false)

    fun class_name URust_Resolution.Unregistered_Literal = "unregistered"
      | class_name URust_Resolution.Registered_Value_Literal = "value"
      | class_name URust_Resolution.Registered_Constructor_Literal =
          "constructor"

    fun expect_class label expected path =
      let
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val actual =
          URust_Resolution.classify_registered_literal
            ctxt resolver path
      in
        if class_matches expected actual
        then ()
        else
          error
            ("contextual bare-match classification audit: " ^ label ^
              " classification changed from " ^ class_name expected ^
              " to " ^ class_name actual)
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun expect_report_free_class serial label expected text =
      let
        val start =
          Position.make0 (96 + serial) (33000 + serial * 500) 0 "" ""
            ("contextual-match-" ^ label ^ "-classification-audit")
        val path =
          path_of_source
            (Parser_Lex_Util.positioned_content_source text start)
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_classification_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val actual =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    URust_Resolution.classify_registered_literal
                      ctxt resolver path) ())
              ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val segment_positions =
          map (#2 o segment_identifier) (path_segments path)
        val reported_at_path =
          exists
            (fn (_, properties) =>
              exists (has_position properties) segment_positions)
            markup
      in
        audit_assert (label ^ " classification changed")
          (class_matches expected actual);
        audit_assert (label ^ " classification emitted path reports")
          (not reported_at_path)
      end

    val _ =
      expect_class "qualified registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "IntegrationAudit::Value")
    val _ =
      expect_class "single-segment registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "registered_seven")
    val _ =
      expect_report_free_class 0 "value-only exact key"
        URust_Resolution.Registered_Value_Literal
        "Color::Red"
    val _ =
      expect_class "registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "Registered::Nullary")
    val _ =
      expect_class "registered phantom constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "RegisteredPhantom::A")
    val _ =
      expect_class "duplicate registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "NegativeRegistered::Duplicate")
    val _ =
      expect_report_free_class 1 "merged constructor/value exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::ConstructorWins"
    val _ =
      expect_report_free_class 2 "two-constructor exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::Ambiguous"
    val _ =
      expect_class "constructor-equal definition"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Value")
    val _ =
      expect_class "constructor-headed application"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Applied")
    val _ =
      (case Exn.result
          (fn () =>
            let
              val path = path_of "Unregistered::Value"
              val resolver =
                URust_Resolution.make_constructor_resolver
                  ctxt (path_position path)
            in
              URust_Resolution.classify_registered_literal
                ctxt resolver path
            end) () of
         Exn.Res _ =>
           error
             "contextual bare-match classification audit: unregistered qualified path was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert
               "unregistered qualified path diagnostic changed"
               (String.isSubstring
                 "qualified path \"Unregistered::Value\" requires an exact micro_rust_notation (literal) declaration"
                 (Runtime.exn_message exn)))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val ast_text =
      "match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, 7 \<Rightarrow> 2, _ \<Rightarrow> 3 }"
    val ast_start =
      Position.make0 71 1700 0 "" ""
        "contextual-match-ast-audit"
    val ast_source =
      Parser_Lex_Util.positioned_content_source ast_text ast_start
    val ast_stop = Position.symbol_explode ast_text ast_start
    val expected_match =
      Position.range_position (ast_start, ast_stop)
    val (first_numeral_raw, expected_first_numeral) =
      token_position ast_text ast_start "0" (size "match 42 { ")
    val (_, expected_value_path) =
      token_position ast_text ast_start "IntegrationAudit::Value"
        (first_numeral_raw + 1)
    val (value_raw, expected_qualifier) =
      token_position ast_text ast_start "IntegrationAudit"
        (first_numeral_raw + 1)
    val (_, expected_terminal) =
      token_position ast_text ast_start "Value"
        (value_raw + size "IntegrationAudit::")
    val (_, expected_second_numeral) =
      token_position ast_text ast_start "7"
        (value_raw + size "IntegrationAudit::Value")
    val _ =
      (case parse_source ast_source of
         UE_Match
           (MF_Auto, _,
            [UR_Arm (P_Literal (LP_Integer (_, first_pos)), NONE, _),
             UR_Arm (P_Path path, NONE, _),
             UR_Arm (P_Literal (LP_Integer (_, second_pos)), NONE, _),
             UR_Arm (P_Wild _, NONE, _)],
            match_pos) =>
           let
             val (_, terminal_pos) =
               segment_identifier (final_segment path)
             val qualifier_pos =
               #2
                 (segment_identifier
                   (hd (path_segments path)))
           in
             audit_assert "contextual classification rewrote MF_Auto"
               true;
             audit_assert "bare match span changed"
               (same_range match_pos expected_match);
             audit_assert "first numeral range changed"
               (same_range first_pos expected_first_numeral);
             audit_assert "second numeral range changed"
               (same_range second_pos expected_second_numeral);
             audit_assert "registered path range changed"
               (same_range (path_position path) expected_value_path);
             audit_assert "registered qualifier range changed"
               (same_range qualifier_pos expected_qualifier);
             audit_assert "registered terminal range changed"
               (same_range terminal_pos expected_terminal)
           end
       | _ => error "contextual bare-match classification audit: AST changed")

    val identifier_text =
      "match 7 { 0 \<Rightarrow> 0, registered_seven \<Rightarrow> 1, _ \<Rightarrow> 2 }"
    val identifier_start =
      Position.make0 72 1900 0 "" ""
        "contextual-match-identifier-ast-audit"
    val (_, expected_identifier) =
      token_position identifier_text identifier_start
        "registered_seven" 0
    val _ =
      (case parse_source
          (Parser_Lex_Util.positioned_content_source
            identifier_text identifier_start) of
         UE_Match
           (_, _,
            [_,
             UR_Arm (P_Ident (_, identifier_pos), NONE, _),
             _],
            _) =>
           audit_assert "single-segment registered key range changed"
             (same_range identifier_pos expected_identifier)
       | _ =>
           error
             "contextual bare-match classification audit: identifier AST changed")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("contextual bare-match classification audit: missing case metadata for " ^
                 quote type_name))
      end

    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>

    val auto =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val explicit =
      checked
        ("match_switch \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "auto registered-value mixture differs from explicit switch"
        (Term.aconv (auto, explicit))
    val _ =
      audit_assert "auto registered-value mixture lost ncase_selector"
        (count_constant \<^const_name>\<open>ncase_selector\<close> auto = 1)
    val _ =
      audit_assert "auto registered-value mixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>mixed_match_scrutinee_marker\<close>
          auto = 1)
    val _ =
      audit_assert "registered backend was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>integration_registered_value_audit\<close>
          auto = 1)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch body marker was duplicated or dropped: " ^ name)
            (count_constant name auto = 1))
        [\<^const_name>\<open>mixed_match_first_body_marker\<close>,
         \<^const_name>\<open>mixed_match_second_body_marker\<close>,
         \<^const_name>\<open>mixed_match_fallback_marker\<close>]
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch lowering introduced " ^ quote name)
            (count_constant name auto = 0))
        [\<^const_name>\<open>case_guard\<close>,
         \<^const_name>\<open>urust_eq\<close>,
         \<^const_name>\<open>two_armed_conditional\<close>,
         \<^const_name>\<open>undefined\<close>,
         \<^const_name>\<open>RegisteredNullary\<close>]

    val switch_preferred =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "registered value without numeral selected switch"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          switch_preferred = 1)
    val _ =
      audit_assert "registered value without numeral retained case equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          switch_preferred = 0)
    val _ =
      audit_assert "registered value without numeral retained case conditional"
        (count_constant \<^const_name>\<open>two_armed_conditional\<close>
          switch_preferred = 0)

    val constructor_wins =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::ConstructorWins \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val _ =
      audit_assert "constructor/nonconstructor exact key did not select the constructor"
        (count_constant negative_case_name constructor_wins = 1)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_markup label source =
      let
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () => ignore (checked_source source)) ())
              ())
      in
        fold collect_markup
          (maps YXML.parse_body (Synchronized.value captured)) []
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val qualified_markup = capture_markup "qualified" ast_source
    val _ =
      audit_assert "first numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "first numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier retained free markup"
        (count_markup Markup.freeN expected_qualifier
          qualified_markup = 0)
    val _ =
      audit_assert "registered qualifier notation report duplicated"
        (count_entity Micro_Rust_Names.notationN
          "IntegrationAudit::Value"
          expected_qualifier qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier typing tooltip duplicated or disappeared"
        (count_markup Markup.typingN expected_qualifier
          qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier acquired terminal styling"
        (count_markup Markup.keyword3N expected_qualifier
          qualified_markup = 0)
    val _ =
      audit_assert "registered terminal notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "IntegrationAudit::Value"
          expected_terminal qualified_markup = 1)
    val _ =
      audit_assert "registered terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal
          qualified_markup = 1)
    val _ =
      audit_assert "registered terminal acquired typing markup"
        (count_markup Markup.typingN expected_terminal
          qualified_markup = 0)
    val _ =
      audit_assert "registered nonconstructor constant entity count changed"
        (count_entity Markup.constantN
          \<^const_name>\<open>integration_registered_value_audit\<close>
          expected_terminal qualified_markup = 1)

    val identifier_source =
      Parser_Lex_Util.positioned_content_source
        identifier_text identifier_start
    val identifier_markup =
      capture_markup "identifier" identifier_source
    val _ =
      audit_assert "single-segment notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "registered_seven"
          expected_identifier identifier_markup = 1)
    val _ =
      audit_assert "single-segment keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_identifier
          identifier_markup = 1)
    val _ =
      audit_assert "single-segment registration acquired typing markup"
        (count_markup Markup.typingN expected_identifier
          identifier_markup = 0)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun recovery_checks () =
      let
        val recovered_switch =
          checked
            ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
             "_ \<Rightarrow> 2 }")
        val recovered_case =
          checked
            ("match \<llangle>RegisteredNullary\<rrangle> { " ^
             "Registered::Nullary \<Rightarrow> 0, " ^
             "Registered::Unary(value) \<Rightarrow> value, " ^
             "Registered::Other \<Rightarrow> 1 }")
        val recovered_unit = checked "()"
      in
        audit_assert "registered-value switch recovery failed"
          (count_constant \<^const_name>\<open>ncase_selector\<close>
            recovered_switch = 1);
        audit_assert "registered-constructor case recovery failed"
          (count_constant registered_case_name recovered_case = 1);
        audit_assert "unit recovery failed"
          (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
            recovered_unit = 1)
      end

    fun expect_exact_rejection serial label text expected_position expected =
      let
        val start =
          Position.make0 (80 + serial) (2300 + serial * 300) 0 "" ""
            ("contextual-match-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val position = expected_position text start
        val expected_message = expected ^ Position.here position
        val expected_range =
          (Value.print_int (the (Position.offset_of position)),
           Value.print_int (the (Position.end_offset_of position)))
        val body =
          (case Exn.result (fn () => checked_source source) () of
             Exn.Res term =>
               error
                 ("contextual bare-match classification audit: " ^
                  label ^ " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ = recovery_checks ()
      in () end

    fun complete_range text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun token_range needle offset text start =
      #2 (token_position text start needle offset)

    val constructor_mixed_text =
      "match \<llangle>RegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), Registered::Nullary \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 0 "registered-constructor-mix"
        constructor_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val guarded_text =
      "match 42 { 0 if True \<Rightarrow> (), IntegrationAudit::Value \<Rightarrow> (), " ^
      "_ \<Rightarrow> () }"
    val guarded_numeral_offset =
      find_from guarded_text "0" (size "match 42 { ")
    val _ =
      expect_exact_rejection 1 "guard-forced-case"
        guarded_text (token_range "0" guarded_numeral_offset)
        "urust_expr: numeric patterns are not supported in case patterns"

    val switch_guard_text =
      "match_switch 42 { IntegrationAudit::Value if True \<Rightarrow> (), _ \<Rightarrow> () }"
    val switch_guard_offset =
      find_from switch_guard_text "if" 0
    val _ =
      expect_exact_rejection 2 "explicit-switch-guard"
        switch_guard_text (token_range "if" switch_guard_offset)
        "urust_expr: guards are not supported in explicit `match_switch`"

    val identifier_failure_text =
      "match 0 { 0 \<Rightarrow> (), unregistered_key \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 3 "unregistered-identifier"
        identifier_failure_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val constructor_wins_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::ConstructorWins \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 4 "constructor-wins-mix"
        constructor_wins_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val ambiguous_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::Ambiguous \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 5 "two-constructor-mix"
        ambiguous_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"
  in
    val _ =
      writeln
        "Contextual bare-match classification, lowering, range, markup, diagnostics, recovery, and single-evaluation regressions passed"
  end
\<close>


section\<open> Or-pattern binder-set validation \<close>

datatype binder_or_audit_fixture =
    BinderAuditA nat nat
  | BinderAuditB nat nat
  | BinderAuditC nat nat
  | BinderAuditSliceA \<open>nat list\<close>
  | BinderAuditSliceB \<open>nat list\<close>

text\<open>
The first alternative is the canonical binder signature. Every alternative is recursively checked
for duplicates before the name sets are compared; rejection precedes local allocation and guard/body
lowering. Successful alternatives share the first signature's entity identities even when source
order and structural positions differ.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("or-pattern binder audit: " ^ message)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("or-pattern binder audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun nth_raw text needle index =
      let
        fun seek 0 offset = find_from text needle offset
          | seek remaining offset =
              let val found = find_from text needle offset
              in seek (remaining - 1) (found + size needle) end
      in seek index 0 end

    fun token_position text start needle index =
      let
        val raw = nth_raw text needle index
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun position_range position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun same_ranges left right =
      length left = length right andalso
        List.all (fn range => member (op =) right range) left

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun markup_of reports =
      fold collect_markup (maps YXML.parse_body reports) []

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position markup =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    fun has_urust_entity position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            has_position properties position)
        markup

    fun entity_id property position markup =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               ("or-pattern binder audit: entity markup changed" ^
                 Position.here position))
      end

    fun has_entity_property property position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            is_some (Properties.get properties property) andalso
            has_position properties position)
        markup

    fun capture_expression text start =
      let
        val captured =
          Synchronized.var "or_pattern_binder_reports" ([]: string list)
        fun capture_reports chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture_reports
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        checked_source
                          (Parser_Lex_Util.positioned_content_source
                            text start)) ()) ())
              ())
      in (result, markup_of (Synchronized.value captured)) end

    val recovery_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | " ^
      "BinderAuditC(x, y) \<Rightarrow> x }"

    fun recover label =
      (ignore (checked recovery_text);
       ignore (checked "()");
       writeln ("or-pattern recovery passed after " ^ label))

    fun expect_rejection serial label text expected positions forbidden =
      let
        val start =
          Position.make0 (110 + serial) (7000 + serial * 400) 0 "" ""
            ("or-pattern-" ^ label ^ "-audit")
        val (result, markup) = capture_expression text start
        val actual =
          (case result of
             Exn.Res term =>
               error
                 ("or-pattern binder audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else Runtime.exn_message exn)
        val _ =
          audit_assert (label ^ " exact diagnostic changed")
            (actual = expected start)
        val actual_ranges = diagnostic_ranges (YXML.parse_body actual)
        val expected_ranges =
          map (position_range o (fn position => position start)) positions
        val _ =
          audit_assert (label ^ " diagnostic ranges changed")
            (same_ranges actual_ranges expected_ranges)
        val _ =
          List.app
            (fn unexpected =>
              audit_assert
                (label ^ " elaborated " ^ quote unexpected)
                (not (String.isSubstring unexpected actual)))
            forbidden
        val _ = recover label
      in (start, markup) end

    fun missing_message name primary secondary start =
      "urust_expr: or-pattern alternative is missing binder " ^ quote name ^
      Position.here (primary start) ^
      "\nThe first alternative binds it here" ^
      Position.here (secondary start)

    fun extra_message name primary start =
      "urust_expr: or-pattern alternative has extra binder " ^ quote name ^
      Position.here (primary start)

    fun duplicate_message name repeated original start =
      "urust_expr: duplicate pattern binder " ^ quote name ^
      Position.here (repeated start) ^
      "\nThe original binder is here" ^
      Position.here (original start)

    val missing_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x }"
    fun missing_bar start = token_position missing_text start "|" 0
    fun missing_first_x start = token_position missing_text start "x" 0
    fun missing_body_x start = token_position missing_text start "x" 1
    val (missing_start, missing_markup) =
      expect_rejection 0 "missing" missing_text
        (missing_message "x" missing_bar missing_first_x)
        [missing_bar, missing_first_x] []
    val _ =
      audit_assert "missing-binder bar lost operator markup"
        (has_markup Markup.operatorN
          (missing_bar missing_start) missing_markup)
    val _ =
      audit_assert "missing-binder bar lost typing markup"
        (has_markup Markup.typingN
          (missing_bar missing_start) missing_markup)
    val _ =
      List.app
        (fn position =>
          (audit_assert "rejected binder acquired bound markup"
             (not (has_markup Markup.boundN position missing_markup));
           audit_assert "rejected binder acquired an entity"
             (not (has_urust_entity position missing_markup))))
        [missing_first_x missing_start, missing_body_x missing_start]

    val extra_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { None | Some(x) \<Rightarrow> 0 }"
    fun extra_x start = token_position extra_text start "x" 0
    val (extra_start, extra_markup) =
      expect_rejection 1 "extra" extra_text
        (extra_message "x" extra_x) [extra_x] []
    val _ =
      audit_assert "extra rejected binder acquired bound markup"
        (not (has_markup Markup.boundN (extra_x extra_start) extra_markup))
    val _ =
      audit_assert "extra rejected binder acquired an entity"
        (not (has_urust_entity (extra_x extra_start) extra_markup))

    val deterministic_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(z, x) | BinderAuditB(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun deterministic_bar start =
      token_position deterministic_text start "|" 0
    fun deterministic_x start =
      token_position deterministic_text start "x" 0
    val _ =
      expect_rejection 2 "deterministic-missing" deterministic_text
        (missing_message "x" deterministic_bar deterministic_x)
        [deterministic_bar, deterministic_x] []

    val third_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(x, _) | " ^
      "BinderAuditC(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun third_first_bar start = token_position third_text start "|" 0
    fun third_first_x start = token_position third_text start "x" 0
    val _ =
      expect_rejection 3 "third-alternative" third_text
        (missing_message "x" third_first_bar third_first_x)
        [third_first_bar, third_first_x] []

    val nested_missing_text =
      "match_case \<llangle>Some (Ok (1 :: nat))\<rrangle> { " ^
      "Some(Ok(x) | Err(y)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_missing_bar start =
      token_position nested_missing_text start "|" 0
    fun nested_missing_x start =
      token_position nested_missing_text start "x" 0
    val _ =
      expect_rejection 4 "nested-missing-before-extra" nested_missing_text
        (missing_message "x" nested_missing_bar nested_missing_x)
        [nested_missing_bar, nested_missing_x] []

    val nested_extra_text =
      "match_case \<llangle>Some (Some (1 :: nat))\<rrangle> { " ^
      "Some(None | Some(x)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_extra_x start =
      token_position nested_extra_text start "x" 0
    val _ =
      expect_rejection 5 "nested-extra" nested_extra_text
        (extra_message "x" nested_extra_x) [nested_extra_x] []

    val guarded_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(x) | None if unknown_binder_guard!() \<Rightarrow> " ^
      "unknown_binder_body!(), _ \<Rightarrow> 0 }"
    fun guarded_bar start = token_position guarded_text start "|" 0
    fun guarded_x start = token_position guarded_text start "x" 0
    val _ =
      expect_rejection 6 "guarded" guarded_text
        (missing_message "x" guarded_bar guarded_x)
        [guarded_bar, guarded_x]
        ["unknown_binder_guard", "unknown_binder_body"]

    val slice_missing_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([x, ..]) | BinderAuditSliceB([]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_missing_bar start =
      token_position slice_missing_text start "|" 0
    fun slice_missing_x start =
      token_position slice_missing_text start "x" 0
    val _ =
      expect_rejection 7 "slice-missing" slice_missing_text
        (missing_message "x" slice_missing_bar slice_missing_x)
        [slice_missing_bar, slice_missing_x] []

    val slice_extra_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([]) | BinderAuditSliceB([.., x]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_extra_x start =
      token_position slice_extra_text start "x" 0
    val _ =
      expect_rejection 8 "slice-extra" slice_extra_text
        (extra_message "x" slice_extra_x) [slice_extra_x] []

    val duplicate_first_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, x) | BinderAuditB(y, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_first_original start =
      token_position duplicate_first_text start "x" 0
    fun duplicate_first_repeated start =
      token_position duplicate_first_text start "x" 1
    val _ =
      expect_rejection 9 "duplicate-first" duplicate_first_text
        (duplicate_message "x"
          duplicate_first_repeated duplicate_first_original)
        [duplicate_first_repeated, duplicate_first_original] []

    val duplicate_later_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(y, y) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_later_original start =
      token_position duplicate_later_text start "y" 0
    fun duplicate_later_repeated start =
      token_position duplicate_later_text start "y" 1
    val _ =
      expect_rejection 10 "duplicate-later" duplicate_later_text
        (duplicate_message "y"
          duplicate_later_repeated duplicate_later_original)
        [duplicate_later_repeated, duplicate_later_original] []

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "or-pattern binder audit: empty parse")

    fun callback_trace text =
      let
        val calls = Unsynchronized.ref ([]: string list)
        fun lower _ expression =
          let
            val label =
              (case expression of
                 UE_Path path => render_path path
               | _ => "<non-path>")
            val _ = calls := label :: !calls
          in Free ("_" ^ label, dummyT) end
        val result =
          (case parse text of
             UE_Match arguments =>
               Exn.result
                 (fn () =>
                   URust_Matching.lower_match lower ctxt
                     URust_Resolution.empty_environment arguments) ()
           | _ => error "or-pattern binder audit: callback fixture changed")
      in (result, rev (!calls)) end

    val invalid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, _) | BinderAuditB(_, _) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (invalid_callback_result, invalid_callback_calls) =
      callback_trace invalid_callback_text
    val _ =
      (case invalid_callback_result of
         Exn.Res _ =>
           error "or-pattern binder audit: invalid callback fixture elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "callback rejection changed"
               (String.isSubstring
                 "or-pattern alternative is missing binder \"x\""
                 (Runtime.exn_message exn)))
    val _ =
      audit_assert "rejected arm lowered its guard or body"
        (invalid_callback_calls = ["binder_or_scrutinee_probe"])

    val valid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (valid_callback_result, valid_callback_calls) =
      callback_trace valid_callback_text
    val _ =
      (case valid_callback_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      audit_assert "valid arm source expressions were not lowered once"
        (valid_callback_calls =
          ["binder_or_scrutinee_probe", "binder_or_guard_probe",
           "binder_or_body_probe", "binder_or_fallback_probe"])

    val valid_markup_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if x < y \<Rightarrow> x, _ \<Rightarrow> 0 }"
    val valid_markup_start =
      Position.make0 140 14000 0 "" "" "or-pattern-valid-markup-audit"
    val (valid_markup_result, valid_markup) =
      capture_expression valid_markup_text valid_markup_start
    val _ =
      (case valid_markup_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val x_positions =
      map (token_position valid_markup_text valid_markup_start "x")
        (0 upto 4)
    val y_positions =
      map (token_position valid_markup_text valid_markup_start "y")
        (0 upto 3)
    fun assert_shared name positions =
      let
        val definition = hd positions
        val references = tl positions
        val id = entity_id Markup.defN definition valid_markup
        val _ =
          audit_assert (name ^ " definition lost bound markup")
            (has_markup Markup.boundN definition valid_markup)
        val _ =
          List.app
            (fn position =>
              (audit_assert (name ^ " occurrence lost bound markup")
                 (has_markup Markup.boundN position valid_markup);
               audit_assert (name ^ " occurrence changed entity identity")
                 (entity_id Markup.refN position valid_markup = id)))
            references
        val _ =
          List.app
            (fn position =>
              audit_assert (name ^ " later alternative allocated a definition")
                (not
                  (has_entity_property Markup.defN
                    position valid_markup)))
            (tl positions)
      in () end
    val _ = assert_shared "x" x_positions
    val _ = assert_shared "y" y_positions

    val _ =
      ignore
        (checked
          ("match_case \<llangle>(Some (1 :: nat), " ^
           "(Some (2 :: nat), TNil))\<rrangle> { " ^
           "(Some(x), y) | (y, Some(x)) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
    val _ =
      ignore
        (checked
          ("match \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
           "BinderAuditSliceA([x, ..]) | " ^
           "BinderAuditSliceB([.., x]) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
  in
    val _ =
      writeln
        "Or-pattern binder diagnostics, ranges, precedence, markup, recovery, and shared-environment regressions passed"
  end
\<close>



end
