(* Readable pattern-matching examples: constructor metadata, structural matrices, slice
   patterns, frozen matcher expectations and name resolution. The ML audits are in
   Parser_Pattern_ML_Tests. *)

theory Parser_Pattern_Examples
  imports
    Parser_Syntax_Examples
    Shallow_Micro_Rust.Core_Expression_Lemmas
begin

chapter\<open> Pattern matching \<close>

section\<open>Native constructor metadata\<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

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

micro_rust_notation (literal)
  Parser_Test_Fixtures_Left.SharedWordState
  ("ParserWordAmbiguityLeft::Shared")

micro_rust_notation (literal)
  Parser_Test_Fixtures_Left.LeftWordState
  ("ParserWordAmbiguityLeft::LeftOnly")

micro_rust_notation (literal)
  Parser_Test_Fixtures_Right.SharedWordState
  ("ParserWordAmbiguityRight::Shared")

micro_rust_notation (literal)
  Parser_Test_Fixtures_Right.RightWordState
  ("ParserWordAmbiguityRight::RightOnly")

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

urust_expr  parser_word_family_unqualified ::
  \<open>
    parser_word_family \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      ParserWordFirst \<Rightarrow> 10,
      ParserWordSecond | ParserWordThird \<Rightarrow> 20
    }
  \<close>

urust_expr parser_word_ambiguity_left_qualified ::
  \<open>
    word_constructor_ambiguity_left \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      ParserWordAmbiguityLeft::Shared \<Rightarrow> 1,
      ParserWordAmbiguityLeft::LeftOnly \<Rightarrow> 2
    }
  \<close>

urust_expr parser_word_ambiguity_right_qualified ::
  \<open>
    word_constructor_ambiguity_right \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      ParserWordAmbiguityRight::Shared \<Rightarrow> 3,
      ParserWordAmbiguityRight::RightOnly \<Rightarrow> 4
    }
  \<close>

urust_expr parser_unknown_bare_identifier_binder ::
  \<open>
    nat \<Rightarrow>
      (unit, nat, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open>
    match_case scrutinee {
      parser_unknown_state \<Rightarrow> parser_unknown_state
    }
  \<close>

urust_expr parser_word_family_matches ::
  \<open>
    parser_word_family \<Rightarrow>
      (unit, bool, unit, unit, unit, unit) expression
  \<close>
  (scrutinee)
  \<open> matches!(scrutinee, ParserWordFamily::Second) \<close>

urust_expr  parser_word_family_nested ::
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
      parser_word_family_unqualified ParserWordFirst =
        literal (10 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_unqualified ParserWordSecond =
        literal (20 :: nat)
    \<close>
    and
    \<open>
      parser_word_family_unqualified ParserWordThird =
        literal (20 :: nat)
    \<close>
    and
    \<open>
      parser_word_ambiguity_left_qualified
        Parser_Test_Fixtures_Left.SharedWordState =
        literal (1 :: nat)
    \<close>
    and
    \<open>
      parser_word_ambiguity_right_qualified
        Parser_Test_Fixtures_Right.RightWordState =
        literal (4 :: nat)
    \<close>
    and
    \<open>
      parser_unknown_bare_identifier_binder 7 =
        literal (7 :: nat)
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
      parser_word_family_unqualified_def
      parser_word_ambiguity_left_qualified_def
      parser_word_ambiguity_right_qualified_def
      parser_unknown_bare_identifier_binder_def
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

urust_expr  parser_nested_registered_nullary
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

urust_expr
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

urust_expr
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

urust_expr
  parser_nested_registered_singleton
  \<open>
    match \<llangle>Some (ParserRegisteredSingleton 7)\<rrangle> {
      Some(ParserFixture::RegisteredSingleton(whole @ _)) \<Rightarrow>
        whole,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr
  parser_nested_native_singleton
  \<open>
    match \<llangle>Some (ParserNativeSingleton 8)\<rrangle> {
      Some(ParserNativeSingleton(whole @ _)) \<Rightarrow> whole,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr
  parser_nested_partial_constructor_alias
  \<open>
    match \<llangle>Some (ParserMatrixPayload 7)\<rrangle> {
      Some(whole @ ParserMatrixPayload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr
  parser_nested_value_fallback
  \<open>
    match \<llangle>Some ParserRawFirst\<rrangle> {
      Some(ParserRaw::First) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr
  parser_nested_range_fallback
  \<open>
    match \<llangle>Some (6 :: nat)\<rrangle> {
      Some(5..=7) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr
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

urust_expr
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

urust_expr parser_nested_registered_payload
  \<open>
    match \<llangle>Some (ParserNativePayload 7)\<rrangle> {
      Some(ParserNative::Payload(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

section\<open> Contextual bare-match classification audit \<close>

urust_expr parser_guarded_integer_case ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject, enabled)
  \<open>
    match subject {
      0 if enabled \<Rightarrow> 11,
      0 \<Rightarrow> 23,
      number \<Rightarrow> number
    }
  \<close>

urust_expr parser_integer_binder_case ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { 0 \<Rightarrow> 11, number \<Rightarrow> number } \<close>

urust_expr parser_integer_constructor_child ::
  \<open>nat option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { Some(0) \<Rightarrow> 11, Some(number) \<Rightarrow> number, None \<Rightarrow> 23 } \<close>

lemma parser_integer_case_results:
  \<open>parser_guarded_integer_case 0 True = literal 11\<close>
  \<open>parser_guarded_integer_case 0 False = literal 23\<close>
  \<open>parser_guarded_integer_case 7 True = literal 7\<close>
  \<open>parser_guarded_integer_case 7 False = literal 7\<close>
  \<open>parser_integer_binder_case 0 = literal 11\<close>
  \<open>parser_integer_binder_case 7 = literal 7\<close>
  \<open>parser_integer_constructor_child (Some 0) = literal 11\<close>
  \<open>parser_integer_constructor_child (Some 7) = literal 7\<close>
  \<open>parser_integer_constructor_child None = literal 23\<close>
  by (simp_all add: parser_guarded_integer_case_def parser_integer_binder_case_def
      parser_integer_constructor_child_def two_armed_conditional_def urust_eq_def micro_rust_simps)

chapter\<open> Slice patterns \<close>

section\<open>Ordered rest extraction\<close>

declare [[urust_verbosity = 0]]

text\<open>
The result records the complete prefix, middle, and suffix separately. Distinct values make reversal,
off-by-one extraction, and binding a suffix element in place of the middle observable.
\<close>

type_synonym parser_slice_parts =
  \<open>(nat list \<times> nat list \<times> nat list) option\<close>

urust_expr parser_slice_rest ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { [rest @ ..] \<Rightarrow> rest } \<close>

urust_expr parser_slice_bare_rest ::
  \<open>nat list \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { [..] \<Rightarrow> 7 } \<close>

urust_expr parser_slice_polymorphic_rest ::
  \<open>'a list \<Rightarrow> (unit, 'a list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { [rest @ ..] \<Rightarrow> rest } \<close>

urust_expr parser_slice_polymorphic_let_rest ::
  \<open>'a list \<Rightarrow> (unit, 'a list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> let [rest @ ..] = subject; rest \<close>

lemma parser_slice_rest_element_polymorphism:
  \<open>parser_slice_polymorphic_rest ([] :: unit list) = literal []\<close>
  \<open>parser_slice_polymorphic_rest [(), (), ()] = literal [(), (), ()]\<close>
  \<open>parser_slice_polymorphic_rest [Some (11 :: nat), None, Some 23] =
    literal [Some 11, None, Some 23]\<close>
  \<open>parser_slice_polymorphic_let_rest ([] :: unit list) = literal []\<close>
  \<open>parser_slice_polymorphic_let_rest [(), (), ()] = literal [(), (), ()]\<close>
  \<open>parser_slice_polymorphic_let_rest [Some (11 :: nat), None, Some 23] =
    literal [Some 11, None, Some 23]\<close>
  by (simp_all add: parser_slice_polymorphic_rest_def parser_slice_polymorphic_let_rest_def
      two_armed_conditional_def micro_rust_simps)

urust_expr parser_slice_prefix ::
  \<open>nat list \<Rightarrow> (unit, parser_slice_parts, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [first, rest @ ..] \<Rightarrow> \<llangle>Some ([first], rest, [])\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_suffix ::
  \<open>nat list \<Rightarrow> (unit, parser_slice_parts, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [rest @ .., last] \<Rightarrow> \<llangle>Some ([], rest, [last])\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_middle ::
  \<open>nat list \<Rightarrow> (unit, parser_slice_parts, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [first, rest @ .., last] \<Rightarrow> \<llangle>Some ([first], rest, [last])\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_asymmetric ::
  \<open>nat list \<Rightarrow> (unit, parser_slice_parts, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [first, second, rest @ .., last] \<Rightarrow>
        \<llangle>Some ([first, second], rest, [last])\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_closed ::
  \<open>nat list \<Rightarrow> (unit, parser_slice_parts, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [first, last] \<Rightarrow> \<llangle>Some ([first], [], [last])\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_rest_lengths:
  \<open>parser_slice_rest [] = literal []\<close>
  \<open>parser_slice_rest [11] = literal [11]\<close>
  \<open>parser_slice_rest [11, 23, 37] = literal [11, 23, 37]\<close>
  \<open>parser_slice_bare_rest [] = literal 7\<close>
  \<open>parser_slice_bare_rest [11] = literal 7\<close>
  \<open>parser_slice_bare_rest [11, 23, 37] = literal 7\<close>
  by (simp_all add: parser_slice_rest_def parser_slice_bare_rest_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_prefix_lengths:
  \<open>parser_slice_prefix [] = literal None\<close>
  \<open>parser_slice_prefix [11] = literal (Some ([11], [], []))\<close>
  \<open>parser_slice_prefix [11, 23] = literal (Some ([11], [23], []))\<close>
  \<open>parser_slice_prefix [11, 23, 37, 41] = literal (Some ([11], [23, 37, 41], []))\<close>
  by (simp_all add: parser_slice_prefix_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_suffix_lengths:
  \<open>parser_slice_suffix [] = literal None\<close>
  \<open>parser_slice_suffix [11] = literal (Some ([], [], [11]))\<close>
  \<open>parser_slice_suffix [11, 23] = literal (Some ([], [11], [23]))\<close>
  \<open>parser_slice_suffix [11, 23, 37, 41] = literal (Some ([], [11, 23, 37], [41]))\<close>
  by (simp_all add: parser_slice_suffix_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_middle_lengths:
  \<open>parser_slice_middle [] = literal None\<close>
  \<open>parser_slice_middle [11] = literal None\<close>
  \<open>parser_slice_middle [11, 23] = literal (Some ([11], [], [23]))\<close>
  \<open>parser_slice_middle [11, 23, 37] = literal (Some ([11], [23], [37]))\<close>
  \<open>parser_slice_middle [11, 23, 37, 41, 53] =
    literal (Some ([11], [23, 37, 41], [53]))\<close>
  by (simp_all add: parser_slice_middle_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_asymmetric_lengths:
  \<open>parser_slice_asymmetric [] = literal None\<close>
  \<open>parser_slice_asymmetric [11] = literal None\<close>
  \<open>parser_slice_asymmetric [11, 23] = literal None\<close>
  \<open>parser_slice_asymmetric [11, 23, 37] = literal (Some ([11, 23], [], [37]))\<close>
  \<open>parser_slice_asymmetric [11, 23, 37, 41] =
    literal (Some ([11, 23], [37], [41]))\<close>
  \<open>parser_slice_asymmetric [11, 23, 37, 41, 53, 67] =
    literal (Some ([11, 23], [37, 41, 53], [67]))\<close>
  by (simp_all add: parser_slice_asymmetric_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_closed_lengths:
  \<open>parser_slice_closed [] = literal None\<close>
  \<open>parser_slice_closed [11] = literal None\<close>
  \<open>parser_slice_closed [11, 23] = literal (Some ([11], [], [23]))\<close>
  \<open>parser_slice_closed [11, 23, 37, 41] = literal None\<close>
  by (simp_all add: parser_slice_closed_def two_armed_conditional_def micro_rust_simps)

text\<open>
These reference terms use HOL list operations, independently of the parser's structural matcher.
The finite equations above also check explicit values rather than deriving expected captures from
the implementation under test.
\<close>

lemma parser_slice_rest_reference:
  \<open>parser_slice_rest subject = literal subject\<close>
  by (simp add: parser_slice_rest_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_prefix_reference:
  \<open>
    parser_slice_prefix subject =
      (case subject of [] \<Rightarrow> literal None
       | first # rest \<Rightarrow> literal (Some ([first], rest, [])))
  \<close>
  by (cases subject; simp add: parser_slice_prefix_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_suffix_reference:
  \<open>
    parser_slice_suffix subject =
      (case rev subject of [] \<Rightarrow> literal None
       | ending # reversed_rest \<Rightarrow> literal (Some ([], rev reversed_rest, [ending])))
  \<close>
  by (simp add: parser_slice_suffix_def two_armed_conditional_def micro_rust_simps split: list.splits)

lemma parser_slice_middle_reference:
  \<open>
    parser_slice_middle subject =
      (case subject of [] \<Rightarrow> literal None
       | first # tail \<Rightarrow>
         (case rev tail of [] \<Rightarrow> literal None
          | ending # reversed_rest \<Rightarrow>
            literal (Some ([first], rev reversed_rest, [ending]))))
  \<close>
  by (cases subject; simp add: parser_slice_middle_def two_armed_conditional_def micro_rust_simps split: list.splits)

subsection\<open>Bare suffixes retain arbitrary middles\<close>

urust_expr parser_slice_bare_suffix ::
  \<open>nat list \<Rightarrow> (unit, nat option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [.., last] \<Rightarrow> \<llangle>Some last\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_bare_middle ::
  \<open>nat list \<Rightarrow> (unit, (nat \<times> nat) option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [first, .., last] \<Rightarrow> \<llangle>Some (first, last)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_bare_suffix_lengths:
  \<open>parser_slice_bare_suffix [] = literal None\<close>
  \<open>parser_slice_bare_suffix [11] = literal (Some 11)\<close>
  \<open>parser_slice_bare_suffix [11, 23] = literal (Some 23)\<close>
  \<open>parser_slice_bare_suffix [11, 23, 37, 41] = literal (Some 41)\<close>
  by (simp_all add: parser_slice_bare_suffix_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_bare_middle_lengths:
  \<open>parser_slice_bare_middle [] = literal None\<close>
  \<open>parser_slice_bare_middle [11] = literal None\<close>
  \<open>parser_slice_bare_middle [11, 23] = literal (Some (11, 23))\<close>
  \<open>parser_slice_bare_middle [11, 23, 37] = literal (Some (11, 37))\<close>
  \<open>parser_slice_bare_middle [11, 23, 37, 41, 53] = literal (Some (11, 53))\<close>
  by (simp_all add: parser_slice_bare_middle_def two_armed_conditional_def micro_rust_simps)

lemma parser_slice_named_and_bare_select_same_inputs:
  \<open>
    List.map (\<lambda>values. parser_slice_suffix values = literal None)
      [[], [11], [11, 23], [11, 23, 37, 41]] =
    List.map (\<lambda>values. parser_slice_bare_suffix values = literal None)
      [[], [11], [11, 23], [11, 23, 37, 41]]
  \<close>
  \<open>
    List.map (\<lambda>values. parser_slice_middle values = literal None)
      [[], [11], [11, 23], [11, 23, 37], [11, 23, 37, 41, 53]] =
    List.map (\<lambda>values. parser_slice_bare_middle values = literal None)
      [[], [11], [11, 23], [11, 23, 37], [11, 23, 37, 41, 53]]
  \<close>
  apply (simp_all only: list.map parser_slice_suffix_lengths parser_slice_bare_suffix_lengths
      parser_slice_middle_lengths parser_slice_bare_middle_lengths)
  by (simp_all add: literal_def fun_eq_iff)

urust_expr parser_slice_nested_suffix ::
  \<open>
    nat list list \<Rightarrow>
      (unit, (nat list list \<times> nat list \<times> nat) option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      [outer @ .., [inner @ .., last],] \<Rightarrow> \<llangle>Some (outer, inner, last)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_nested_bare_suffix ::
  \<open>nat list list \<Rightarrow> (unit, nat option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [.., [.., last]] \<Rightarrow> \<llangle>Some last\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_nested_suffix_results:
  \<open>parser_slice_nested_suffix [] = literal None\<close>
  \<open>parser_slice_nested_suffix [[]] = literal None\<close>
  \<open>parser_slice_nested_suffix [[11]] = literal (Some ([], [], 11))\<close>
  \<open>parser_slice_nested_suffix [[11, 23, 37]] = literal (Some ([], [11, 23], 37))\<close>
  \<open>parser_slice_nested_suffix [[11, 23], [37, 41, 53]] =
    literal (Some ([[11, 23]], [37, 41], 53))\<close>
  \<open>parser_slice_nested_suffix [[11], [23, 37], [41, 53, 67, 71]] =
    literal (Some ([[11], [23, 37]], [41, 53, 67], 71))\<close>
  \<open>parser_slice_nested_suffix [[11, 23], []] = literal None\<close>
  \<open>parser_slice_nested_bare_suffix [] = literal None\<close>
  \<open>parser_slice_nested_bare_suffix [[]] = literal None\<close>
  \<open>parser_slice_nested_bare_suffix [[11]] = literal (Some 11)\<close>
  \<open>parser_slice_nested_bare_suffix [[11, 23, 37]] = literal (Some 37)\<close>
  \<open>parser_slice_nested_bare_suffix [[11, 23], [37, 41, 53]] = literal (Some 53)\<close>
  \<open>parser_slice_nested_bare_suffix [[11, 23], []] = literal None\<close>
  by (simp_all add: parser_slice_nested_suffix_def parser_slice_nested_bare_suffix_def
      two_armed_conditional_def micro_rust_simps)

lemma parser_slice_sixty_four_elements:
  \<open>
    parser_slice_asymmetric
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
       33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
       49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64] =
    literal (Some ([1, 2],
      [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
       17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32,
       33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
       49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63], [64]))
  \<close>
  by (simp add: parser_slice_asymmetric_def two_armed_conditional_def micro_rust_simps)

section\<open>Integer patterns at structural depth\<close>

urust_expr parser_slice_integer_middle ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [0, rest @ .., 42] \<Rightarrow> \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_prefix ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject { [0, rest @ ..] \<Rightarrow> \<llangle>Some rest\<rrangle>, _ \<Rightarrow> \<llangle>None\<rrangle> }
  \<close>

urust_expr parser_slice_integer_suffix ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject { [rest @ .., 42] \<Rightarrow> \<llangle>Some rest\<rrangle>, _ \<Rightarrow> \<llangle>None\<rrangle> }
  \<close>

lemma parser_slice_integer_boundaries:
  \<open>parser_slice_integer_middle [] = literal None\<close>
  \<open>parser_slice_integer_middle [0] = literal None\<close>
  \<open>parser_slice_integer_middle [0, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_middle [0, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_middle [7, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_middle [0, 11, 23, 41] = literal None\<close>
  \<open>parser_slice_integer_prefix [] = literal None\<close>
  \<open>parser_slice_integer_prefix [0] = literal (Some [])\<close>
  \<open>parser_slice_integer_prefix [0, 11, 23] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_prefix [7, 11, 23] = literal None\<close>
  \<open>parser_slice_integer_suffix [] = literal None\<close>
  \<open>parser_slice_integer_suffix [42] = literal (Some [])\<close>
  \<open>parser_slice_integer_suffix [11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_suffix [11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_middle_def parser_slice_integer_prefix_def
      parser_slice_integer_suffix_def two_armed_conditional_def urust_eq_def micro_rust_simps)

urust_expr parser_slice_integer_option ::
  \<open>nat option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { Some(0) \<Rightarrow> 11, Some(7) \<Rightarrow> 23, _ \<Rightarrow> 37 } \<close>

urust_expr parser_slice_integer_alias ::
  \<open>
    nat option \<Rightarrow>
      (unit, (nat option \<times> nat) option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      whole @ Some(number @ 0) \<Rightarrow> \<llangle>Some (whole, number)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_nested ::
  \<open>
    nat list list option \<Rightarrow>
      (unit, (nat list \<times> nat list list) option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      Some([[0, rest @ .., 42], tail @ ..]) \<Rightarrow> \<llangle>Some (rest, tail)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_tuple ::
  \<open>
    (nat \<times> ((nat option \<times> (nat list \<times> tnil)) \<times> tnil)) \<Rightarrow>
      (unit, nat list option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      (7, (Some(0), [rest @ .., 42])) \<Rightarrow> \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

datatype parser_slice_packet =
    ParserSlicePacket (slice_tag: nat) (slice_values: \<open>nat list\<close>)
  | ParserSliceEmpty

urust_expr parser_slice_integer_struct ::
  \<open>
    parser_slice_packet \<Rightarrow>
      (unit, nat list option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      ParserSlicePacket { slice_values: [0, rest @ .., 42], slice_tag: 7 } \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_integer_deep_results:
  \<open>parser_slice_integer_option (Some 0) = literal 11\<close>
  \<open>parser_slice_integer_option (Some 7) = literal 23\<close>
  \<open>parser_slice_integer_option (Some 8) = literal 37\<close>
  \<open>parser_slice_integer_option None = literal 37\<close>
  \<open>parser_slice_integer_alias (Some 0) = literal (Some (Some 0, 0))\<close>
  \<open>parser_slice_integer_alias (Some 7) = literal None\<close>
  \<open>parser_slice_integer_alias None = literal None\<close>
  \<open>parser_slice_integer_nested (Some [[0, 11, 23, 42], [37, 41], []]) =
    literal (Some ([11, 23], [[37, 41], []]))\<close>
  \<open>parser_slice_integer_nested (Some [[0, 42]]) = literal (Some ([], []))\<close>
  \<open>parser_slice_integer_nested (Some [[7, 11, 42]]) = literal None\<close>
  \<open>parser_slice_integer_nested (Some [[0, 11, 41]]) = literal None\<close>
  \<open>parser_slice_integer_nested (Some []) = literal None\<close>
  \<open>parser_slice_integer_nested None = literal None\<close>
  \<open>parser_slice_integer_tuple (7, ((Some 0, ([11, 23, 42], TNil)), TNil)) =
    literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_tuple (8, ((Some 0, ([11, 23, 42], TNil)), TNil)) =
    literal None\<close>
  \<open>parser_slice_integer_tuple (7, ((Some 1, ([11, 23, 42], TNil)), TNil)) =
    literal None\<close>
  \<open>parser_slice_integer_tuple (7, ((Some 0, ([11, 23, 41], TNil)), TNil)) =
    literal None\<close>
  \<open>parser_slice_integer_struct (ParserSlicePacket 7 [0, 11, 23, 42]) =
    literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_struct (ParserSlicePacket 7 [0, 42]) = literal (Some [])\<close>
  \<open>parser_slice_integer_struct (ParserSlicePacket 8 [0, 11, 23, 42]) = literal None\<close>
  \<open>parser_slice_integer_struct (ParserSlicePacket 7 [1, 11, 23, 42]) = literal None\<close>
  \<open>parser_slice_integer_struct (ParserSlicePacket 7 [0, 11, 23, 41]) = literal None\<close>
  \<open>parser_slice_integer_struct ParserSliceEmpty = literal None\<close>
  by (simp_all add: parser_slice_integer_option_def parser_slice_integer_alias_def
      parser_slice_integer_nested_def parser_slice_integer_tuple_def parser_slice_integer_struct_def
      two_armed_conditional_def urust_eq_def micro_rust_simps)

subsection\<open>Supported suffixes, bases, and separators\<close>

urust_expr parser_slice_integer_u8 ::
  \<open>8 word list \<Rightarrow> (unit, 8 word list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match_case subject {
      [0u8, 0o17_u8, 1_7u8, 0x2a_u8, rest @ .., 0b10_1010u8] \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_u16 ::
  \<open>16 word list \<Rightarrow> (unit, 16 word list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match_case subject {
      [0u16, 0o17_u16, 1_7u16, 0x2a_u16, rest @ .., 0b10_1010u16] \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_u32 ::
  \<open>32 word list \<Rightarrow> (unit, 32 word list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match_case subject {
      [0u32, 0o17_u32, 1_7u32, 0x2a_u32, rest @ .., 0b10_1010u32] \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_u64 ::
  \<open>64 word list \<Rightarrow> (unit, 64 word list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match_case subject {
      [0u64, 0o17_u64, 1_7u64, 0x2a_u64, rest @ .., 0b10_1010u64] \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_integer_usize ::
  \<open>64 word list \<Rightarrow> (unit, 64 word list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match_case subject {
      [0usize, 0o17_usize, 1_7usize, 0x2a_usize, rest @ .., 0b10_1010usize] \<Rightarrow>
        \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_integer_u8_results:
  \<open>parser_slice_integer_u8 [0, 15, 17, 42, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_u8 [0, 15, 17, 42, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_u8 [1, 15, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u8 [0, 14, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u8 [0, 15, 16, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u8 [0, 15, 17, 41, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u8 [0, 15, 17, 42, 11, 23, 41] = literal None\<close>
  \<open>parser_slice_integer_u8 [0, 15, 17, 42] = literal None\<close>
  by (simp_all add: parser_slice_integer_u8_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

lemma parser_slice_integer_u16_results:
  \<open>parser_slice_integer_u16 [0, 15, 17, 42, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_u16 [0, 15, 17, 42, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_u16 [1, 15, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u16 [0, 15, 17, 42, 11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_u16_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

lemma parser_slice_integer_u32_results:
  \<open>parser_slice_integer_u32 [0, 15, 17, 42, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_u32 [0, 15, 17, 42, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_u32 [1, 15, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u32 [0, 15, 17, 42, 11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_u32_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

lemma parser_slice_integer_u64_results:
  \<open>parser_slice_integer_u64 [0, 15, 17, 42, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_u64 [0, 15, 17, 42, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_u64 [1, 15, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_u64 [0, 15, 17, 42, 11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_u64_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

lemma parser_slice_integer_usize_results:
  \<open>parser_slice_integer_usize [0, 15, 17, 42, 42] = literal (Some [])\<close>
  \<open>parser_slice_integer_usize [0, 15, 17, 42, 11, 23, 37, 42] = literal (Some [11, 23, 37])\<close>
  \<open>parser_slice_integer_usize [1, 15, 17, 42, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_usize [0, 15, 17, 42, 11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_usize_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

urust_expr parser_slice_integer_separators ::
  \<open>nat option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      Some(0b1010_) \<Rightarrow> 11,
      Some(0o17_) \<Rightarrow> 23,
      Some(0xff_) \<Rightarrow> 37,
      Some(1_000_000) \<Rightarrow> 41,
      Some(1_) \<Rightarrow> 53,
      _ \<Rightarrow> 67
    }
  \<close>

urust_expr parser_slice_integer_large_hex ::
  \<open>32 word option \<Rightarrow> (unit, bool, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { Some(0xff_00u32) \<Rightarrow> true, _ \<Rightarrow> false } \<close>

lemma parser_slice_integer_separator_results:
  \<open>parser_slice_integer_separators (Some 10) = literal 11\<close>
  \<open>parser_slice_integer_separators (Some 15) = literal 23\<close>
  \<open>parser_slice_integer_separators (Some 255) = literal 37\<close>
  \<open>parser_slice_integer_separators (Some 1000000) = literal 41\<close>
  \<open>parser_slice_integer_separators (Some 1) = literal 53\<close>
  \<open>parser_slice_integer_separators (Some 9) = literal 67\<close>
  \<open>parser_slice_integer_separators None = literal 67\<close>
  \<open>parser_slice_integer_large_hex (Some 65280) = literal True\<close>
  \<open>parser_slice_integer_large_hex (Some 65281) = literal False\<close>
  \<open>parser_slice_integer_large_hex None = literal False\<close>
  by (simp_all add: parser_slice_integer_separators_def parser_slice_integer_large_hex_def
      two_armed_conditional_def urust_eq_def true_def false_def micro_rust_simps)

urust_expr parser_slice_integer_or ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [0 | 7, rest @ .., 42 | 99] \<Rightarrow> \<llangle>Some rest\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_integer_or_results:
  \<open>parser_slice_integer_or [0, 11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_or [7, 11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_or [0, 11, 23, 99] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_or [7, 11, 23, 99] = literal (Some [11, 23])\<close>
  \<open>parser_slice_integer_or [8, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_integer_or [0, 11, 23, 41] = literal None\<close>
  by (simp_all add: parser_slice_integer_or_def two_armed_conditional_def urust_eq_def
      micro_rust_simps)

section\<open>Irrefutable ordinary bindings\<close>

urust_expr parser_slice_let_rest ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> let [rest @ ..] = subject; rest \<close>

urust_expr parser_slice_let_bare_rest ::
  \<open>nat list \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> let [..] = subject; 7 \<close>

urust_expr parser_slice_let_chain ::
  \<open>
    nat list \<Rightarrow>
      (unit, nat list \<times> nat list \<times> nat list, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    let whole @ again @ [rest @ ..] = subject;
    \<llangle>(whole, again, rest)\<rrangle>
  \<close>

urust_expr parser_slice_let_scalar_chain ::
  \<open>nat \<Rightarrow> (unit, nat \<times> nat \<times> nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> let whole @ again @ number = subject; \<llangle>(whole, again, number)\<rrangle> \<close>

type_synonym parser_slice_tuple_input =
  \<open>nat list \<times> ((nat list \<times> (bool \<times> tnil)) \<times> tnil)\<close>

type_synonym parser_slice_tuple_observation =
  \<open>parser_slice_tuple_input \<times> (nat list \<times> (bool \<times> tnil)) \<times>
    nat list \<times> nat list \<times> bool\<close>

urust_expr parser_slice_let_tuple ::
  \<open>
    parser_slice_tuple_input \<Rightarrow>
      (unit, parser_slice_tuple_observation, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    let whole @ ([left @ ..], inside @ ([right @ ..], flag)) = subject;
    \<llangle>(whole, inside, left, right, flag)\<rrangle>
  \<close>

lemma parser_slice_ordinary_binding_results:
  \<open>parser_slice_let_rest [] = literal []\<close>
  \<open>parser_slice_let_rest [11, 23, 37] = literal [11, 23, 37]\<close>
  \<open>parser_slice_let_bare_rest [] = literal 7\<close>
  \<open>parser_slice_let_bare_rest [11, 23, 37] = literal 7\<close>
  \<open>parser_slice_let_chain [] = literal ([], [], [])\<close>
  \<open>parser_slice_let_chain [11, 23, 37] =
    literal ([11, 23, 37], [11, 23, 37], [11, 23, 37])\<close>
  \<open>parser_slice_let_scalar_chain 11 = literal (11, 11, 11)\<close>
  \<open>parser_slice_let_tuple ([], (([], (False, TNil)), TNil)) =
    literal (([], (([], (False, TNil)), TNil)), ([], (False, TNil)), [], [], False)\<close>
  \<open>parser_slice_let_tuple ([11, 23], (([37, 41, 53], (True, TNil)), TNil)) =
    literal (([11, 23], (([37, 41, 53], (True, TNil)), TNil)),
      ([37, 41, 53], (True, TNil)), [11, 23], [37, 41, 53], True)\<close>
  by (simp_all add: parser_slice_let_rest_def parser_slice_let_bare_rest_def
      parser_slice_let_chain_def parser_slice_let_scalar_chain_def parser_slice_let_tuple_def
      two_armed_conditional_def micro_rust_simps)

definition parser_slice_effect ::
  \<open>nat \<Rightarrow> 'a \<Rightarrow> (nat list, 'a, unit, unit, unit, unit) expression\<close>
  where
  \<open>parser_slice_effect marker value =
    sequence (put (\<lambda>trace. trace @ [marker])) (literal value)\<close>

urust_expr parser_slice_let_rhs_once ::
  \<open>
    nat list \<Rightarrow>
      (nat list, nat list \<times> nat list \<times> nat list, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    let whole @ again @ [rest @ ..] = \<epsilon>\<open>parser_slice_effect 7 subject\<close>;
    \<llangle>(whole, again, rest)\<rrangle>
  \<close>

lemma parser_slice_let_rhs_once_results:
  \<open>evaluate (parser_slice_let_rhs_once []) [] = Success ([], [], []) [7]\<close>
  \<open>evaluate (parser_slice_let_rhs_once [11, 23, 37]) [3] =
    Success ([11, 23, 37], [11, 23, 37], [11, 23, 37]) [3, 7]\<close>
  by (simp_all add: parser_slice_let_rhs_once_def parser_slice_effect_def two_armed_conditional_def micro_rust_simps
      evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

urust_expr parser_slice_for_chain ::
  \<open>((nat list \<times> nat list \<times> nat list) list, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    for whole @ again @ [rest @ ..] in \<llangle>[[], [11], [23, 37, 41]]\<rrangle> {
      \<epsilon>\<open>put (\<lambda>seen. seen @ [(whole, again, rest)])\<close>;
    }
  \<close>

urust_expr parser_slice_for_tuple ::
  \<open>(parser_slice_tuple_observation list, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    for whole @ ([left @ ..], inside @ ([right @ ..], flag)) in
      \<llangle>[([], (([], (False, TNil)), TNil)),
        ([11, 23], (([37, 41, 53], (True, TNil)), TNil))]\<rrangle> {
      \<epsilon>\<open>put (\<lambda>seen. seen @ [(whole, inside, left, right, flag)])\<close>;
    }
  \<close>

urust_expr parser_slice_for_rhs_once ::
  \<open>(nat list, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    for whole @ again @ [rest @ ..] in
      \<epsilon>\<open>parser_slice_effect 7 ([[], [11], [23, 37, 41]] :: nat list list)\<close> {
      \<epsilon>\<open>put (\<lambda>trace. trace @ [length whole, length again, length rest])\<close>;
    }
  \<close>

lemma parser_slice_for_binding_results:
  \<open>evaluate parser_slice_for_chain [] =
    Success () [([], [], []), ([11], [11], [11]),
      ([23, 37, 41], [23, 37, 41], [23, 37, 41])]\<close>
  \<open>evaluate parser_slice_for_tuple [] =
    Success ()
      [(([], (([], (False, TNil)), TNil)), ([], (False, TNil)), [], [], False),
       (([11, 23], (([37, 41, 53], (True, TNil)), TNil)),
        ([37, 41, 53], (True, TNil)), [11, 23], [37, 41, 53], True)]\<close>
  \<open>evaluate parser_slice_for_rhs_once [] =
    Success () [7, 0, 0, 0, 1, 1, 1, 3, 3, 3]\<close>
  by (simp_all add: parser_slice_for_chain_def parser_slice_for_tuple_def
      parser_slice_for_rhs_once_def parser_slice_effect_def
      for_loop_def for_loop_core_def raw_for_loop_def sequence'_def
      iterator_ethunks_def list_into_iter_def make_iterator_from_list_def
      two_armed_conditional_def micro_rust_simps evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

text\<open>
Closure formals use the same contract: each non-binder formal destructures one value slot as
\<open>let PATTERN = slot;\<close> would.
\<close>

definition parser_slice_closure_apply ::
  \<open>'a \<Rightarrow> ('a \<Rightarrow> (unit, 'b, unit, unit, unit) function_body) \<Rightarrow>
    (unit, 'b, unit, unit, unit) function_body\<close>
  where \<open> parser_slice_closure_apply value closure \<equiv> closure value \<close>

urust_expr parser_slice_closure_rest ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> parser_slice_closure_apply(subject, |[rest @ ..]| rest) \<close>

urust_expr parser_slice_closure_bare_rest ::
  \<open>nat list \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> parser_slice_closure_apply(subject, |[..]| 7) \<close>

urust_expr parser_slice_closure_chain ::
  \<open>
    nat list \<Rightarrow>
      (unit, nat list \<times> nat list \<times> nat list, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    parser_slice_closure_apply(
      subject,
      |whole @ again @ [rest @ ..]| \<llangle>(whole, again, rest)\<rrangle>
    )
  \<close>

urust_expr parser_slice_closure_scalar_chain ::
  \<open>nat \<Rightarrow> (unit, nat \<times> nat \<times> nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    parser_slice_closure_apply(
      subject,
      |whole @ again @ number| \<llangle>(whole, again, number)\<rrangle>
    )
  \<close>

urust_expr parser_slice_closure_tuple ::
  \<open>
    parser_slice_tuple_input \<Rightarrow>
      (unit, parser_slice_tuple_observation, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    parser_slice_closure_apply(
      subject,
      |whole @ ([left @ ..], inside @ ([right @ ..], flag))|
        \<llangle>(whole, inside, left, right, flag)\<rrangle>
    )
  \<close>

lemma parser_slice_closure_binding_results:
  \<open>parser_slice_closure_rest [] = literal []\<close>
  \<open>parser_slice_closure_rest [11, 23, 37] = literal [11, 23, 37]\<close>
  \<open>parser_slice_closure_bare_rest [] = literal 7\<close>
  \<open>parser_slice_closure_bare_rest [11, 23, 37] = literal 7\<close>
  \<open>parser_slice_closure_chain [] = literal ([], [], [])\<close>
  \<open>parser_slice_closure_chain [11, 23, 37] =
    literal ([11, 23, 37], [11, 23, 37], [11, 23, 37])\<close>
  \<open>parser_slice_closure_scalar_chain 11 = literal (11, 11, 11)\<close>
  \<open>parser_slice_closure_tuple ([], (([], (False, TNil)), TNil)) =
    literal (([], (([], (False, TNil)), TNil)), ([], (False, TNil)), [], [], False)\<close>
  \<open>parser_slice_closure_tuple ([11, 23], (([37, 41, 53], (True, TNil)), TNil)) =
    literal (([11, 23], (([37, 41, 53], (True, TNil)), TNil)),
      ([37, 41, 53], (True, TNil)), [11, 23], [37, 41, 53], True)\<close>
  by (simp_all add: parser_slice_closure_rest_def parser_slice_closure_bare_rest_def
      parser_slice_closure_chain_def parser_slice_closure_scalar_chain_def
      parser_slice_closure_tuple_def parser_slice_closure_apply_def two_armed_conditional_def
      micro_rust_simps)

urust_expr parser_slice_closure_alias_formal
  \<open> |whole @ again @ [rest @ ..]| \<llangle>(whole, again, rest :: nat list)\<rrangle> \<close>

urust_expr parser_slice_closure_alias_desugared
  \<open>
    |slot| {
      let whole @ again @ [rest @ ..] = slot;
      \<llangle>(whole, again, rest :: nat list)\<rrangle>
    }
  \<close>

lemma \<open> parser_slice_closure_alias_formal = parser_slice_closure_alias_desugared \<close>
  unfolding parser_slice_closure_alias_formal_def parser_slice_closure_alias_desugared_def
  by (rule refl)

section\<open>Scope, aliases, and alternative bindings\<close>

urust_expr parser_slice_scope ::
  \<open>
    nat list \<Rightarrow> nat list \<Rightarrow>
      (unit, nat list \<times> nat list, unit, unit, unit, unit) expression
  \<close>
  (subject, rest)
  \<open>
    let answer = match subject {
      [0, rest @ .., 42] \<Rightarrow> \<epsilon>\<open>literal rest\<close>,
      _ \<Rightarrow> rest
    };
    \<llangle>(answer, rest)\<rrangle>
  \<close>

urust_expr parser_slice_sibling_scope ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [0, rest @ ..] \<Rightarrow> \<llangle>Some rest\<rrangle>,
      [rest @ .., 42] \<Rightarrow> \<epsilon>\<open>literal (Some rest)\<close>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_alternative_positions ::
  \<open>
    nat list \<Rightarrow>
      (unit, (nat \<times> nat list \<times> nat) option, unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      [0, first, rest @ .., last] | [last, rest @ .., first, 7] \<Rightarrow>
        \<llangle>Some (first, rest, last)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_constructor_collisions ::
  \<open>
    (unit, nat list \<times> nat list \<times> nat list \<times> nat list \<times> nat list,
      unit, unit, unit, unit) expression
  \<close>
  \<open>
    match \<llangle>[[11], [23, 37], [41, 53, 67], [71, 83], [97]]\<rrangle> {
      [[None @ ..], [Some @ ..], [Nil @ ..], [rev @ ..], [length @ ..]] \<Rightarrow>
        \<llangle>(None, Some, Nil, rev, length)\<rrangle>,
      _ \<Rightarrow> \<llangle>([], [], [], [], [])\<rrangle>
    }
  \<close>

urust_expr parser_slice_hol_collision ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { [zip @ ..] \<Rightarrow> \<epsilon>\<open>literal zip\<close> } \<close>

urust_expr parser_slice_apostrophised_capture ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { [tail' @ ..] \<Rightarrow> tail' } \<close>

urust_expr parser_slice_alias_range_reference ::
  \<open>
    nat list \<Rightarrow>
      (unit, (nat list \<times> nat \<times> nat list \<times> nat) option,
        unit, unit, unit, unit) expression
  \<close>
  (subject)
  \<open>
    match subject {
      whole @ &[&(first @ 1..=3), middle @ .., &(last @ 7..10),] \<Rightarrow>
        \<llangle>Some (whole, first, middle, last)\<rrangle>,
      _ \<Rightarrow> \<llangle>None\<rrangle>
    }
  \<close>

lemma parser_slice_scope_results:
  \<open>parser_slice_scope [0, 11, 23, 42] [71, 83] = literal ([11, 23], [71, 83])\<close>
  \<open>parser_slice_scope [7, 11, 23, 42] [71, 83] = literal ([71, 83], [71, 83])\<close>
  \<open>parser_slice_scope [0] [71, 83] = literal ([71, 83], [71, 83])\<close>
  \<open>parser_slice_sibling_scope [0, 11, 23, 42] = literal (Some [11, 23, 42])\<close>
  \<open>parser_slice_sibling_scope [11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_sibling_scope [11, 23, 41] = literal None\<close>
  \<open>parser_slice_alternative_positions [0, 11, 23, 37, 42] =
    literal (Some (11, [23, 37], 42))\<close>
  \<open>parser_slice_alternative_positions [11, 23, 37, 42, 7] =
    literal (Some (42, [23, 37], 11))\<close>
  \<open>parser_slice_alternative_positions [0, 11, 23, 37, 7] =
    literal (Some (11, [23, 37], 7))\<close>
  \<open>parser_slice_alternative_positions [11, 23, 37, 42] = literal None\<close>
  \<open>parser_slice_constructor_collisions =
    literal ([11], [23, 37], [41, 53, 67], [71, 83], [97])\<close>
  \<open>parser_slice_hol_collision [] = literal []\<close>
  \<open>parser_slice_hol_collision [11, 23, 37] = literal [11, 23, 37]\<close>
  \<open>parser_slice_apostrophised_capture [11, 23, 37] = literal [11, 23, 37]\<close>
  by (simp_all add: parser_slice_scope_def parser_slice_sibling_scope_def
      parser_slice_alternative_positions_def parser_slice_constructor_collisions_def
      parser_slice_hol_collision_def parser_slice_apostrophised_capture_def
      two_armed_conditional_def urust_eq_def micro_rust_simps)

lemma parser_slice_alias_range_reference_results:
  \<open>parser_slice_alias_range_reference [1, 11, 23, 7] =
    literal (Some ([1, 11, 23, 7], 1, [11, 23], 7))\<close>
  \<open>parser_slice_alias_range_reference [3, 11, 23, 37, 9] =
    literal (Some ([3, 11, 23, 37, 9], 3, [11, 23, 37], 9))\<close>
  \<open>parser_slice_alias_range_reference [2, 8] = literal (Some ([2, 8], 2, [], 8))\<close>
  \<open>parser_slice_alias_range_reference [0, 11, 23, 7] = literal None\<close>
  \<open>parser_slice_alias_range_reference [4, 11, 23, 7] = literal None\<close>
  \<open>parser_slice_alias_range_reference [2, 11, 23, 6] = literal None\<close>
  \<open>parser_slice_alias_range_reference [2, 11, 23, 10] = literal None\<close>
  \<open>parser_slice_alias_range_reference [2] = literal None\<close>
  by (simp_all add: parser_slice_alias_range_reference_def two_armed_conditional_def
      comp_ge_def comp_le_def comp_lt_def urust_conj_def true_def false_def micro_rust_simps)

section\<open>All structural case consumers\<close>

urust_expr parser_slice_if_let ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    if let [0, rest @ .., 42] = subject {
      \<llangle>Some rest\<rrangle>
    } else {
      \<llangle>None\<rrangle>
    }
  \<close>

urust_expr parser_slice_let_else ::
  \<open>nat list \<Rightarrow> (unit, nat list option, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    let [0, rest @ .., 42] = subject else { \<llangle>None\<rrangle> };
    \<llangle>Some rest\<rrangle>
  \<close>

urust_expr parser_slice_matches ::
  \<open>nat list \<Rightarrow> (unit, bool, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> matches!(subject, [0, rest @ .., 42]) \<close>

urust_expr parser_slice_matches_guard ::
  \<open>nat list \<Rightarrow> (unit, bool, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match subject {
      [0, rest @ .., 42] if matches!(rest, [_, _]) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

text\<open>
The existing matches! consumer takes a pattern without a guard. Guard composition therefore uses
the macro in an ordinary match guard, where the capture is available in the enclosing arm's scope.
\<close>

urust_expr parser_slice_total_if_let ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> if let [rest @ ..] = subject { rest } else { \<llangle>[]\<rrangle> } \<close>

urust_expr parser_slice_total_let_else ::
  \<open>nat list \<Rightarrow> (unit, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> let whole @ [rest @ ..] = subject else { \<llangle>[]\<rrangle> }; rest \<close>

lemma parser_slice_conditional_consumer_results:
  \<open>parser_slice_if_let [0, 11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_if_let [0, 42] = literal (Some [])\<close>
  \<open>parser_slice_if_let [7, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_if_let [0] = literal None\<close>
  \<open>parser_slice_let_else [0, 11, 23, 42] = literal (Some [11, 23])\<close>
  \<open>parser_slice_let_else [0, 42] = literal (Some [])\<close>
  \<open>parser_slice_let_else [7, 11, 23, 42] = literal None\<close>
  \<open>parser_slice_let_else [0] = literal None\<close>
  \<open>parser_slice_matches [0, 11, 23, 42] = literal True\<close>
  \<open>parser_slice_matches [0, 42] = literal True\<close>
  \<open>parser_slice_matches [0] = literal False\<close>
  \<open>parser_slice_matches [0, 11, 23, 41] = literal False\<close>
  \<open>parser_slice_matches_guard [0, 11, 23, 42] = literal True\<close>
  \<open>parser_slice_matches_guard [0, 11, 42] = literal False\<close>
  \<open>parser_slice_matches_guard [7, 11, 23, 42] = literal False\<close>
  \<open>parser_slice_total_if_let [] = literal []\<close>
  \<open>parser_slice_total_if_let [11, 23, 37] = literal [11, 23, 37]\<close>
  \<open>parser_slice_total_let_else [] = literal []\<close>
  \<open>parser_slice_total_let_else [11, 23, 37] = literal [11, 23, 37]\<close>
  by (simp_all add: parser_slice_if_let_def parser_slice_let_else_def parser_slice_matches_def
      parser_slice_matches_guard_def parser_slice_total_if_let_def parser_slice_total_let_else_def
      two_armed_conditional_def urust_eq_def true_def false_def micro_rust_simps)

type_synonym parser_slice_loop_state = \<open>nat list list \<times> nat list list \<times> nat\<close>

definition parser_slice_poll ::
  \<open>(parser_slice_loop_state, nat list, unit, unit, unit, unit) expression\<close>
  where
  \<open>
    parser_slice_poll =
      bind (get id) (\<lambda>(pending, seen, calls).
        case pending of
          [] \<Rightarrow> sequence (put (\<lambda>_. ([], seen, Suc calls))) (literal [])
        | next_values # remaining_inputs \<Rightarrow>
            sequence (put (\<lambda>_. (remaining_inputs, seen, Suc calls))) (literal next_values))
  \<close>

urust_expr parser_slice_while_let ::
  \<open>(parser_slice_loop_state, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    #[fuel(\<epsilon>\<open>4 :: nat\<close>)] while let [0, rest @ .., 42] =
      \<epsilon>\<open>parser_slice_poll\<close> {
      \<epsilon>\<open>put (\<lambda>(pending, seen, calls). (pending, seen @ [rest], calls))\<close>;
    }
  \<close>

urust_expr parser_slice_total_while_let ::
  \<open>(nat list, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    #[fuel(\<epsilon>\<open>2 :: nat\<close>)] while let [rest @ ..] =
      \<epsilon>\<open>parser_slice_effect 7 [11, 23, 37]\<close> {
      \<epsilon>\<open>put (\<lambda>trace. trace @ rest)\<close>;
    }
  \<close>

lemma parser_slice_while_consumer_results:
  \<open>evaluate parser_slice_while_let
      ([[0, 11, 23, 42], [0, 37, 41, 42], []], [], 0) =
    Success () ([], [[11, 23], [37, 41]], 3)\<close>
  \<open>evaluate parser_slice_while_let ([[0, 42], []], [], 0) =
    Success () ([], [[]], 2)\<close>
  \<open>evaluate parser_slice_while_let ([[7, 11, 42], [0, 23, 42]], [], 0) =
    Success () ([[0, 23, 42]], [], 1)\<close>
  \<open>evaluate parser_slice_while_let ([[0]], [], 0) = Success () ([], [], 1)\<close>
  \<open>evaluate parser_slice_total_while_let [] = Success () [7, 11, 23, 37, 7, 11, 23, 37]\<close>
  apply (simp_all add: parser_slice_while_let_def parser_slice_poll_def
      parser_slice_total_while_let_def parser_slice_effect_def
      two_armed_conditional_def urust_eq_def true_def false_def micro_rust_simps
      evaluate_def sequence_def put_def get_def literal_def Core_Expression.bind.simps)
  by (simp_all add: bounded_while.simps numeral_eq_Suc
      two_armed_conditional_def urust_eq_def urust_conj_def true_def false_def micro_rust_simps
      evaluate_def sequence_def put_def get_def literal_def Core_Expression.bind.simps)

section\<open>Evaluation and source guard order\<close>

urust_expr parser_slice_effectful_match ::
  \<open>
    nat list \<Rightarrow> bool \<Rightarrow>
      (nat list, nat list, unit, unit, unit, unit) expression
  \<close>
  (subject, enabled)
  \<open>
    match \<epsilon>\<open>parser_slice_effect 1 subject\<close> {
      [0, rest @ .., 42] if \<epsilon>\<open>parser_slice_effect 2 enabled\<close> \<Rightarrow>
        \<epsilon>\<open>parser_slice_effect 3 rest\<close>,
      [0, rest @ ..] if \<epsilon>\<open>parser_slice_effect 4 True\<close> \<Rightarrow>
        \<epsilon>\<open>parser_slice_effect 5 rest\<close>,
      _ \<Rightarrow> \<epsilon>\<open>parser_slice_effect 6 []\<close>
    }
  \<close>

lemma parser_slice_effectful_match_results:
  \<open>evaluate (parser_slice_effectful_match [0, 11, 23, 42] True) [] =
    Success [11, 23] [1, 2, 3]\<close>
  \<open>evaluate (parser_slice_effectful_match [0, 11, 23, 42] False) [] =
    Success [11, 23, 42] [1, 2, 4, 5]\<close>
  \<open>evaluate (parser_slice_effectful_match [0] True) [] = Success [] [1, 4, 5]\<close>
  \<open>evaluate (parser_slice_effectful_match [7, 11, 23, 42] True) [] = Success [] [1, 6]\<close>
  \<open>evaluate (parser_slice_effectful_match [] True) [] = Success [] [1, 6]\<close>
  by (simp_all add: parser_slice_effectful_match_def parser_slice_effect_def
      two_armed_conditional_def urust_eq_def urust_conj_def true_def false_def micro_rust_simps
      evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

urust_expr parser_slice_guarded_or_order ::
  \<open>
    nat list \<Rightarrow> nat \<Rightarrow>
      (nat list, nat list, unit, unit, unit, unit) expression
  \<close>
  (subject, expected)
  \<open>
    match \<epsilon>\<open>parser_slice_effect 1 subject\<close> {
      [capture @ .., _] | [_, capture @ ..]
        if \<epsilon>\<open>parser_slice_effect 2 (capture \<noteq> [] \<and> hd capture = expected)\<close> \<Rightarrow>
          \<epsilon>\<open>parser_slice_effect 3 capture\<close>,
      _ \<Rightarrow> \<epsilon>\<open>parser_slice_effect 9 []\<close>
    }
  \<close>

text\<open>
The first structurally successful alternative supplies the capture and the source guard runs once.
The final equation records the existing guarded-or divergence: on [11, 23, 37] with expected 23,
Rust retries the second alternative, returns [23, 37], and runs the guard twice. The current parser
continues to the next source arm after the first false guard. General guarded-or policy is separate
from rest capture; the Rust probe is retained with the feature's validation evidence.
\<close>

lemma parser_slice_guarded_or_order_results:
  \<open>evaluate (parser_slice_guarded_or_order [11, 23, 37] 11) [] =
    Success [11, 23] [1, 2, 3]\<close>
  \<open>evaluate (parser_slice_guarded_or_order [11] 11) [] = Success [] [1, 2, 9]\<close>
  \<open>evaluate (parser_slice_guarded_or_order [] 11) [] = Success [] [1, 9]\<close>
  \<open>evaluate (parser_slice_guarded_or_order [11, 23, 37] 23) [] =
    Success [] [1, 2, 9]\<close>
  by (simp_all add: parser_slice_guarded_or_order_def parser_slice_effect_def
      two_armed_conditional_def micro_rust_simps
      evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

urust_expr parser_slice_effectful_if_let ::
  \<open>nat list \<Rightarrow> (nat list, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    if let [0, rest @ .., 42] = \<epsilon>\<open>parser_slice_effect 1 subject\<close> {
      \<epsilon>\<open>parser_slice_effect 3 rest\<close>
    } else {
      \<epsilon>\<open>parser_slice_effect 9 []\<close>
    }
  \<close>

urust_expr parser_slice_effectful_let_else ::
  \<open>nat list \<Rightarrow> (nat list, nat list, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    let [0, rest @ .., 42] = \<epsilon>\<open>parser_slice_effect 1 subject\<close>
      else { \<epsilon>\<open>parser_slice_effect 9 []\<close> };
    \<epsilon>\<open>parser_slice_effect 3 rest\<close>
  \<close>

urust_expr parser_slice_effectful_matches ::
  \<open>nat list \<Rightarrow> (nat list, bool, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    match \<epsilon>\<open>parser_slice_effect 1 subject\<close> {
      [0, rest @ .., 42] if \<epsilon>\<open>parser_slice_effect 2 (length rest = 2)\<close> \<Rightarrow>
        matches!(rest, [_, _]),
      _ \<Rightarrow> false
    }
  \<close>

urust_expr parser_slice_effectful_matches_plain ::
  \<open>nat list \<Rightarrow> (nat list, bool, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open>
    matches!(\<epsilon>\<open>parser_slice_effect 1 subject\<close>, [0, rest @ .., 42])
  \<close>

lemma parser_slice_effectful_consumer_results:
  \<open>evaluate (parser_slice_effectful_if_let [0, 11, 23, 42]) [] =
    Success [11, 23] [1, 3]\<close>
  \<open>evaluate (parser_slice_effectful_if_let [7, 11, 23, 42]) [] = Success [] [1, 9]\<close>
  \<open>evaluate (parser_slice_effectful_let_else [0, 11, 23, 42]) [] =
    Success [11, 23] [1, 3]\<close>
  \<open>evaluate (parser_slice_effectful_let_else [7, 11, 23, 42]) [] = Success [] [1, 9]\<close>
  \<open>evaluate (parser_slice_effectful_matches [0, 11, 23, 42]) [] = Success True [1, 2]\<close>
  \<open>evaluate (parser_slice_effectful_matches [0, 11, 42]) [] = Success False [1, 2]\<close>
  \<open>evaluate (parser_slice_effectful_matches [7, 11, 23, 42]) [] = Success False [1]\<close>
  \<open>evaluate (parser_slice_effectful_matches_plain [0, 11, 23, 42]) [] = Success True [1]\<close>
  \<open>evaluate (parser_slice_effectful_matches_plain [0, 42]) [] = Success True [1]\<close>
  \<open>evaluate (parser_slice_effectful_matches_plain [7, 11, 23, 42]) [] = Success False [1]\<close>
  \<open>evaluate (parser_slice_effectful_matches_plain [0]) [] = Success False [1]\<close>
  by (simp_all add: parser_slice_effectful_if_let_def parser_slice_effectful_let_else_def
      parser_slice_effectful_matches_def parser_slice_effectful_matches_plain_def parser_slice_effect_def
      two_armed_conditional_def urust_eq_def urust_conj_def true_def false_def micro_rust_simps
      evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

section\<open>Binding-site boundaries\<close>

urust_expr_rejects
  \<open> let whole @ [first, rest @ ..] = \<llangle>[11, 23, 37 :: nat]\<rrangle>; whole \<close>
  \<open> unsupported or refutable pattern \<close>

urust_expr_rejects
  \<open> let whole @ [rest @ .., last] = \<llangle>[11, 23, 37 :: nat]\<rrangle>; whole \<close>
  \<open> unsupported or refutable pattern \<close>

urust_expr_rejects
  \<open> for whole @ [first, rest @ ..] in \<llangle>[[11, 23 :: nat]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern \<close>

urust_expr_rejects
  \<open> let whole @ [whole @ ..] = \<llangle>[11, 23 :: nat]\<rrangle>; whole \<close>
  \<open> duplicate pattern binder \<close>

urust_expr_rejects
  \<open> const whole @ [rest @ ..] = \<llangle>[11, 23 :: nat]\<rrangle>; whole \<close>
  \<open> unsupported or refutable pattern \<close>

urust_expr_rejects
  \<open> let mut whole @ [rest @ ..] = \<llangle>[11, 23 :: nat]\<rrangle>; whole \<close>
  \<open> invalid mutable binding pattern \<close>

urust_expr_rejects
  \<open> let whole @ &[rest @ ..] = \<llangle>[11, 23 :: nat]\<rrangle>; whole \<close>
  \<open> reference patterns are not implemented \<close>

section\<open>Lowering controls and closed generated terms\<close>

urust_expr parser_slice_numeric_switch ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { 0 \<Rightarrow> 11, 7 \<Rightarrow> 23, _ \<Rightarrow> 37 } \<close>

urust_expr parser_slice_numeric_explicit_switch ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match_switch subject { 0 \<Rightarrow> 11, 7 \<Rightarrow> 23, _ \<Rightarrow> 37 } \<close>

urust_expr parser_slice_numeric_or_switch ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { 0 | 7 \<Rightarrow> 11, _ \<Rightarrow> 37 } \<close>

urust_expr parser_slice_numeric_or_explicit_switch ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match_switch subject { 0 | 7 \<Rightarrow> 11, _ \<Rightarrow> 37 } \<close>

lemma parser_slice_numeric_or_switch_results:
  \<open>parser_slice_numeric_or_switch 0 = literal 11\<close>
  \<open>parser_slice_numeric_or_switch 7 = literal 11\<close>
  \<open>parser_slice_numeric_or_switch 8 = literal 37\<close>
  \<open>parser_slice_numeric_or_explicit_switch 0 = literal 11\<close>
  \<open>parser_slice_numeric_or_explicit_switch 7 = literal 11\<close>
  \<open>parser_slice_numeric_or_explicit_switch 8 = literal 37\<close>
  by (simp_all add: parser_slice_numeric_or_switch_def
      parser_slice_numeric_or_explicit_switch_def ncase_simps micro_rust_simps)

urust_expr parser_slice_numeric_case ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match_case subject { 0 \<Rightarrow> 11, 7 \<Rightarrow> 23, _ \<Rightarrow> 37 } \<close>

urust_expr parser_slice_numeric_binding ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject)
  \<open> match subject { 0 \<Rightarrow> 11, number \<Rightarrow> number } \<close>

urust_expr parser_slice_numeric_guarded ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (subject, enabled)
  \<open>
    match subject {
      0 if enabled \<Rightarrow> 11,
      0 \<Rightarrow> 23,
      number \<Rightarrow> number
    }
  \<close>

lemma parser_slice_numeric_control_results:
  \<open>parser_slice_numeric_switch 0 = literal 11\<close>
  \<open>parser_slice_numeric_switch 7 = literal 23\<close>
  \<open>parser_slice_numeric_switch 8 = literal 37\<close>
  \<open>parser_slice_numeric_explicit_switch 0 = literal 11\<close>
  \<open>parser_slice_numeric_explicit_switch 7 = literal 23\<close>
  \<open>parser_slice_numeric_explicit_switch 8 = literal 37\<close>
  \<open>parser_slice_numeric_case 0 = literal 11\<close>
  \<open>parser_slice_numeric_case 7 = literal 23\<close>
  \<open>parser_slice_numeric_case 8 = literal 37\<close>
  \<open>parser_slice_numeric_binding 0 = literal 11\<close>
  \<open>parser_slice_numeric_binding 7 = literal 7\<close>
  \<open>parser_slice_numeric_guarded 0 True = literal 11\<close>
  \<open>parser_slice_numeric_guarded 0 False = literal 23\<close>
  \<open>parser_slice_numeric_guarded 7 True = literal 7\<close>
  \<open>parser_slice_numeric_guarded 7 False = literal 7\<close>
  by (simp_all add: parser_slice_numeric_switch_def parser_slice_numeric_explicit_switch_def
      parser_slice_numeric_case_def parser_slice_numeric_binding_def parser_slice_numeric_guarded_def
      ncase_simps two_armed_conditional_def urust_eq_def micro_rust_simps)

definition parser_slice_source_marker ::
  \<open>(nat list, nat list, unit, unit, unit, unit) expression\<close>
  where \<open>parser_slice_source_marker = parser_slice_effect 1 [0, 11, 23, 42]\<close>

definition parser_slice_guard_marker ::
  \<open>(nat list, bool, unit, unit, unit, unit) expression\<close>
  where \<open>parser_slice_guard_marker = parser_slice_effect 2 True\<close>

definition parser_slice_body_marker ::
  \<open>nat list \<Rightarrow> (nat list, nat list, unit, unit, unit, unit) expression\<close>
  where \<open>parser_slice_body_marker rest = parser_slice_effect 3 rest\<close>

urust_expr parser_slice_term_markers ::
  \<open>(nat list, nat list, unit, unit, unit, unit) expression\<close>
  \<open>
    match \<epsilon>\<open>parser_slice_source_marker\<close> {
      [0, rest @ .., 42] if \<epsilon>\<open>parser_slice_guard_marker\<close> \<Rightarrow>
        \<epsilon>\<open>parser_slice_body_marker rest\<close>,
      _ \<Rightarrow> \<llangle>[]\<rrangle>
    }
  \<close>

lemma parser_slice_term_marker_result:
  \<open>evaluate parser_slice_term_markers [] = Success [11, 23] [1, 2, 3]\<close>
  by (simp add: parser_slice_term_markers_def parser_slice_source_marker_def
      parser_slice_guard_marker_def parser_slice_body_marker_def parser_slice_effect_def
      two_armed_conditional_def urust_eq_def urust_conj_def true_def false_def micro_rust_simps
      evaluate_def sequence_def put_def literal_def Core_Expression.bind.simps)

chapter\<open> Slice pattern syntax \<close>

section\<open> Retained binding-site restrictions \<close>

text\<open>
Rest-only slices and recursive aliases are ordinary let, for and closure-formal features. Local const,
mutable bindings, and reference binding modes retain their separate policies. A supplied list value
cannot make a pattern requiring an element irrefutable.
\<close>

urust_expr_rejects
  \<open> |[tail, ..]| () \<close>
  \<open> unsupported or refutable pattern in a closure formal position \<close>

urust_expr_rejects
  \<open> let mut [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> invalid mutable binding pattern \<close>

urust_expr_rejects
  \<open> let mut whole @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> invalid mutable binding pattern \<close>

urust_expr_rejects
  \<open> let mut ([tail @ ..], other) = \<llangle>([] :: nat list, (0 :: nat, TNil))\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> const [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> const whole @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [first, tail @ ..] = \<llangle>[1 :: nat, 4, 9]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [tail @ .., last] = \<llangle>[1 :: nat, 4, 9]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [first] = \<llangle>[1 :: nat]\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> let whole @ [] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open>
    let (whole @ [first, tail @ ..], other) =
      \<llangle>([1 :: nat, 4, 9], (0 :: nat, TNil))\<rrangle>; ()
  \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> for whole @ [first, tail @ ..] in \<llangle>[[1 :: nat, 4, 9]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> for [tail @ .., last] in \<llangle>[[1 :: nat, 4, 9]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> for whole @ [first] in \<llangle>[[1 :: nat]]\<rrangle> { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> let whole @ &[tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> reference patterns are not implemented \<close>

urust_expr_rejects
  \<open> for whole @ &mut [tail @ ..] in \<llangle>[[] :: nat list]\<rrangle> { () } \<close>
  \<open> reference patterns are not implemented \<close>

urust_expr_rejects
  \<open> match_switch \<llangle>[] :: nat list\<rrangle> { [tail @ ..] \<Rightarrow> () } \<close>
  \<open> unsupported match_switch pattern \<close>

urust_expr_rejects
  \<open> let tail @ [tail @ ..] = \<llangle>[] :: nat list\<rrangle>; () \<close>
  \<open> duplicate pattern binder "tail" \<close>

urust_expr_rejects
  \<open> for tail @ [tail @ ..] in \<llangle>[[] :: nat list]\<rrangle> { () } \<close>
  \<open> duplicate pattern binder "tail" \<close>

section\<open> Rest-only slice list type constraints \<close>

text\<open>
Both named and bare rest-only slices require a list at every structural depth, including when the
matcher is total and can use a direct abstraction. These sources use supported patterns and binding
sites; rejection must come from checked type elaboration. The bodies leave captures unconstrained
so they cannot impose the missing list type on behalf of the pattern.
\<close>

urust_expr_rejects
  \<open> let [rest@..] = true; rest \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match true { [rest@..] \<Rightarrow> rest } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match true { [..] \<Rightarrow> () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some([rest@..]) \<Rightarrow> rest,
      _ \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> match_case \<llangle>Some True\<rrangle> { Some([..]) \<Rightarrow> (), _ \<Rightarrow> () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> for [rest@..] in \<llangle>[True]\<rrangle> { let _ = rest; () } \<close>
  \<open> no instances \<close>

urust_expr_rejects
  \<open> for [..] in \<llangle>[True]\<rrangle> { () } \<close>
  \<open> no instances \<close>

urust_expr_rejects
  \<open> let [rest@..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let outer @ inner @ [rest@..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let outer @ inner @ [..] = true; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> if let [rest@..] = true { () } else { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> if let [..] = true { () } else { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [rest@..] = true else { () }; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> let [..] = true else { () }; () \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [rest@..] = true { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open> #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [..] = true { () } \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(_) | Some([..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(rest) | Some([rest@..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

text\<open>
Every source arm retains its type constraints, including arms covered by an earlier singleton
constructor arm. Captures must also have the same type across alternatives, even when unused.
\<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some True\<rrangle> {
      Some(_) \<Rightarrow> (),
      Some([..]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some [11 :: nat]\<rrangle> {
      Some([rest@..]) | Some([rest]) \<Rightarrow> rest,
      None \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some [11 :: nat]\<rrangle> {
      Some([rest@..]) | Some([rest]) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some ([11 :: nat], [True], TNil)\<rrangle> {
      Some(([rest@..], _)) | Some((_, [rest@..])) \<Rightarrow> rest,
      None \<Rightarrow> \<llangle>undefined\<rrangle>
    }
  \<close>
  \<open> Type unification failed \<close>

urust_expr_rejects
  \<open>
    match_case \<llangle>Some ([11 :: nat], [True], TNil)\<rrangle> {
      Some(([rest@..], _)) | Some((_, [rest@..])) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> Type unification failed \<close>

chapter\<open> Matcher stability \<close>

declare [[urust_pretty = false]]

text\<open>
The expectations below are frozen from urust-parsing 39c334c93d8deb5bfa04f8ef9a45eaf87cca4934.
Each equation unfolds only its declaration and closes with kernel reflexivity.
They intentionally retain redundant cases and the distinction between generated-test failure
and source-guard failure. The imported suites retain the stateful guard, scrutinee-count,
navigation, source-range, rejection, and recovery regressions.
\<close>

urust_expr matcher_stability_overlap ::
  \<open>nat option \<times> nat option \<times> tnil \<Rightarrow> bool \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input, enabled)
  \<open>
    match input {
      (Some(value), _) | (_, Some(value)) if enabled \<Rightarrow> value,
      (Some(value), _) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_alias ::
  \<open>nat option option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      whole @ Some(Some(value)) \<Rightarrow> value,
      Some(_) \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_range ::
  \<open>nat option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      Some(2..=4) \<Rightarrow> 1,
      Some(7) \<Rightarrow> 2,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_slice ::
  \<open>nat list option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      Some([head, ..]) if False \<Rightarrow> head,
      Some([head, ..]) \<Rightarrow> head,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_if_let ::
  \<open>nat option option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open> if let Some(Some(value)) = input { value } else { 0 } \<close>

urust_expr matcher_stability_let_else ::
  \<open>nat option option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open> let Some(Some(value)) = input else { 0 }; value \<close>

urust_expr matcher_stability_while_let ::
  \<open>nat option option \<Rightarrow>
    (unit, unit, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    #[fuel(\<epsilon>\<open>2 :: nat\<close>)]
    while let Some(Some(value)) = input { () }
  \<close>

urust_expr matcher_stability_matches ::
  \<open>nat option option \<Rightarrow>
    (unit, bool, unit, unit, unit, unit) expression\<close>
  (input)
  \<open> matches!(input, Some(Some(_))) \<close>

urust_fn matcher_stability_function
  \<open>
    fn StabilityFunction(input: u64) -> u64 {
      match Some(input) { Some(value) if false \<Rightarrow> value, _ \<Rightarrow> 0 }
    }
  \<close>

urust_expr [abbrev] matcher_stability_abbreviation ::
  \<open>nat option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open> match input { Some(value) if False \<Rightarrow> value, _ \<Rightarrow> 0 } \<close>

urust_expr _ ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> match Some(3) { Some(2..=4) \<Rightarrow> 1, _ \<Rightarrow> 0 } \<close>

lemma matcher_stability_overlap_frozen:
  \<open>
    matcher_stability_overlap =
    ((\<lambda>x xa.
   literal x \<bind>
   (\<lambda>x.
       (\<lambda>(xb, xc).
           case_option
            ((\<lambda>(xb, xc).
                 case_option
                  ((\<lambda>(x, xa).
                       case_option (literal 0)
                        (\<lambda>x.
                            (\<lambda>(xa, xb). case_tnil (literal x) xb)
                             xa)
                        x)
                    x)
                  (\<lambda>xb.
                      case_tnil
                       (two_armed_conditional (literal xa) (literal xb)
                         ((\<lambda>(x, xa).
                              case_option (literal 0)
                               (\<lambda>x.
                                   (\<lambda>(xa, xb).
 case_tnil (literal x) xb)
                                    xa)
                               x)
                           x))
                       xc)
                  xb)
              xc)
            (\<lambda>xb.
                (\<lambda>(xc, xd).
                    case_option
                     (case_tnil
                       (two_armed_conditional (literal xa) (literal xb)
                         ((\<lambda>(x, xa).
                              case_option (literal 0)
                               (\<lambda>x.
                                   (\<lambda>(xa, xb).
 case_tnil (literal x) xb)
                                    xa)
                               x)
                           x))
                       xd)
                     (\<lambda>xc.
                         case_tnil
                          (two_armed_conditional (literal xa) (literal xb)
                            ((\<lambda>(x, xa).
                                 case_option (literal 0)
                                  (\<lambda>x.
(\<lambda>(xa, xb). case_tnil (literal x) xb) xa)
                                  x)
                              x))
                          xd)
                     xc)
                 xc)
            xb)
        x)) :: nat option \<times> nat option \<times> tnil
\<Rightarrow> bool
              \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_overlap_def by (rule refl)

lemma matcher_stability_alias_frozen:
  \<open>
    matcher_stability_alias =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal 0)
        (\<lambda>xa.
            case_option (literal 1)
             (\<lambda>xa. literal x \<bind> (\<lambda>x. literal xa)) xa)
        x)) :: nat option option
\<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_alias_def by (rule refl)

lemma matcher_stability_range_frozen:
  \<open>
    matcher_stability_range =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option
        (case_option (literal 0)
          (\<lambda>x.
              two_armed_conditional
               (literal x \<bind>
                (\<lambda>x.
                    two_armed_conditional (urust_eq (literal x) (literal 7))
                     (literal True) (literal False)))
               (literal x \<bind>
                (\<lambda>x.
                    two_armed_conditional (urust_eq (literal x) (literal 7))
                     (literal 2) undefined))
               (literal 0))
          x)
        (\<lambda>xa.
            two_armed_conditional
             (literal xa \<bind>
              (\<lambda>x.
                  two_armed_conditional
                   (urust_conj (comp_ge (literal x) (literal 2))
                     (comp_le (literal x) (literal 4)))
                   (literal True) (literal False)))
             (literal xa \<bind>
              (\<lambda>x.
                  two_armed_conditional
                   (urust_conj (comp_ge (literal x) (literal 2))
                     (comp_le (literal x) (literal 4)))
                   (literal 1) undefined))
             (case_option (literal 0)
               (\<lambda>x.
                   two_armed_conditional
                    (literal x \<bind>
                     (\<lambda>x.
                         two_armed_conditional
                          (urust_eq (literal x) (literal 7)) (literal True)
                          (literal False)))
                    (literal x \<bind>
                     (\<lambda>x.
                         two_armed_conditional
                          (urust_eq (literal x) (literal 7)) (literal 2)
                          undefined))
                    (literal 0))
               x))
        x)) :: nat option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_range_def by (rule refl)

lemma matcher_stability_slice_frozen:
  \<open>
    matcher_stability_slice =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option
        (case_option (literal 0)
          (\<lambda>x. case_list (literal 0) (\<lambda>x xa. literal x) x)
          x)
        (\<lambda>xa.
            case_list
             (case_option (literal 0)
               (\<lambda>x.
                   case_list (literal 0) (\<lambda>x xa. literal x) x)
               x)
             (\<lambda>xa xb.
                 two_armed_conditional (literal False) (literal xa)
                  (case_option (literal 0)
                    (\<lambda>x.
                        case_list (literal 0) (\<lambda>x xa. literal x) x)
                    x))
             xa)
        x)) :: nat list option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_slice_def by (rule refl)

lemma matcher_stability_if_let_frozen:
  \<open>
    matcher_stability_if_let =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal 0)
        (\<lambda>x. case_option (literal 0) (\<lambda>x. literal x) x) x)) :: nat option option
\<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_if_let_def by (rule refl)

lemma matcher_stability_let_else_frozen:
  \<open>
    matcher_stability_let_else =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal 0)
        (\<lambda>x. case_option (literal 0) (\<lambda>x. literal x) x) x)) :: nat option option
\<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_let_else_def by (rule refl)

lemma matcher_stability_while_let_frozen:
  \<open>
    matcher_stability_while_let =
    ((\<lambda>x.
   bounded_while 2
    (literal x \<bind>
     (\<lambda>x.
         case_option (literal False)
          (\<lambda>x.
              case_option (literal False)
               (\<lambda>x. sequence (literal ()) (literal True)) x)
          x))
    (literal ())) :: nat option option
\<Rightarrow> (unit, unit, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_while_let_def by (rule refl)

lemma matcher_stability_matches_frozen:
  \<open>
    matcher_stability_matches =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal False)
        (\<lambda>x.
            case_option (literal False) (\<lambda>x. literal True) x)
        x)) :: nat option option
\<Rightarrow> (unit, bool, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_matches_def by (rule refl)

schematic_goal matcher_stability_function_frozen:
  \<open>
    matcher_stability_function =
    ((\<lambda>x.
   FunctionBody
    (funcall1 (lift_fun1 Some) (literal x) \<bind>
     (\<lambda>x.
         case_option (literal 0)
          (\<lambda>x. two_armed_conditional false (literal x) (literal 0))
          x))) :: 64 word \<Rightarrow> (?'a, 64 word, ?'b, ?'c, ?'d) function_body)
  \<close>
  unfolding matcher_stability_function_def by (rule refl)

lemma matcher_stability_abbreviation_frozen:
  \<open>
    matcher_stability_abbreviation =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal 0)
        (\<lambda>x.
            two_armed_conditional (literal False) (literal x) (literal 0))
        x)) :: nat option \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  by (rule refl)

text\<open>
The declarations below are frozen from 3245e9443b75b533a46cfbb2db0f7132b8c6726e in the same way.
Each reaches a root rule that no parser test reached at that commit. A clause shape covered by
an earlier shape whose first row has a generated test is not emitted, both between enumerated
root groups and within one tuple root group. In a match without wildcard rows, a cut prefix that
covers the type leaves no catchall. A failure suffix keeps a binding catchall, both after a false
source guard and after a nested generated-test miss; the frozen equations do not distinguish
that catchall from a wildcard one, so the last two declarations reach it without pinning it.
\<close>

urust_expr matcher_stability_subsumed ::
  \<open>nat option option \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      Some(Some(3)) \<Rightarrow> 1,
      Some(Some(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_subsumed_tuple ::
  \<open>nat option \<times> nat option \<times> tnil \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      (None, Some(3)) \<Rightarrow> 1,
      (None, Some(value)) \<Rightarrow> value,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_covered_cut ::
  \<open>nat option \<Rightarrow> bool \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (input, enabled)
  \<open>
    match input {
      Some(_) | None if enabled \<Rightarrow> 1,
      Some(value) \<Rightarrow> value,
      None \<Rightarrow> 0
    }
  \<close>

urust_expr matcher_stability_guard_binder ::
  \<open>nat option \<Rightarrow> bool \<Rightarrow>
    (unit, nat option, unit, unit, unit, unit) expression\<close>
  (input, enabled)
  \<open>
    match input {
      Some(value) if enabled \<Rightarrow> Some(value),
      other \<Rightarrow> other
    }
  \<close>

urust_expr matcher_stability_nested_binder ::
  \<open>nat option option \<Rightarrow>
    (unit, nat option option, unit, unit, unit, unit) expression\<close>
  (input)
  \<open>
    match input {
      Some(Some(3)) \<Rightarrow> None,
      other \<Rightarrow> other
    }
  \<close>

lemma matcher_stability_subsumed_frozen:
  \<open>
    matcher_stability_subsumed =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option
        (case_option (literal 0)
          (\<lambda>x. case_option (literal 0) (\<lambda>x. literal x) x) x)
        (\<lambda>xa.
            two_armed_conditional
             (literal xa \<bind>
              (\<lambda>x.
                  case_option (literal False)
                   (\<lambda>x.
                       two_armed_conditional
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) (literal False)))
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) undefined))
                        (literal False))
                   x))
             (literal xa \<bind>
              (\<lambda>x.
                  case_option undefined
                   (\<lambda>x.
                       two_armed_conditional
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) (literal False)))
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3)) (literal 1)
                              undefined))
                        undefined)
                   x))
             (case_option (literal 0)
               (\<lambda>x.
                   case_option (literal 0) (\<lambda>x. literal x) x)
               x))
        x)) :: nat option option
\<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_subsumed_def by (rule refl)

lemma matcher_stability_subsumed_tuple_frozen:
  \<open>
    matcher_stability_subsumed_tuple =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       (\<lambda>(xa, xb).
           case_option
            ((\<lambda>(xa, xb).
                 case_tnil
                  (two_armed_conditional
                    (literal xa \<bind>
                     (\<lambda>x.
                         case_option (literal False)
                          (\<lambda>x.
                              two_armed_conditional
                               (literal x \<bind>
                                (\<lambda>x.
                                    two_armed_conditional
                                     (urust_eq (literal x) (literal 3))
                                     (literal True) (literal False)))
                               (literal x \<bind>
                                (\<lambda>x.
                                    two_armed_conditional
                                     (urust_eq (literal x) (literal 3))
                                     (literal True) undefined))
                               (literal False))
                          x))
                    (literal xa \<bind>
                     (\<lambda>x.
                         case_option undefined
                          (\<lambda>x.
                              two_armed_conditional
                               (literal x \<bind>
                                (\<lambda>x.
                                    two_armed_conditional
                                     (urust_eq (literal x) (literal 3))
                                     (literal True) (literal False)))
                               (literal x \<bind>
                                (\<lambda>x.
                                    two_armed_conditional
                                     (urust_eq (literal x) (literal 3))
                                     (literal 1) undefined))
                               undefined)
                          x))
                    ((\<lambda>(x, xa).
                         case_option
                          ((\<lambda>(x, xa).
                               case_option (literal 0)
                                (\<lambda>x. case_tnil (literal x) xa) x)
                            xa)
                          (\<lambda>x. literal 0) x)
                      x))
                  xb)
              xb)
            (\<lambda>xa.
                (\<lambda>(x, xa).
                    case_option
                     ((\<lambda>(x, xa).
                          case_option (literal 0)
                           (\<lambda>x. case_tnil (literal x) xa) x)
                       xa)
                     (\<lambda>x. literal 0) x)
                 x)
            xa)
        x)) :: nat option \<times> nat option \<times> tnil
\<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_subsumed_tuple_def by (rule refl)

lemma matcher_stability_covered_cut_frozen:
  \<open>
    matcher_stability_covered_cut =
    ((\<lambda>x xa.
   literal x \<bind>
   (\<lambda>x.
       case_option
        (two_armed_conditional (literal xa) (literal 1)
          (case_option (case_option (literal 0) (\<lambda>x. undefined) x)
            (\<lambda>x. literal x) x))
        (\<lambda>xb.
            two_armed_conditional (literal xa) (literal 1)
             (case_option
               (case_option (literal 0) (\<lambda>x. undefined) x)
               (\<lambda>x. literal x) x))
        x)) :: nat option
\<Rightarrow> bool
              \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_covered_cut_def by (rule refl)

lemma matcher_stability_guard_binder_frozen:
  \<open>
    matcher_stability_guard_binder =
    ((\<lambda>x xa.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal None)
        (\<lambda>xb.
            two_armed_conditional (literal xa)
             (funcall1 (lift_fun1 Some) (literal xb)) (literal x))
        x)) :: nat option
\<Rightarrow> bool
              \<Rightarrow> (unit, nat option, unit, unit, unit,
                             unit) expression)
  \<close>
  unfolding matcher_stability_guard_binder_def by (rule refl)

lemma matcher_stability_nested_binder_frozen:
  \<open>
    matcher_stability_nested_binder =
    ((\<lambda>x.
   literal x \<bind>
   (\<lambda>x.
       case_option (literal x)
        (\<lambda>xa.
            two_armed_conditional
             (literal xa \<bind>
              (\<lambda>x.
                  case_option (literal False)
                   (\<lambda>x.
                       two_armed_conditional
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) (literal False)))
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) undefined))
                        (literal False))
                   x))
             (literal xa \<bind>
              (\<lambda>x.
                  case_option undefined
                   (\<lambda>x.
                       two_armed_conditional
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal True) (literal False)))
                        (literal x \<bind>
                         (\<lambda>x.
                             two_armed_conditional
                              (urust_eq (literal x) (literal 3))
                              (literal None) undefined))
                        undefined)
                   x))
             (literal x))
        x)) :: nat option option
\<Rightarrow> (unit, nat option option, unit, unit, unit, unit) expression)
  \<close>
  unfolding matcher_stability_nested_binder_def by (rule refl)

chapter\<open>Turbofish\<close>

section\<open> Additive payload fixtures \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

definition generic_dimension_call ::
  \<open>nat \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_dimension_call _ \<equiv> cf0 \<close>

definition GENERIC_LIMIT_A :: nat where
  \<open> GENERIC_LIMIT_A = 11 \<close>

definition GENERIC_LIMIT_B :: nat where
  \<open> GENERIC_LIMIT_B = 13 \<close>

urust_expr generic_payload_01 \<open> generic_dimension_call::<1>() \<close>

urust_expr generic_payload_02 \<open> generic_dimension_call::<GENERIC_LIMIT_A>() \<close>

urust_expr generic_payload_03 \<open> generic_dimension_call::<1 + GENERIC_LIMIT_A>() \<close>

urust_expr generic_payload_04
  \<open> generic_dimension_call::<GENERIC_LIMIT_A + 3 + GENERIC_LIMIT_B>() \<close>

section\<open> Exact canonical names \<close>

urust_notation (call) cf0 ("GenericFactory::<TypeA>::make")

urust_notation (call) cf0 ("GenericContainer::<2>::make")

urust_expr generic_exact_type_a \<open> GenericFactory::<TypeA>::make() \<close>

urust_expr generic_exact_container_2 \<open> GenericContainer::<2>::make() \<close>

definition exact_fallback ::
  \<open>int \<Rightarrow> int \<Rightarrow>
    (unit, int, unit, unit, unit) function_body\<close>
  where \<open> exact_fallback parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument) \<close>

micro_rust_notation (call) exact_fallback ("Exact::f")

urust_notation (call) cf0 ("Exact::f::<N>")

urust_expr exact_generic_wins \<open> Exact::f::<N>() \<close>

urust_expr exact_generic_fallback \<open> Exact::f::<1>(2) \<close>

section\<open> Canonical exact-key regressions \<close>

urust_notation (call) cf0 ("AuditSpaced::<a + b>::new")

urust_notation cf0 ("AuditAuto::<a + b>::new")

urust_notation (call) cf0 ("AuditIdentifier::<div>::new")

urust_notation (call) cf0 ("AuditIdentifier::<mod>::new")

urust_notation (call) macro_shout ("AuditMacro::<a + b>::shout!")

urust_notation (config) [shadow_no_warn] "AuditConfig::<a + b>::new"

urust_expr audit_spaced_compact \<open> AuditSpaced::<a+b>::new() \<close>

urust_expr audit_spaced_spaced \<open> AuditSpaced::<a + b>::new() \<close>

urust_expr audit_spaced_multiline
  \<open>
    AuditSpaced::<
      a +
      b
    >::new()
  \<close>

urust_expr audit_auto \<open> AuditAuto::<a+b>::new() \<close>

urust_expr audit_div_identifier \<open> AuditIdentifier::<div>::new() \<close>

urust_expr audit_mod_identifier \<open> AuditIdentifier::<mod>::new() \<close>

urust_expr audit_macro \<open> AuditMacro::<a+b>::shout!(true) \<close>

end
