theory Parser_Test_Constructor_Matching
  imports
    Parser_Test_Utils
    Constructor_Ambiguity_Left
    Constructor_Ambiguity_Right
    Misc.Simple_Word_Enums
    Shallow_Micro_Rust.Core_Expression_Lemmas
begin

declare [[urust_conformance = true]]
declare [[urust_pp_test = true]]

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
