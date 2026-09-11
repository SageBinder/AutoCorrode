theory Parser_Test_Constructor_Matching
  imports
    Parser_Test_Utils
    Constructor_Ambiguity_Left
    Constructor_Ambiguity_Right
    Misc.Simple_Word_Enums
    Shallow_Micro_Rust.Core_Expression_Lemmas
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
  | ParserTertiaryStatus

type_synonym parser_nested_overlap_input =
  \<open>
    (unit, parser_nested_status) result \<times>
      ((unit, parser_nested_status) result \<times> tnil)
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
                (literal (Err error)))
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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
      urust_eq_def
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

    fun has_ordered_equality_results [] _ = true
      | has_ordered_equality_results
          ((expected_constructor, expected_result) :: rest) term =
        let
          fun matches
                (Const (conditional, _) $
                  (Const (equality, _) $ _ $
                    (Const (literal, _) $ constructor)) $
                  success $ failure) =
                conditional =
                    \<^const_name>\<open>two_armed_conditional\<close> andalso
                  equality = \<^const_name>\<open>urust_eq\<close> andalso
                  literal = \<^const_name>\<open>literal\<close> andalso
                  constant_name constructor = expected_constructor andalso
                  Term.aconv_untyped (success, expected_result) andalso
                  has_ordered_equality_results rest failure
            | matches _ = false
        in Term.exists_subterm matches term end

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
                    (literal (3 :: nat))))) ::
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
                    (literal (0 :: nat))))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val guarded_order_expected =
      \<^term>\<open>
        (bind (literal parser_nested_guarded_scrutinee)
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow> literal (2 :: nat)
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserPrimaryStatus))
                  (two_armed_conditional
                    (literal parser_nested_guard_marker)
                    (literal (1 :: nat))
                    (literal (2 :: nat)))
                  (literal (2 :: nat)))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val global_source_order_expected =
      \<^term>\<open>
        (bind (literal parser_nested_interleaved_scrutinee)
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow>
                two_armed_conditional
                  (literal parser_nested_interleaved_guard)
                  (literal (2 :: nat))
                  (literal (4 :: nat))
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserPrimaryStatus))
                  (literal (1 :: nat))
                  (two_armed_conditional
                    (literal parser_nested_interleaved_guard)
                    (literal (2 :: nat))
                    (two_armed_conditional
                      (urust_eq
                        (literal error)
                        (literal ParserSecondaryStatus))
                      (literal (3 :: nat))
                      (literal (4 :: nat)))))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val overlapping_tuple_expected =
      \<^term>\<open>
        (bind (literal parser_nested_overlap_scrutinee)
          (\<lambda>value.
            case value of
              (Err first_error, second, TNil) \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal first_error)
                    (literal ParserPrimaryStatus))
                  (literal (1 :: nat))
                  (case
                    (Err first_error, second, TNil)
                   of
                    (_, Err second_error, TNil) \<Rightarrow>
                      two_armed_conditional
                        (urust_eq
                          (literal second_error)
                          (literal ParserSecondaryStatus))
                        (literal (2 :: nat))
                        (literal (3 :: nat))
                  | _ \<Rightarrow> literal (3 :: nat))
            | (first, Err second_error, TNil) \<Rightarrow>
                (case
                  (first, Err second_error, TNil)
                 of
                  (Err first_error, second, TNil) \<Rightarrow>
                    two_armed_conditional
                      (urust_eq
                        (literal first_error)
                        (literal ParserPrimaryStatus))
                      (literal (1 :: nat))
                      (case
                        (Err first_error, second, TNil)
                       of
                        (_, Err later_error, TNil) \<Rightarrow>
                          two_armed_conditional
                            (urust_eq
                              (literal later_error)
                              (literal ParserSecondaryStatus))
                            (literal (2 :: nat))
                            (literal (3 :: nat))
                      | _ \<Rightarrow> literal (3 :: nat))
                | _ \<Rightarrow>
                    two_armed_conditional
                      (urust_eq
                        (literal second_error)
                        (literal ParserSecondaryStatus))
                      (literal (2 :: nat))
                      (literal (3 :: nat)))
            | _ \<Rightarrow> literal (3 :: nat))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val alias_wildcard_expected =
      \<^term>\<open>
        (bind (literal parser_nested_alias_wild_scrutinee)
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow> literal (2 :: nat)
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserTertiaryStatus))
                  (literal (0 :: nat))
                  (two_armed_conditional
                    (urust_eq
                      (literal error)
                      (literal ParserPrimaryStatus))
                    (bind (literal value)
                      (\<lambda>whole.
                        literal (parser_nested_alias_tag whole)))
                    (literal (2 :: nat))))) ::
          (unit, nat, unit, unit, unit, unit) expression
      \<close>
    val alias_binder_expected =
      \<^term>\<open>
        (bind (literal parser_nested_alias_binder_scrutinee)
          (\<lambda>value.
            case value of
              Ok result \<Rightarrow> literal (Ok result)
            | Err error \<Rightarrow>
                two_armed_conditional
                  (urust_eq
                    (literal error)
                    (literal ParserTertiaryStatus))
                  (literal parser_nested_alias_probe_result)
                  (two_armed_conditional
                    (urust_eq
                      (literal error)
                      (literal ParserPrimaryStatus))
                    (bind (literal value)
                      (\<lambda>whole.
                        literal (parser_nested_alias_rewrite whole)))
                    (literal (Err error))))) ::
          (unit, (unit, parser_nested_status) result,
            unit, unit, unit, unit) expression
      \<close>
    val ordered =
      checked_ordered_term
        "parser_nested_registered_ordered" ordered_expected
    val ordered_or =
      checked_ordered_term
        "parser_nested_registered_or_ordered" ordered_or_expected
    val guarded_order =
      checked_ordered_term
        "parser_nested_registered_guard_order"
        guarded_order_expected
    val global_source_order =
      checked_ordered_term
        "parser_nested_global_source_order"
        global_source_order_expected
    val overlapping_tuple =
      checked_ordered_term
        "parser_nested_overlapping_tuple"
        overlapping_tuple_expected
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
    val (exhaustive_lhs, exhaustive) =
      equation_of "parser_nested_exhaustive_outer_shapes"
    val (exhaustive_guarded_lhs, exhaustive_guarded) =
      equation_of "parser_nested_exhaustive_outer_shapes_guarded"
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
    val exhaustive_guarded_instantiated =
      instantiate_definition exhaustive_guarded
        [\<^term>\<open>
            parser_nested_exhaustive_first_miss_scrutinee
          \<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val (global_ok_branch, global_err_branch) =
      result_case_branches global_source_order
    val alias_wildcard =
      checked_ordered_term
        "parser_nested_alias_wildcard" alias_wildcard_expected
    val alias_binder =
      checked_ordered_term
        "parser_nested_alias_binder" alias_binder_expected
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
    val (_, exhaustive_arguments) =
      Term.strip_comb exhaustive_lhs
    val (_, exhaustive_guarded_arguments) =
      Term.strip_comb exhaustive_guarded_lhs
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
        ("exhaustive outer-shape fixture emitted a redundant outer clause: " ^
          string_of_int (length (outer_case_clauses exhaustive)))
        (length (outer_case_clauses exhaustive) = 4)
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
        ("guarded exhaustive outer-shape fixture emitted a redundant outer clause: " ^
          string_of_int (length
            (outer_case_clauses exhaustive_guarded)))
        (length (outer_case_clauses exhaustive_guarded) = 4)
    val expected_equality_order =
      map constant_name
        [\<^term>\<open>ParserPrimaryStatus\<close>,
         \<^term>\<open>ParserSecondaryStatus\<close>]
    val overlapping_or_order =
      [(constant_name
          \<^term>\<open>ParserPrimaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>),
       (constant_name
          \<^term>\<open>ParserSecondaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>),
       (constant_name
          \<^term>\<open>ParserSecondaryStatus\<close>,
        \<^term>\<open>literal (2 :: nat)\<close>)]
    val overlapping_or_reversed_order =
      [(constant_name
          \<^term>\<open>ParserSecondaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>),
       (constant_name
          \<^term>\<open>ParserPrimaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>),
       (constant_name
          \<^term>\<open>ParserSecondaryStatus\<close>,
        \<^term>\<open>literal (2 :: nat)\<close>)]
    val exhaustive_outer_order =
      [(constant_name
          \<^term>\<open>ParserPrimaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>),
       (constant_name
          \<^term>\<open>ParserSecondaryStatus\<close>,
        \<^term>\<open>literal (1 :: nat)\<close>)]
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
      assert "guarded same-shape arm lost its generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          guarded_order = 1)
    val _ =
      assert "global source-order fixture duplicated the outer case"
        (count_constant result_case_name global_source_order = 1)
    val _ =
      assert "global source-order fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_scrutinee\<close>
          global_source_order = 1)
    val _ =
      assert "global source-order fixture lost an equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          global_source_order = 2)
    val _ =
      assert "global source-order fixture changed guard evaluation count"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_source_order = 2)
    val _ =
      assert "global source-order Ok branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_ok_branch = 1)
    val _ =
      assert "global source-order Err branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_err_branch = 1)
    val _ =
      assert "overlapping tuple fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_overlap_scrutinee\<close>
          overlapping_tuple = 1)
    val _ =
      assert "overlapping or-pattern alternatives changed source order"
        (has_ordered_equality_results
          overlapping_or_order overlapping_or)
    val _ =
      assert "exhaustive outer-shape equality continuations changed order"
        (has_ordered_equality_results
          exhaustive_outer_order exhaustive)
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
      assert "alias/wildcard fixture lost a generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_wildcard = 2)
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
      assert "alias/binder fixture lost a generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_binder = 2)
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
    val option_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt
          (fst (dest_Type \<^typ>\<open>parser_native_case option\<close>)) of
         SOME {casex, ...} => constant_name casex
       | NONE =>
           error "constructor matching audit: missing option case sugar")
    val _ =
      assert "argument-bearing nested constructor lost recursive case lowering"
        (count_constant native_case_name nested_payload > 0)
    val _ =
      assert "argument-bearing nested constructor was normalized as equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nested_payload = 0)

    val mixed = rhs_of "parser_nested_registered_mixed"
    val _ =
      assert "mixed nested alternatives duplicated the outer option case"
        (count_constant option_case_name mixed = 1)
    val _ =
      assert "mixed nested alternatives lost the native payload case"
        (count_constant native_case_name mixed > 0)
    val _ =
      assert "mixed nested alternatives lost exact-nullary equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> mixed = 1)
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
    fun find_empty_conditional term =
      (case Term.strip_comb term of
         (Const (name, _), [condition, _, else_branch]) =>
           if name = \<^const_name>\<open>two_armed_conditional\<close> andalso
              count_constant native_empty_name condition = 1
           then SOME (condition, else_branch)
           else find_empty_conditional_arguments term
       | _ => find_empty_conditional_arguments term)
    and find_empty_conditional_arguments (left $ right) =
          (case find_empty_conditional left of
             SOME result => SOME result
           | NONE => find_empty_conditional right)
      | find_empty_conditional_arguments (Abs (_, _, body)) =
          find_empty_conditional body
      | find_empty_conditional_arguments _ = NONE
    val (_, mixed_after_empty) =
      (case find_empty_conditional mixed of
         SOME result => result
       | NONE =>
           error
             "constructor matching audit: missing mixed empty conditional")
    val _ =
      assert "mixed nested source order moved payload before exact empty"
        (count_constant native_case_name mixed_after_empty > 0)

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
