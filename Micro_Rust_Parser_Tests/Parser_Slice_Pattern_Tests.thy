theory Parser_Slice_Pattern_Tests
  imports Parser_Pattern_Matching_Tests
begin

declare [[urust_verbosity = 0]]

section\<open>Ordered rest extraction\<close>

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

ML_val\<open>
  local
    val ctxt = \<^context>
    fun assert message condition =
      if condition then () else error ("slice pattern term audit: " ^ message)

    fun rhs_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of |> Logic.dest_equals |> snd

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) => if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val list_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>list\<close> of
         SOME {casex = Const (name, _), ...} => name
       | _ => error "slice pattern term audit: missing list case metadata")

    val pattern_type_probe_prefix = "_urust_pattern_type_probe_"

    fun probe_abstraction (Abs (name, _, _)) =
          String.isPrefix pattern_type_probe_prefix name
      | probe_abstraction _ = false

    fun probe_marker (Abs (name, _, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Free (name, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Var ((name, _), _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Const (name, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker _ = false

    fun erased_type_probes name =
      let val definition = Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))
      in
        assert (name ^ " retained a pattern typing probe abstraction")
          (not (Term.exists_subterm probe_abstraction definition));
        assert (name ^ " retained a pattern typing probe marker")
          (not (Term.exists_subterm probe_marker definition))
      end

    fun closed name =
      let val rhs = rhs_of name
      in
        assert (name ^ " leaked generated free variables") (null (Term.add_frees rhs []));
        assert (name ^ " leaked schematic variables") (null (Term.add_vars rhs []));
        erased_type_probes name
      end

    val _ = List.app closed
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_polymorphic_rest",
       "parser_slice_polymorphic_let_rest", "parser_slice_prefix",
       "parser_slice_suffix", "parser_slice_middle", "parser_slice_asymmetric",
       "parser_slice_closed", "parser_slice_bare_suffix", "parser_slice_bare_middle",
       "parser_slice_nested_suffix", "parser_slice_nested_bare_suffix",
       "parser_slice_integer_middle", "parser_slice_integer_prefix", "parser_slice_integer_suffix",
       "parser_slice_integer_option", "parser_slice_integer_alias", "parser_slice_integer_nested",
       "parser_slice_integer_tuple", "parser_slice_integer_struct",
       "parser_slice_integer_u8", "parser_slice_integer_u16", "parser_slice_integer_u32",
       "parser_slice_integer_u64", "parser_slice_integer_usize", "parser_slice_integer_or",
       "parser_slice_let_rest", "parser_slice_let_chain", "parser_slice_let_tuple",
       "parser_slice_let_rhs_once", "parser_slice_for_chain", "parser_slice_for_tuple",
       "parser_slice_for_rhs_once", "parser_slice_scope", "parser_slice_sibling_scope",
       "parser_slice_alternative_positions", "parser_slice_constructor_collisions",
       "parser_slice_hol_collision", "parser_slice_alias_range_reference",
       "parser_slice_if_let", "parser_slice_let_else", "parser_slice_matches",
       "parser_slice_matches_guard", "parser_slice_while_let", "parser_slice_total_while_let",
       "parser_slice_effectful_match", "parser_slice_guarded_or_order",
       "parser_slice_effectful_if_let", "parser_slice_effectful_let_else",
       "parser_slice_effectful_matches", "parser_slice_effectful_matches_plain",
       "parser_slice_numeric_switch",
       "parser_slice_numeric_explicit_switch", "parser_slice_numeric_or_switch",
       "parser_slice_numeric_or_explicit_switch",
       "parser_slice_numeric_case", "parser_slice_numeric_binding",
       "parser_slice_numeric_guarded", "parser_slice_term_markers"]

    val automatic = rhs_of "parser_slice_numeric_switch"
    val explicit = rhs_of "parser_slice_numeric_explicit_switch"
    val _ = assert "numeral-only bare match changed its explicit-switch term shape"
      (Term.aconv (automatic, explicit))
    val _ = assert "numeral-only bare match lost its switch selector"
      (count_constant \<^const_name>\<open>ncase_selector\<close> automatic = 1)

    val automatic_or = rhs_of "parser_slice_numeric_or_switch"
    val explicit_or = rhs_of "parser_slice_numeric_or_explicit_switch"
    val _ = assert "numeral or-pattern changed its explicit-switch term shape"
      (Term.aconv (automatic_or, explicit_or))
    val _ = assert "numeral or-pattern lost its switch selector"
      (count_constant \<^const_name>\<open>ncase_selector\<close> automatic_or = 1)
    val _ = assert "numeral or-pattern retained case equality"
      (count_constant \<^const_name>\<open>urust_eq\<close> automatic_or = 0)
    val _ = assert "numeral or-pattern retained case conditional lowering"
      (count_constant \<^const_name>\<open>two_armed_conditional\<close> automatic_or = 0)

    val _ = List.app
      (fn name =>
        let val term = rhs_of name
        in
          assert (name ^ " selected switch lowering")
            (count_constant \<^const_name>\<open>ncase_selector\<close> term = 0);
          assert (name ^ " lost value-pattern equality")
            (count_constant \<^const_name>\<open>urust_eq\<close> term > 0)
        end)
      ["parser_slice_numeric_case", "parser_slice_numeric_binding", "parser_slice_numeric_guarded",
       "parser_slice_integer_option", "parser_slice_integer_middle"]

    val _ = List.app
      (fn name => assert (name ^ " retained an undefined fallback")
        (count_constant \<^const_name>\<open>undefined\<close> (rhs_of name) = 0))
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_let_rest",
       "parser_slice_let_chain", "parser_slice_let_tuple",
       "parser_slice_total_if_let", "parser_slice_total_let_else", "parser_slice_total_while_let"]

    val _ = List.app
      (fn name => assert (name ^ " lost its direct rest-only abstraction")
        (count_constant list_case_name (rhs_of name) = 0))
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_let_rest",
       "parser_slice_let_chain", "parser_slice_total_if_let", "parser_slice_total_let_else"]

    val _ = List.app
      (fn (name, term) =>
        assert ("duplicated or dropped " ^ name)
          (count_constant name term = 1))
      (map (fn name => (name, rhs_of "parser_slice_term_markers"))
        [\<^const_name>\<open>parser_slice_source_marker\<close>,
         \<^const_name>\<open>parser_slice_guard_marker\<close>,
         \<^const_name>\<open>parser_slice_body_marker\<close>])

    val unchanged_let =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "let value = \<llangle>11 :: nat\<rrangle>; value")
    val reference_let = \<^term>\<open>
      bind (literal (11 :: nat)) (\<lambda>value. literal value)
        :: (unit, nat, unit, unit, unit, unit) expression
    \<close>
    val _ = assert "ordinary identifier let changed its checked term shape"
      (Term.aconv_untyped (unchanged_let, reference_let))
  in
    val _ = writeln "Slice capture, integer lowering, totality, hygiene, and evaluation-shape audits passed"
  end
\<close>

end
