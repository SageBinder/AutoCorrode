(* Readable examples of accepted-surface improvements, primitive-type path heads, expression
   declarations and grammar boundaries. The ML audits are in Parser_Syntax_ML_Tests. *)

theory Parser_Syntax_Examples
  imports
    Parser_Expression_Examples
    Parser_Function_Examples
    Parser_Test_Fixtures_Left
    Parser_Test_Fixtures_Right
    Misc.Simple_Word_Enums
begin

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

text\<open>
Each example exercises syntax accepted by the production parser beyond the
baseline positive corpus.
\<close>

chapter\<open>Accepted language improvements\<close>

section\<open>Total conditional bindings\<close>

text\<open>
The parser omits an unreachable wildcard fallback when resolved-pattern coverage proves an
\<open>if let\<close> or \<open>let ... else\<close> pattern total. Fallback lowering still occurs for diagnostics and
markup, but the discarded term does not constrain final HOL type checking; the regression audit pins
that behavior separately.
\<close>

subsection\<open>Basic total patterns\<close>

urust_expr improvement_if_let_total_wildcard
  \<open> if let _ = \<llangle>1 :: nat\<rrangle> { 2 } else { 0 } \<close>

urust_expr improvement_let_else_total_wildcard
  \<open> let _ = \<llangle>1 :: nat\<rrangle> else { 0 }; 2 \<close>

urust_expr improvement_if_let_total_identifier
  \<open> if let value = \<llangle>1 :: nat\<rrangle> { value } else { 0 } \<close>

urust_expr improvement_let_else_total_identifier
  \<open> let value = \<llangle>1 :: nat\<rrangle> else { 0 }; value \<close>

urust_expr improvement_if_let_total_group
  \<open> if let (value) = \<llangle>1 :: nat\<rrangle> { value } else { 0 } \<close>

urust_expr improvement_let_else_total_group
  \<open> let (value) = \<llangle>1 :: nat\<rrangle> else { 0 }; value \<close>

urust_expr improvement_if_let_total_alias
  \<open> if let whole @ _ = \<llangle>1 :: nat\<rrangle> { whole } else { 0 } \<close>

urust_expr improvement_let_else_total_alias
  \<open> let whole @ _ = \<llangle>1 :: nat\<rrangle> else { 0 }; whole \<close>

urust_expr improvement_if_let_total_discards_fallback_type
  \<open> if let _ = \<llangle>1 :: nat\<rrangle> { 2 } else { false } \<close>

urust_expr improvement_let_else_total_discards_fallback_type
  \<open> let _ = \<llangle>1 :: nat\<rrangle> else { false }; 2 \<close>

subsection\<open>Structural and constructor totality\<close>

urust_expr improvement_if_let_total_grouped_tuple
  \<open>
    if let ((left, (middle, right))) =
      (\<llangle>1 :: nat\<rrangle>, (\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>)) {
      \<llangle>left + middle + right\<rrangle>
    } else {
      0
    }
  \<close>

urust_expr improvement_let_else_total_grouped_tuple
  \<open>
    let ((left, (middle, right))) =
      (\<llangle>1 :: nat\<rrangle>, (\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>))
      else { 0 };
    \<llangle>left + middle + right\<rrangle>
  \<close>

urust_expr improvement_if_let_total_tnil
  \<open> if let TNil = TNil { () } else { () } \<close>

urust_expr improvement_let_else_total_tnil
  \<open> let TNil = TNil else { () }; () \<close>

urust_expr improvement_if_let_total_option
  \<open>
    if let Some(_) | None = \<llangle>Some (1 :: nat)\<rrangle> {
      1
    } else {
      0
    }
  \<close>

urust_expr improvement_let_else_total_option
  \<open>
    let Some(_) | None = \<llangle>Some (1 :: nat)\<rrangle> else { 0 };
    1
  \<close>

urust_expr improvement_if_let_total_nested_option
  \<open>
    if let Some(Some(_) | None) | None =
      \<llangle>Some (Some (1 :: nat))\<rrangle> {
      1
    } else {
      0
    }
  \<close>

urust_expr improvement_let_else_total_nested_option
  \<open>
    let Some(Some(_) | None) | None =
      \<llangle>Some (Some (1 :: nat))\<rrangle> else { 0 };
    1
  \<close>

subsection\<open>Total alternatives and wrappers\<close>

urust_expr improvement_if_let_total_wildcard_alternative
  \<open>
    if let Some(_) | _ = \<llangle>Some (1 :: nat)\<rrangle> {
      1
    } else {
      0
    }
  \<close>

urust_expr improvement_let_else_total_wildcard_alternative
  \<open>
    let Some(_) | _ = \<llangle>Some (1 :: nat)\<rrangle> else { 0 };
    1
  \<close>

urust_expr improvement_if_let_total_borrow_wrapper
  \<open> if let &_ = \<llangle>1 :: nat\<rrangle> { 1 } else { 0 } \<close>

urust_expr improvement_let_else_total_borrow_wrapper
  \<open> let &_ = \<llangle>1 :: nat\<rrangle> else { 0 }; 1 \<close>

subsection\<open>One-armed total if-let\<close>

urust_expr improvement_if_let_total_one_armed_unit
  \<open> if let _ = \<llangle>1 :: nat\<rrangle> { () } \<close>

urust_expr improvement_if_let_total_one_armed_value
  \<open> if let value = \<llangle>1 :: nat\<rrangle> { value } \<close>

urust_expr cast_corpus_nested_tuple
  \<open>
    ((if true { 0 } else { 1 }, true),
     if false { (2 as u32, 3 as u32) } else { (4, 5) })
  \<close>

section\<open>Registered literal patterns\<close>

text\<open>
An exact registered literal whose complete backend is an authentic datatype constructor remains a
constructor pattern and carries the catalogue's arity, family, and selector metadata. Other
registered constants and expressions are value patterns, so they avoid datatype case translation
when the backend is not a constructor.
\<close>

urust_expr registered_constructor_pattern_boundary
  \<open>
    match_case \<llangle>RegisteredUnary 9\<rrangle> {
      Registered::Nullary \<Rightarrow> 0,
      Registered::Unary(value) \<Rightarrow> value,
      Registered::Other \<Rightarrow> 1
    }
  \<close>

urust_expr path_constant_pattern
  \<open>
    match_case Color::Red {
      Color::Red \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

urust_expr path_constant_match
  \<open>
    match Color::Red {
      Color::Red \<Rightarrow> 1,
      _ \<Rightarrow> 0
    }
  \<close>

section\<open>Mixed conditional chains\<close>

text\<open>
The grammar accepts right-associated mixtures of ordinary
\<open>if\<close> and \<open>if let\<close> arms.
\<close>

urust_expr improvement_if_to_if_let_chain
  \<open>
    if false {
      0
    } else if let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> {
      value
    } else {
      2
    }
  \<close>

urust_expr improvement_if_let_to_if_chain
  \<open>
    if let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> {
      value
    } else if false {
      2
    } else {
      3
    }
  \<close>

urust_expr improvement_if_let_to_if_let_without_final_else
  \<open>
    if let Some(first) = Some(()) {
      let _ = first;
      ()
    } else if let Some(second) = Some(()) {
      let _ = second;
      ()
    }
  \<close>

urust_expr improvement_mixed_conditional_right_association
  \<open>
    if false {
      0
    } else if let Some(first) = \<llangle>Some (1 :: nat)\<rrangle> {
      first
    } else if false {
      2
    } else if let Some(last) = \<llangle>Some (3 :: nat)\<rrangle> {
      last
    } else {
      4
    }
  \<close>

urust_expr improvement_mixed_conditional_semicolon_free_statement
  \<open>
    if false {
      ()
    } else if let Some(value) = Some(()) {
      let _ = value;
      ()
    } else {
      ()
    }
    ()
  \<close>

urust_expr improvement_mixed_conditional_binder_isolation
  \<open>
    let value = \<llangle>1 :: nat\<rrangle>;
    if let Some(value) = \<llangle>Some (2 :: nat)\<rrangle> {
      \<llangle>value\<rrangle>
    } else if \<llangle>value = 1\<rrangle> {
      value
    } else if let Some(value) = Some(\<llangle>value + 1\<rrangle>) {
      \<llangle>value\<rrangle>
    } else {
      value
    }
  \<close>

urust_expr improvement_mixed_conditional_guard
  \<open>
    match_case Some(()) {
      Some(_) if if false {
        false
      } else if let Some(flag) = Some(true) {
        flag
      } else if true {
        true
      } else {
        false
      } \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

section\<open>Semicolon-free explicit matches\<close>

text\<open>
The dedicated grammar treats all three match flavours as control expressions. Explicit
\<open>match_case\<close> and \<open>match_switch\<close> can therefore prefix a following body without a
semicolon, both in an ordinary body and in a match guard.
\<close>

urust_expr improvement_match_case_semicolon_free_statement
  \<open>
    match_case Some(()) { Some(value) \<Rightarrow> value, None \<Rightarrow> () }
    ()
  \<close>

urust_expr improvement_match_switch_semicolon_free_statement
  \<open>
    match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () }
    ()
  \<close>

urust_expr improvement_match_case_semicolon_free_guard
  \<open>
    match_case Some(()) {
      Some(_) if
        match_case Some(()) { Some(value) \<Rightarrow> value, None \<Rightarrow> () }
        true
        \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr improvement_match_switch_semicolon_free_guard
  \<open>
    match_case Some(()) {
      Some(_) if
        match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> (), _ \<Rightarrow> () }
        true
        \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

section\<open>Rust line comments\<close>

text\<open>
The production lexer skips \<open>//\<close> comments only in its ordinary Rust state.
Literal \<open>//\<close> inside strings and both antiquotation states remains content;
these rows cover comments at token boundaries and end of input.
\<close>

urust_expr improvement_line_comment_full_line
  \<open>
    // full-line comment
    ()
  \<close>

urust_expr improvement_line_comment_end_of_line
  \<open>
    ();
    () // end-of-line comment
  \<close>

urust_expr improvement_line_comment_between_tokens
  \<open>
    \<llangle>1 :: 32 word\<rrangle> // between the operands and operator
      + \<llangle>2 :: 32 word\<rrangle>
  \<close>

urust_expr improvement_line_comment_operator_text
  \<open>
    () // += => \<Rightarrow> /= /* block-shaped text */
  \<close>

urust_expr improvement_line_comment_empty
  \<open>
    {
      //
      ()
    }
  \<close>

urust_expr improvement_line_comment_eof
  \<open> () // comment at EOF \<close>

urust_expr improvement_d21_struct_line_comments
  \<open>
    D21Pair {
      left: 1_u64, // separator
      right: 2_u64
    }
  \<close>

urust_expr improvement_d21_struct_comment_at_eof
  \<open> D21One { value: 1_u64 } // end \<close>

urust_expr improvement_line_comment_nested_adjacent
  \<open>
    if true {// then branch
      {// nested block
        ()// body value
      }// after nested block
    } else {// else branch
      ()
    }
  \<close>

section\<open>Rust-compatible integer suffixes\<close>

text\<open>
The lexer accepts Rust's glued integer suffixes as well as the retained
underscore spelling.
\<close>

urust_expr improvement_integer_suffix_decimal_u8
  \<open> 1u8 \<close>

urust_expr improvement_integer_suffix_hex_u8
  \<open> 0xffu8 \<close>

urust_expr improvement_integer_suffix_decimal_u16
  \<open> 2u16 \<close>

urust_expr improvement_integer_suffix_hex_u16
  \<open> 0x12abu16 \<close>

urust_expr improvement_integer_suffix_decimal_u32
  \<open> 3u32 \<close>

urust_expr improvement_integer_suffix_hex_u32
  \<open> 0x1234abcdu32 \<close>

urust_expr improvement_integer_suffix_decimal_u64
  \<open> 4u64 \<close>

urust_expr improvement_integer_suffix_hex_u64
  \<open> 0x123456789abcdef0u64 \<close>

urust_expr improvement_integer_suffix_decimal_usize
  \<open> 5usize \<close>

urust_expr improvement_integer_suffix_hex_usize
  \<open> 0xffffffff0usize \<close>

section\<open>ASCII match arrows\<close>

urust_expr improvement_ascii_match_arrow
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>

urust_expr improvement_ascii_match_arrow_guarded
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) if True => x, None => 0 } \<close>

urust_expr improvement_ascii_match_arrow_nested
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) => match x { 0 => 0, _ => x },
      None => 0
    }
  \<close>

urust_expr improvement_ascii_match_arrow_case
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>

urust_expr improvement_ascii_match_arrow_switch
  \<open>
    match_switch \<llangle>1 :: nat\<rrangle> {
      0 => \<llangle>False\<rrangle>,
      _ => \<llangle>True\<rrangle>
    }
  \<close>

section\<open>Empty blocks\<close>

urust_expr improvement_empty_block_value
  \<open> {} \<close>

urust_expr improvement_empty_block_branches
  \<open> if true {} else {} \<close>

urust_expr improvement_empty_block_nested
  \<open> {{}} \<close>

urust_expr improvement_empty_block_statement
  \<open> {} () \<close>

urust_expr improvement_empty_unsafe_block
  \<open> unsafe {} \<close>

section\<open>Trailing commas\<close>

text\<open>
Trailing commas are accepted consistently in calls, arms, constructor patterns,
tuples, array literals, struct patterns, and slice patterns.
\<close>

urust_expr improvement_trailing_array_literal
  \<open> [\<llangle>1 :: 32 word\<rrangle>, \<llangle>2 :: 32 word\<rrangle>,] \<close>

urust_expr improvement_trailing_direct_call
  \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>,) \<close>

urust_expr improvement_trailing_antiquotation_call
  \<open> \<epsilon>\<open>cf1\<close>(\<llangle>1 :: 64 word\<rrangle>,) \<close>

urust_expr improvement_trailing_function_literal_call
  \<open> \<llangle>Suc\<rrangle>\<^sub>1(0,) \<close>

context
  fixes trailing_antiquotation_call14 :: \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body \<close>
begin
urust_expr improvement_trailing_antiquotation_call14
  \<open>
    \<epsilon>\<open>trailing_antiquotation_call14\<close>(
      0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,
    )
  \<close>
end

urust_expr improvement_trailing_function_literal_call14
  \<open>
    \<llangle>\<lambda>a b c d e f g h i j k l m n.
      (a + b + c + d + e + f + g + h + i + j + k + l + m + n :: nat)
    \<rrangle>\<^sub>1\<^sub>4
      (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13,)
  \<close>

urust_expr improvement_trailing_method_call
  \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>,) \<close>

urust_expr improvement_trailing_registered_path_call
  \<open> plus2::lifted(\<llangle>3 :: 64 word\<rrangle>,) \<close>

context
  fixes receiver :: nat
  fixes generic_method ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      (unit, nat, unit, unit, unit) function_body\<close>
begin
urust_expr improvement_trailing_turbofish_method_call
  \<open> receiver.generic_method::<5>(6,) \<close>
end

urust_expr improvement_turbofish_punctuation_newlines
  \<open>
    turbofish_ignore_two
      ::
      <
        (1 + 2),
        (True)
      >
      (\<llangle>4 :: 64 word\<rrangle>,)
  \<close>

urust_expr improvement_trailing_guarded_arm
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if True \<Rightarrow> x,
      None \<Rightarrow> 0,
    }
  \<close>

urust_expr improvement_trailing_constructor_pattern
  \<open> match_case \<llangle>P2 1 2\<rrangle> { P2(x, y,) \<Rightarrow> x } \<close>

urust_expr improvement_trailing_tuple_expression
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>,) \<close>

urust_expr improvement_trailing_tuple_pattern
  \<open>
    let (x, y,) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>);
    x
  \<close>

urust_expr improvement_trailing_struct_pattern
  \<open>
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left: x, adv_right: y, } \<Rightarrow> x,
      _ \<Rightarrow> 0
    }
  \<close>

datatype trailing_comma_fixture =
  TrailingComma
    (trailing_option: "64 word option")
    (trailing_values: "64 word list")

text\<open>
This composed row puts all trailing-comma sites in one source: nested tuple,
call, arm, struct, constructor, and slice lists, including a guarded arm and a
method call. The witness removes separators only.
\<close>

text\<open>
C1-I5 checks this guarded extended pattern with the shared source-arm handler; its checked term
uses the parser's source-ordered guarded-arm lowering.
\<close>

urust_expr improvement_trailing_composed
  \<open>
    let (x, y,) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>,);
    cf2(
      match \<llangle>TrailingComma (Some 3) [4, 5]\<rrangle> {
        TrailingComma {
          trailing_option: Some(z,),
          trailing_values: [head, .., tail,],
        } if True \<Rightarrow>
          x.cf2(z,),
        _ \<Rightarrow>
          y,
      },
      y,
    )
  \<close>

section\<open>Composed accepted-surface improvements\<close>

text\<open>
This row combines line comments, glued suffixes, trailing separators, postfix
propagation, mixed conditional chains, ASCII arrows, and empty blocks. The
showoff retains the same composed parser source.
\<close>

urust_expr improvement_showoff_composition
  \<open>
    // These spellings are accepted only by the dedicated parser.
    let seeds = [1u64, 2u64,];
    let seed = seeds[0usize];
    let bumped = Some(cf1(seed,))?.cf1();
    let selected =
      if seed == 0u64 {
        seed
      } else if let Some(value) = Some(bumped) {
        value
      } else if bumped > 2u64 {
        bumped
      } else {
        seed
      };
    match Some(selected) {
      Some(value) => (value, {}, unsafe {},),
      None => (0u64, {}, unsafe {},),
    }
  \<close>

section\<open>Compositional range patterns\<close>

datatype improvement_packet =
    ImprovementPacket
      (improvement_tag: nat)
      (improvement_values: "nat list")
  | ImprovementEmpty

text\<open>
The new pattern grammar permits ranges wherever another pattern is expected. Here
one range occupies a struct field and another occupies a nonfinal slice element.
\<close>

urust_expr improvement_struct_and_slice_ranges
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket {
        improvement_tag: 1..=3,
        improvement_values: [4..=6, last]
      } \<Rightarrow>
        last,
      _ \<Rightarrow>
        0
    }
  \<close>

text\<open>
The same design makes a range valid in a nonfinal positional constructor
argument.
\<close>

urust_expr improvement_constructor_range
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket(1..=3, values) \<Rightarrow>
        1,
      _ \<Rightarrow>
        0
    }
  \<close>

text\<open>
Bare top-level ranges in \<open>while let\<close> are ordinary Rust-shaped patterns.
The shared pattern grammar admits both range forms directly.
\<close>

urust_expr improvement_while_let_range_exclusive
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 1..3 =
      \<llangle>2 :: nat\<rrangle> {
      ()
    }
  \<close>

urust_expr improvement_while_let_range_inclusive
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 1..=3 =
      \<llangle>2 :: nat\<rrangle> {
      ()
    }
  \<close>

section\<open>Structural while-let lowering\<close>

text\<open>
Structurally irrefutable patterns lower directly without a generated false
fallback. Grouping is transparent, aliases bind the complete scrutinee before
applying their inner pattern, and tuple direct lowering is reserved for tuples
whose children are all irrefutable. Reference-pattern wrappers are erased by
case preparation before this classification.
\<close>

urust_expr improvement_wrapped_grouped_range
  \<open>
    match_case \<llangle>Some (3 :: nat)\<rrangle> {
      Some(&(2..=4)) \<Rightarrow> \<llangle>True\<rrangle>,
      _ \<Rightarrow> \<llangle>False\<rrangle>
    }
  \<close>

urust_expr improvement_while_let_wrapped_tuple_children
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let (&left, & mut right) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>left + right\<rrangle>;
    }
  \<close>

urust_expr improvement_while_let_grouped_tuple
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let ((left, right)) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>left + right\<rrangle>;
    }
  \<close>

urust_expr improvement_while_let_refutable_tuple
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let (Some(value), other) =
      (\<llangle>Some (1 :: nat)\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>value + other\<rrangle>;
    }
  \<close>

urust_expr improvement_while_let_wildcard
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let _ =
      \<llangle>1 :: nat\<rrangle> {
      ()
    }
  \<close>

urust_expr improvement_while_let_identifier
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let value =
      \<llangle>1 :: nat\<rrangle> {
      let _ = value;
      ()
    }
  \<close>

urust_expr improvement_while_let_alias_wildcard
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let whole @ _ =
      \<llangle>1 :: nat\<rrangle> {
      let _ = whole;
      ()
    }
  \<close>

urust_expr improvement_while_let_nested_range
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(1..=3) =
      \<llangle>Some (2 :: nat)\<rrangle> {
      ()
    }
  \<close>

urust_expr improvement_while_let_return_scrutinee
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) =
      return \<llangle>Some (1 :: nat)\<rrangle> {
      let _ = value;
      ()
    }
  \<close>

section\<open>Hygienic aliases across nested lowering\<close>

text\<open>
Slice-rest patterns require generated nested matches. The new parser represents
the alias structurally, so \<open>whole\<close> remains bound to the packet rather than to
an internal list value.
\<close>

urust_expr improvement_hygienic_alias
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      whole @ ImprovementPacket {
        improvement_tag: _,
        improvement_values: [head, .., tail]
      } \<Rightarrow>
        whole,
      _ \<Rightarrow>
        \<llangle>ImprovementEmpty\<rrangle>
    }
  \<close>

section\<open>Hygienic mutable wildcard\<close>

definition improvement_reference_fixture ::
  \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> improvement_reference_fixture \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture

text\<open>
The pattern AST gives \<open>let mut _\<close> the same allocated-reference term shape
as an unused mutable name while representing the continuation binder as an anonymous abstraction.
\<close>

urust_expr improvement_mutable_wildcard
  \<open>
    let keep = \<llangle>5 :: nat\<rrangle>;
    let mut _ = \<llangle>7 :: nat\<rrangle>;
    keep
  \<close>

section\<open>Recursive reference-prefix composition\<close>

no_adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture

text\<open>
The recursive reference-prefix tier accepts mixed and deeper unparenthesized
compositions, including triple dereference.
\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes rr ::
    \<open>(unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref\<close>
    and rrr ::
      \<open>(unit, unit,
          (unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref)
        Global_Store.ref\<close>
    and r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
begin

urust_expr improvement_recursive_borrow_deref
  \<open> &*rr \<close>

urust_expr improvement_recursive_deref_mut_borrow
  \<open> *& mut r \<close>

urust_expr improvement_recursive_triple_deref
  \<open> ***rrr \<close>

end

section\<open>Expression-antiquotation places\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

text\<open>
Expression antiquotations may serve as assignment places. These rows cover a
fixed reference and capture of a mutable local inside the antiquotation body.
\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
begin

urust_expr improvement_antiquotation_place
  \<open> \<epsilon>\<open>literal r\<close> = rhs \<close>

urust_expr improvement_antiquotation_place_capture
  \<open> let mut x = lhs; \<epsilon>\<open>literal x\<close> = rhs; *x \<close>

end

section\<open>Compositional field places\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

text\<open>
The explicit place conversion admits a field chain whose base is a parenthesized
dereference and lowers it to the focused reference before update.
\<close>

adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr improvement_grouped_deref_field_place
  \<open> (*rp).inner.value = field_value \<close>

end

section\<open>Composable postfix expressions\<close>

no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

text\<open>
The parser treats propagation, fields, and methods as one left-associative
postfix tier.
\<close>

urust_expr improvement_path_postfix_chain
  \<open> Some(Path::Values[1_usize])?.cf1() \<close>

context fixes self :: postfix_outer
begin
urust_expr improvement_propagate_method
  \<open> self.optional?.to_value() \<close>
end

section\<open>Closure delimiter placement and parser-wide compositions\<close>

text\<open>
The parser gives closures one explicit delimiter-level argument category and
accepts it consistently at each covered delimiter position.
\<close>

definition improvement_apply_closure ::
    \<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
      (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> improvement_apply_closure closure \<equiv> closure 1 \<close>

definition improvement_apply_closure_first ::
    \<open>(nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
      nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> improvement_apply_closure_first closure value \<equiv> closure value \<close>

subsection\<open>Grouping, nesting, siblings, and invocation through a binding\<close>

urust_expr improvement_closure_group
  \<open> (|x| \<llangle>x :: nat\<rrangle>) \<close>

urust_expr improvement_closure_grouped_initializer
  \<open>
    let closure = (|x| \<llangle>x :: nat\<rrangle>);
    closure(\<llangle>1 :: nat\<rrangle>)
  \<close>

urust_expr improvement_closure_nested_parenthesized
  \<open>
    |outer|
      (|inner| \<llangle>(outer :: nat, inner :: bool)\<rrangle>)
  \<close>

urust_expr improvement_closure_siblings
  \<open>
    (|x| \<llangle>x :: nat\<rrangle>,
     |y| \<llangle>y :: bool\<rrangle>)
  \<close>

subsection\<open>Calls, tuples, arrays, macros, indexing, and arm bodies\<close>

urust_expr improvement_closure_single_call_argument
  \<open>
    improvement_apply_closure(
      |x| \<llangle>x :: nat\<rrangle>
    )
  \<close>

urust_expr improvement_closure_first_call_argument
  \<open>
    improvement_apply_closure_first(
      |x| \<llangle>x :: nat\<rrangle>,
      1
    )
  \<close>

urust_expr improvement_closure_first_tuple_element
  \<open>
    (|x| \<llangle>x :: nat\<rrangle>, \<llangle>True\<rrangle>)
  \<close>

urust_expr improvement_closure_array_elements
  \<open>
    [|x| \<llangle>x :: nat\<rrangle>,
     |x| \<llangle>x :: nat\<rrangle>]
  \<close>

urust_expr improvement_closure_macro_arguments
  \<open>
    vec![|x| \<llangle>x :: nat\<rrangle>,
         |x| \<llangle>x :: nat\<rrangle>]
  \<close>

datatype closure_index_fixture = ClosureIndexFixture

definition closure_index_impl ::
    \<open>closure_index_fixture \<Rightarrow>
      (nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body) \<Rightarrow>
      (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> closure_index_impl _ closure \<equiv> closure 1 \<close>

adhoc_overloading index_const \<rightleftharpoons> closure_index_impl

context fixes closure_index_value :: closure_index_fixture
begin

urust_expr improvement_closure_index_subscript
  \<open>
    closure_index_value[|x| \<llangle>x :: nat\<rrangle>]
  \<close>

end

no_adhoc_overloading index_const \<rightleftharpoons> closure_index_impl

urust_expr improvement_closure_grouped_arm_body
  \<open>
    match true {
      true \<Rightarrow> (|| \<llangle>1 :: nat\<rrangle>),
      false \<Rightarrow> (|| \<llangle>2 :: nat\<rrangle>)
    }
  \<close>

subsection\<open>Existing parser improvements composed with closures\<close>

urust_expr improvement_closure_line_comment
  \<open>
    |x| {
      // Closure comments use the production lexer state.
      \<llangle>x :: nat\<rrangle>
    }
  \<close>

urust_expr improvement_closure_empty_block
  \<open> || {} \<close>

urust_expr improvement_closure_call_trailing_comma
  \<open>
    closure_invoke_nat(
      1,
      |x| \<llangle>x :: nat\<rrangle>,
    )
  \<close>

urust_expr improvement_closure_array_trailing_comma
  \<open>
    [\<llangle>(\<lambda>x::nat. FunctionBody (literal x))\<rrangle>,
     |x| \<llangle>x :: nat\<rrangle>,]
  \<close>

urust_expr improvement_closure_ascii_arrow
  \<open>
    |value|
      match Some(value) {
        Some(result) => \<llangle>result :: nat\<rrangle>,
        None => 0
      }
  \<close>

urust_expr improvement_closure_glued_suffix
  \<open> || 1u32 \<close>

urust_expr improvement_closure_mixed_chain_in_block
  \<open>
    || {
      if false {
        0
      } else if let Some(value) = Some(1) {
        value
      } else {
        2
      }
    }
  \<close>

section\<open>Rust-compatible return expressions\<close>

text\<open>
Return is a low-precedence value expression whose operand and semicolon are independently
optional.
\<close>

urust_expr improvement_tail_return
  \<open> return \<close>

urust_expr improvement_tail_return_value
  \<open> return \<llangle>1 :: nat\<rrangle> \<close>

urust_expr improvement_guard_tail_return
  \<open>
    match_case Some(()) {
      Some(_) if return \<llangle>True\<rrangle> \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr improvement_guard_tail_return_unit
  \<open>
    match_case Some(()) {
      Some(_) if return \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr improvement_branch_returns
  \<open>
    if \<llangle>True\<rrangle> {
      return \<llangle>1 :: nat\<rrangle>
    } else {
      return \<llangle>2 :: nat\<rrangle>
    }
  \<close>

urust_expr improvement_return_initializer
  \<open>
    let result = return \<llangle>1 :: nat\<rrangle>;
    result
  \<close>

section\<open>Rust-aligned prefix-before-cast precedence\<close>

text\<open>
The grammar parses every prefix before a following cast.
\<close>

context
  fixes cast_prefix_word :: \<open>32 word\<close>
begin

urust_expr improvement_cast_before_not
  \<open> !cast_prefix_word as u8 \<close>

urust_expr improvement_cast_line_comment_before_target
  \<open>
    cast_prefix_word as // target width follows
      u16
  \<close>

end

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

context
  fixes cast_prefix_raw :: \<open>(unit, unit) gref\<close>
    and cast_prefix_ref :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
begin

urust_expr improvement_cast_multiline_pointer_target
  \<open>
    cast_prefix_raw
      as
      *
      mut
      u16
  \<close>

urust_expr improvement_cast_before_deref
  \<open> *cast_prefix_ref as u8 \<close>

urust_expr improvement_cast_line_comments_in_pointer_target
  \<open>
    cast_prefix_raw as * // pointer mutability follows
      mut // pointee width follows
      u16
  \<close>

end

chapter\<open>Intentional semantic corrections\<close>

section\<open>Checked-term corrections\<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

text\<open>
These sources exercise intentional checked-term corrections.
\<open>Parser_Pattern_ML_Tests.thy\<close> pins the associated term shapes.
\<close>

context fixes r :: rich_case
begin

urust_expr rich_or_guarded
  \<open> match r { RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> x, _ \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

urust_expr rich_or_three_guard_fallthrough
  \<open> match r { RMA(x) | RMB(x) | RMD(x) if False \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>, RMA(x) | RMB(x) | RMD(x) \<Rightarrow> x, RMC \<Rightarrow> \<llangle>0 :: 32 word\<rrangle> } \<close>

end

context fixes b :: bool
begin

urust_expr value_pat_source_guard
  \<open> match b { true if False \<Rightarrow> True, _ \<Rightarrow> False } \<close>

end

urust_expr value_pat_guard_order
  \<open> match \<llangle>VPP True (String.implode ''ok'')\<rrangle> {
      VPP(true, "ok") if True \<Rightarrow> True, _ \<Rightarrow> False } \<close>

urust_expr adv_range_guard
  \<open> match_case \<llangle>Some (6 :: nat)\<rrangle> { Some(5..=7) if True \<Rightarrow> \<llangle>1 :: nat\<rrangle>, Some(5..=7) \<Rightarrow> \<llangle>2 :: nat\<rrangle>, _ \<Rightarrow> \<llangle>3 :: nat\<rrangle> } \<close>

urust_expr adv_struct_nested
  \<open> match \<llangle>AdvNested (Some (3 :: nat)) [4, 5]\<rrangle> { AdvNested { adv_option: Some(x), adv_values: [y, .., z] } if True \<Rightarrow> z, _ \<Rightarrow> 0 } \<close>

urust_expr bind_match_guard_shadow
  \<open>
    let x = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if x > \<llangle>0 :: nat\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>

urust_expr bind_match_slice_shadow
  \<open>
    let head = \<llangle>0 :: nat\<rrangle>;
    let tail = \<llangle>0 :: nat\<rrangle>;
    match \<llangle>[1 :: nat, 2, 3]\<rrangle> {
      [head, .., tail] \<Rightarrow> { let _ = \<llangle>tail\<rrangle>; \<llangle>head\<rrangle> },
      _ \<Rightarrow> head
    }
  \<close>

urust_expr bind_match_or_shadow
  \<open>
    let x = \<llangle>0 :: 32 word\<rrangle>;
    match \<llangle>RMA (1 :: 32 word)\<rrangle> {
      RMA(x) | RMB(x) if x > \<llangle>0 :: 32 word\<rrangle> \<Rightarrow> \<llangle>x\<rrangle>,
      _ \<Rightarrow> x
    }
  \<close>

context fixes x :: nat and y :: bool
begin

urust_expr bind_hol_match_guard_shadow
  \<open>
    match Some(x) {
      Some(x) if x == \<llangle>x\<rrangle> \<Rightarrow> x,
      None \<Rightarrow> x
    }
  \<close>

end

urust_expr while_let_exhaustive_tnil
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let TNil = TNil {
      ()
    }
  \<close>

urust_expr while_let_exhaustive_option
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) | None =
      \<llangle>Some (1 :: nat)\<rrangle> {
      ()
    }
  \<close>

urust_expr while_let_nested_exhaustive_option
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let
      Some(Some(_) | None) | None =
      \<llangle>Some (None :: nat option)\<rrangle> {
      ()
    }
  \<close>

chapter\<open> Primitive-type path heads \<close>

section\<open> Primitive-type path heads \<close>

declare [[urust_verbosity = 0]]

definition primitive_head_u8_max :: \<open> 8 word \<close>
  where \<open> primitive_head_u8_max = 7 \<close>

definition primitive_head_u16_max :: \<open> 16 word \<close>
  where \<open> primitive_head_u16_max = 17 \<close>

definition primitive_head_u32_max :: \<open> 32 word \<close>
  where \<open> primitive_head_u32_max = 37 \<close>

definition primitive_head_u64_max :: \<open> 64 word \<close>
  where \<open> primitive_head_u64_max = 67 \<close>

definition primitive_head_usize_max :: \<open> 64 word \<close>
  where \<open> primitive_head_usize_max = 3 \<close>

definition primitive_head_i32_max :: \<open> 32 word \<close>
  where \<open> primitive_head_i32_max = 47 \<close>

definition primitive_head_i64_max :: \<open> 64 word \<close>
  where \<open> primitive_head_i64_max = 79 \<close>

definition primitive_head_u64_min :: \<open> 64 word \<close>
  where \<open> primitive_head_u64_min = 0 \<close>

definition primitive_head_flag :: bool
  where \<open> primitive_head_flag = True \<close>

definition primitive_head_option :: \<open> 64 word option \<close>
  where \<open> primitive_head_option = Some 11 \<close>

definition primitive_head_values :: \<open> 64 word list \<close>
  where \<open> primitive_head_values = [13, 17] \<close>

definition primitive_head_pair :: \<open> 64 word \<times> 64 word \<close>
  where \<open> primitive_head_pair = (19, 23) \<close>

datatype_record primitive_head_record =
  primitive_head_record_value :: \<open> 64 word \<close>

micro_rust_record primitive_head_record

definition primitive_head_record_constant :: primitive_head_record
  where \<open> primitive_head_record_constant = make_primitive_head_record 29 \<close>

definition primitive_head_zero ::
    \<open> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_zero = lift_fun0 0 \<close>

definition primitive_head_from ::
    \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_from = lift_fun1 id \<close>

definition primitive_head_combine ::
    \<open> 64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_combine = lift_fun2 (+) \<close>

definition primitive_head_bump ::
    \<open> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_bump = lift_fun1 (\<lambda>x. x + 1) \<close>

definition primitive_head_dual_literal :: \<open> 64 word \<close>
  where \<open> primitive_head_dual_literal = 31 \<close>

definition primitive_head_dual_call ::
    \<open> (unit, 64 word, unit, unit, unit) function_body \<close>
  where \<open> primitive_head_dual_call = lift_fun0 31 \<close>

definition primitive_head_ambiguous_left :: \<open> 64 word \<close>
  where \<open> primitive_head_ambiguous_left = 41 \<close>

definition primitive_head_ambiguous_right :: \<open> 64 word \<close>
  where \<open> primitive_head_ambiguous_right = 43 \<close>

datatype primitive_head_constructor_backend =
  PrimitiveHeadConstructor

micro_rust_notation (literal) primitive_head_u8_max ("u8::MAX")

micro_rust_notation (literal) primitive_head_u16_max ("u16::MAX")

micro_rust_notation (literal) primitive_head_u32_max ("u32::MAX")

micro_rust_notation (literal) primitive_head_u64_max ("u64::MAX")

micro_rust_notation (literal) primitive_head_usize_max ("usize::MAX")

micro_rust_notation (literal) primitive_head_i32_max ("i32::MAX")

micro_rust_notation (literal) primitive_head_i64_max ("i64::MAX")

micro_rust_notation (literal) primitive_head_u64_min ("u64::MIN")

micro_rust_notation (literal) primitive_head_flag ("u64::FLAG")

micro_rust_notation (literal) primitive_head_option ("u64::OPTION")

micro_rust_notation (literal) primitive_head_values ("u64::VALUES")

micro_rust_notation (literal) primitive_head_pair ("u64::PAIR")

micro_rust_notation (literal)
  primitive_head_record_constant ("u64::RECORD")

urust_notation (literal)
  primitive_head_u64_max ("u64::Nested::MAX")

micro_rust_notation (call) primitive_head_zero ("u64::zero")

micro_rust_notation (call) primitive_head_from ("u64::from")

micro_rust_notation (call) primitive_head_combine ("u64::combine")

micro_rust_notation (call)
  primitive_head_from ("u64::from::<PrimitiveParam>")

micro_rust_notation (call) primitive_head_bump ("primitive_head_bump")

micro_rust_notation (literal)
  primitive_head_dual_literal ("u64::DUAL")

micro_rust_notation (call)
  primitive_head_dual_call ("u64::DUAL")

micro_rust_notation (literal)
  primitive_head_ambiguous_left ("u64::AMBIGUOUS")

micro_rust_notation (literal)
  primitive_head_ambiguous_right ("u64::AMBIGUOUS")

micro_rust_notation (literal)
  PrimitiveHeadConstructor ("u64::CONSTRUCTOR_VALUE")

micro_rust_notation (literal)
  primitive_head_u8_max ("PrimitiveCompat::U8Max")

micro_rust_notation (literal)
  primitive_head_u16_max ("PrimitiveCompat::U16Max")

micro_rust_notation (literal)
  primitive_head_u32_max ("PrimitiveCompat::U32Max")

micro_rust_notation (literal)
  primitive_head_u64_max ("PrimitiveCompat::U64Max")

micro_rust_notation (literal)
  primitive_head_usize_max ("PrimitiveCompat::UsizeMax")

micro_rust_notation (literal)
  primitive_head_i32_max ("PrimitiveCompat::I32Max")

micro_rust_notation (literal)
  primitive_head_i64_max ("PrimitiveCompat::I64Max")

micro_rust_notation (literal)
  primitive_head_u64_min ("PrimitiveCompat::U64Min")

micro_rust_notation (call)
  primitive_head_zero ("PrimitiveCompat::zero")

micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert")

micro_rust_notation (call)
  primitive_head_combine ("PrimitiveCompat::combine")

micro_rust_notation (call)
  primitive_head_from ("PrimitiveCompat::convert::<PrimitiveParam>")

micro_rust_notation (literal)
  primitive_head_dual_literal ("PrimitiveCompat::DUAL")

micro_rust_notation (call)
  primitive_head_dual_call ("PrimitiveCompat::DUAL")

micro_rust_notation (literal) primitive_head_u64_max ("u64_MAX")

micro_rust_notation (literal) primitive_head_u64_max ("u64x::MAX")

micro_rust_notation (literal) primitive_head_u64_max ("u64x'::MAX")

micro_rust_notation (literal) primitive_head_u64_max ("u128::MAX")

urust_type_alias \<open> type PrimitivePathAlias = u64; \<close>

subsection\<open> Exact literal and call resolution \<close>

urust_expr primitive_path_u8 \<open> u8::MAX \<close>

urust_expr primitive_path_u8_compat
  \<open> PrimitiveCompat::U8Max \<close>

lemma primitive_path_u8_equal:
  \<open> primitive_path_u8 = primitive_path_u8_compat \<close>
  unfolding primitive_path_u8_def primitive_path_u8_compat_def
  by (rule refl)

urust_expr primitive_path_u16 \<open> u16::MAX \<close>

urust_expr primitive_path_u16_compat
  \<open> PrimitiveCompat::U16Max \<close>

lemma primitive_path_u16_equal:
  \<open> primitive_path_u16 = primitive_path_u16_compat \<close>
  unfolding primitive_path_u16_def primitive_path_u16_compat_def
  by (rule refl)

urust_expr primitive_path_u32 \<open> u32::MAX \<close>

urust_expr primitive_path_u32_compat
  \<open> PrimitiveCompat::U32Max \<close>

lemma primitive_path_u32_equal:
  \<open> primitive_path_u32 = primitive_path_u32_compat \<close>
  unfolding primitive_path_u32_def primitive_path_u32_compat_def
  by (rule refl)

urust_expr primitive_path_u64 \<open> u64::MAX \<close>

urust_expr primitive_path_u64_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_u64_equal:
  \<open> primitive_path_u64 = primitive_path_u64_compat \<close>
  unfolding primitive_path_u64_def primitive_path_u64_compat_def
  by (rule refl)

urust_expr primitive_path_usize \<open> usize::MAX \<close>

urust_expr primitive_path_usize_compat
  \<open> PrimitiveCompat::UsizeMax \<close>

lemma primitive_path_usize_equal:
  \<open> primitive_path_usize = primitive_path_usize_compat \<close>
  unfolding primitive_path_usize_def primitive_path_usize_compat_def
  by (rule refl)

urust_expr primitive_path_i32 \<open> i32::MAX \<close>

urust_expr primitive_path_i32_compat
  \<open> PrimitiveCompat::I32Max \<close>

lemma primitive_path_i32_equal:
  \<open> primitive_path_i32 = primitive_path_i32_compat \<close>
  unfolding primitive_path_i32_def primitive_path_i32_compat_def
  by (rule refl)

urust_expr primitive_path_i64 \<open> i64::MAX \<close>

urust_expr primitive_path_i64_compat
  \<open> PrimitiveCompat::I64Max \<close>

lemma primitive_path_i64_equal:
  \<open> primitive_path_i64 = primitive_path_i64_compat \<close>
  unfolding primitive_path_i64_def primitive_path_i64_compat_def
  by (rule refl)

urust_expr primitive_path_call_zero \<open> u64::zero() \<close>

urust_expr primitive_path_call_zero_compat
  \<open> PrimitiveCompat::zero() \<close>

lemma primitive_path_call_zero_equal:
  \<open> primitive_path_call_zero = primitive_path_call_zero_compat \<close>
  unfolding primitive_path_call_zero_def primitive_path_call_zero_compat_def
  by (rule refl)

urust_expr primitive_path_call_one \<open> u64::from(5u64) \<close>

urust_expr primitive_path_call_one_compat
  \<open> PrimitiveCompat::convert(5_u64) \<close>

lemma primitive_path_call_one_equal:
  \<open> primitive_path_call_one = primitive_path_call_one_compat \<close>
  unfolding primitive_path_call_one_def primitive_path_call_one_compat_def
  by (rule refl)

urust_expr primitive_path_call_multiple
  \<open> u64::combine(5u64, 7u64) \<close>

urust_expr primitive_path_call_multiple_compat
  \<open> PrimitiveCompat::combine(5_u64, 7_u64) \<close>

lemma primitive_path_call_multiple_equal:
  \<open> primitive_path_call_multiple = primitive_path_call_multiple_compat \<close>
  unfolding primitive_path_call_multiple_def primitive_path_call_multiple_compat_def
  by (rule refl)

urust_expr primitive_path_call_turbofish
  \<open> u64::from::<PrimitiveParam>(5u64) \<close>

urust_expr primitive_path_call_turbofish_compat
  \<open> PrimitiveCompat::convert::<PrimitiveParam>(5_u64) \<close>

lemma primitive_path_call_turbofish_equal:
  \<open> primitive_path_call_turbofish = primitive_path_call_turbofish_compat \<close>
  unfolding primitive_path_call_turbofish_def primitive_path_call_turbofish_compat_def
  by (rule refl)

urust_expr primitive_path_dual_literal \<open> u64::DUAL \<close>

urust_expr primitive_path_dual_literal_compat
  \<open> PrimitiveCompat::DUAL \<close>

lemma primitive_path_dual_literal_equal:
  \<open> primitive_path_dual_literal = primitive_path_dual_literal_compat \<close>
  unfolding primitive_path_dual_literal_def primitive_path_dual_literal_compat_def
  by (rule refl)

urust_expr primitive_path_dual_call \<open> u64::DUAL() \<close>

urust_expr primitive_path_dual_call_compat
  \<open> PrimitiveCompat::DUAL() \<close>

lemma primitive_path_dual_call_equal:
  \<open> primitive_path_dual_call = primitive_path_dual_call_compat \<close>
  unfolding primitive_path_dual_call_def primitive_path_dual_call_compat_def
  by (rule refl)

subsection\<open> Layout and lexical boundaries \<close>

urust_expr primitive_path_spaces \<open> u64 :: MAX \<close>

urust_expr primitive_path_spaces_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_spaces_equal:
  \<open> primitive_path_spaces = primitive_path_spaces_compat \<close>
  unfolding primitive_path_spaces_def primitive_path_spaces_compat_def
  by (rule refl)

urust_expr primitive_path_newlines
  \<open>
    u64
      ::
    MAX
  \<close>

urust_expr primitive_path_newlines_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_newlines_equal:
  \<open> primitive_path_newlines = primitive_path_newlines_compat \<close>
  unfolding primitive_path_newlines_def primitive_path_newlines_compat_def
  by (rule refl)

urust_expr primitive_path_line_comment
  \<open>
    u64 // before separator
      :: // before item
    MAX
  \<close>

urust_expr primitive_path_line_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_line_comment_equal:
  \<open> primitive_path_line_comment = primitive_path_line_comment_compat \<close>
  unfolding primitive_path_line_comment_def primitive_path_line_comment_compat_def
  by (rule refl)

urust_expr primitive_path_block_comment
  \<open> u64 /* outer /* nested */ comment */ :: MAX \<close>

urust_expr primitive_path_block_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_block_comment_equal:
  \<open> primitive_path_block_comment = primitive_path_block_comment_compat \<close>
  unfolding primitive_path_block_comment_def primitive_path_block_comment_compat_def
  by (rule refl)

urust_expr primitive_path_formal_comment
  \<open>
    u64
      \<comment> \<open> formal layout with \<^term>\<open>True\<close>\<close>
      ::
      MAX
  \<close>

urust_expr primitive_path_formal_comment_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_formal_comment_equal:
  \<open> primitive_path_formal_comment = primitive_path_formal_comment_compat \<close>
  unfolding primitive_path_formal_comment_def primitive_path_formal_comment_compat_def
  by (rule refl)

urust_expr primitive_path_identifier_boundary \<open> u64_MAX \<close>

urust_expr primitive_path_identifier_boundary_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_identifier_boundary_equal:
  \<open> primitive_path_identifier_boundary = primitive_path_identifier_boundary_compat \<close>
  unfolding primitive_path_identifier_boundary_def primitive_path_identifier_boundary_compat_def
  by (rule refl)

urust_expr primitive_path_identifier_prefix \<open> u64x::MAX \<close>

urust_expr primitive_path_identifier_prefix_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_identifier_prefix_equal:
  \<open> primitive_path_identifier_prefix = primitive_path_identifier_prefix_compat \<close>
  unfolding primitive_path_identifier_prefix_def primitive_path_identifier_prefix_compat_def
  by (rule refl)

urust_expr primitive_path_apostrophe \<open> u64x'::MAX \<close>

urust_expr primitive_path_apostrophe_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_apostrophe_equal:
  \<open> primitive_path_apostrophe = primitive_path_apostrophe_compat \<close>
  unfolding primitive_path_apostrophe_def primitive_path_apostrophe_compat_def
  by (rule refl)

urust_expr primitive_path_unsupported_width \<open> u128::MAX \<close>

urust_expr primitive_path_unsupported_width_compat
  \<open> PrimitiveCompat::U64Max \<close>

lemma primitive_path_unsupported_width_equal:
  \<open> primitive_path_unsupported_width = primitive_path_unsupported_width_compat \<close>
  unfolding primitive_path_unsupported_width_def primitive_path_unsupported_width_compat_def
  by (rule refl)

urust_expr_rejects \<open> u64 \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> u64:: \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> u64::::MAX \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> u64:::::MAX \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> u64::u8 \<close> \<open> syntax error \<close>

urust_expr_rejects \<open> Module::u64::MAX \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::<PrimitiveParam>::MAX \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::from::<>() \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::from::<PrimitiveParam,>() \<close> \<open> syntax error \<close>

subsection\<open> Expression composition \<close>

urust_expr primitive_path_prefix \<open> !u64::MAX \<close>

urust_expr primitive_path_dereference \<open> *u64::MAX \<close>

urust_expr primitive_path_cast_u8 \<open> u64::MIN as u8 \<close>

urust_expr primitive_path_cast_u16 \<open> u64::MIN as u16 \<close>

urust_expr primitive_path_cast_u32 \<open> u64::MIN as u32 \<close>

urust_expr primitive_path_cast_u64 \<open> u8::MAX as u64 \<close>

urust_expr primitive_path_cast_usize \<open> u64::MIN as usize \<close>

urust_expr primitive_path_cast_i32 \<open> u64::MIN as i32 \<close>

urust_expr primitive_path_cast_i64 \<open> u64::MIN as i64 \<close>

urust_expr primitive_path_named_cast_alias
  \<open> u8::MAX as PrimitivePathAlias \<close>

urust_expr primitive_path_named_cast_alias_compat
  \<open> PrimitiveCompat::U8Max as u64 \<close>

lemma primitive_path_named_cast_alias_equal:
  \<open> primitive_path_named_cast_alias = primitive_path_named_cast_alias_compat \<close>
  unfolding primitive_path_named_cast_alias_def primitive_path_named_cast_alias_compat_def
  by (rule refl)

urust_expr primitive_path_binary \<open> u64::MAX + 1u64 \<close>

urust_expr primitive_path_comparison \<open> u64::MIN < u64::MAX \<close>

urust_expr primitive_path_range \<open> u64::MIN..u64::MAX \<close>

urust_expr primitive_path_group \<open> (u64::MAX) \<close>

urust_expr primitive_path_block \<open> { u64::MAX } \<close>

urust_expr primitive_path_unsafe \<open> unsafe { u64::MAX } \<close>

urust_expr primitive_path_propagate \<open> u64::OPTION? \<close>

urust_expr primitive_path_field
  \<open> u64::RECORD.primitive_head_record_value \<close>

urust_expr primitive_path_method
  \<open> u64::MAX.primitive_head_bump() \<close>

urust_expr primitive_path_index \<open> u64::VALUES[0_usize] \<close>

urust_expr primitive_path_projection \<open> u64::PAIR.0 \<close>

urust_expr primitive_path_array \<open> [u64::MIN, u64::MAX] \<close>

urust_expr primitive_path_repeat
  \<open> [u64::MAX; usize::MAX] \<close>

urust_expr primitive_path_repeat_arithmetic
  \<open> [u64::MAX; usize::MAX + 1] \<close>

urust_expr primitive_path_macro_argument
  \<open> assert!(u64::MIN < u64::MAX) \<close>

urust_expr primitive_path_let
  \<open> let value = u64::MAX; value \<close>

urust_expr primitive_path_let_mut
  \<open> let mut value = u64::MAX; *value \<close>

urust_expr primitive_path_const
  \<open> const value = u64::MAX; value \<close>

urust_expr primitive_path_sequence
  \<open> u64::MIN; u64::MAX \<close>

urust_expr primitive_path_closure
  \<open> |value| value + u64::MAX \<close>

urust_expr primitive_path_return
  \<open> return u64::MAX \<close>

urust_expr primitive_path_if
  \<open> if u64::FLAG { u64::MAX } else { u64::MIN } \<close>

urust_expr primitive_path_if_let
  \<open>
    if let Some(value) = u64::OPTION {
      value
    } else {
      u64::MIN
    }
  \<close>

urust_expr primitive_path_if_let_constant
  \<open>
    if let u64::MAX = u64::MAX {
      true
    } else {
      false
    }
  \<close>

urust_expr primitive_path_for
  \<open> for value in u64::VALUES { let _ = value; () } \<close>

urust_expr primitive_path_while
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while (u64::FLAG) { () }
  \<close>

urust_expr primitive_path_loop
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    loop { let value = u64::MAX; let _ = value; () }
  \<close>

urust_expr primitive_path_while_let
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while let Some(value) = u64::OPTION {
      let _ = value;
      ()
    }
  \<close>

urust_expr primitive_path_while_let_constant
  \<open>
    #[fuel(\<epsilon>\<open> 1 :: nat \<close>)]
    while let u64::MAX = u64::MAX { () }
  \<close>

urust_expr primitive_path_match
  \<open>
    match u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_case
  \<open>
    match_case Some(u64::MAX) {
      Some(u64::MAX) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_match_switch
  \<open>
    match_switch u64::MAX {
      u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_semicolon_free_control
  \<open>
    if u64::FLAG { () }
    u64::MAX
  \<close>

subsection\<open> Pattern roles and place rejection \<close>

urust_expr primitive_path_tuple_pattern
  \<open>
    match_case (u64::MAX, Some(u64::MAX)) {
      (u64::MAX, Some(u64::MAX)) \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_slice_pattern
  \<open>
    match_case [u64::MAX, u64::MIN] {
      [u64::MAX, _] \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_range_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN..=u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_alias_pattern
  \<open>
    match_case u64::MAX {
      whole @ u64::MAX \<Rightarrow> whole,
      _ \<Rightarrow> u64::MIN
    }
  \<close>

urust_expr primitive_path_or_pattern
  \<open>
    match_case u64::MAX {
      u64::MIN | u64::MAX \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_guarded_pattern
  \<open>
    match_case u64::MAX {
      u64::MAX if u64::FLAG \<Rightarrow> true,
      _ \<Rightarrow> false
    }
  \<close>

urust_expr primitive_path_matches_pattern
  \<open> matches!(u64::MAX, u64::MAX) \<close>

urust_expr_rejects
  \<open> let u64::MAX = u64::MAX; () \<close>
  \<open> unsupported or refutable pattern in an irrefutable (let/const) binder position \<close>

urust_expr_rejects
  \<open> for u64::MAX in u64::VALUES { () } \<close>
  \<open> unsupported or refutable pattern in a `for` binder position \<close>

urust_expr_rejects
  \<open> |u64::MAX| () \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX = u64::MIN \<close>
  \<open> primitive associated-item path is not an assignment target \<close>

urust_expr_rejects
  \<open> u64::MAX { field: u64::MIN } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> match_case u64::MAX { u64::MAX { field: _ } \<Rightarrow> true } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> PrimitiveRecord { u64: u64::MAX } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> u64::MAX.u64() \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> &u64::MAX \<close> \<open> no backend matches the use-site type \<close>

urust_expr_rejects
  \<open> *u64::MAX + true \<close> \<open> Unresolved adhoc overloading \<close>

subsection\<open> Exact-registration failures \<close>

urust_expr_rejects
  \<open> u64::MISSING \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MISSING() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::zero \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::MAX() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::AMBIGUOUS \<close>
  \<open> Ambiguous uRust notation \<close>

urust_expr_rejects
  \<open> u64::MAX as u64::MAX \<close> \<open> syntax error \<close>

urust_expr primitive_path_recovery_after_rejections
  \<open> u64::MAX \<close>

subsection\<open> Exact generic paths and role boundaries \<close>

micro_rust_notation (call) primitive_head_zero ("u8::zero")

micro_rust_notation (call) primitive_head_zero ("u16::zero")

micro_rust_notation (call) primitive_head_zero ("u32::zero")

micro_rust_notation (call) primitive_head_zero ("usize::zero")

micro_rust_notation (call) primitive_head_zero ("i32::zero")

micro_rust_notation (call) primitive_head_zero ("i64::zero")

urust_expr primitive_path_all_call_heads
  \<open>
    (u8::zero(), u16::zero(), u32::zero(), u64::zero(),
     usize::zero(), i32::zero(), i64::zero())
  \<close>

urust_expr primitive_path_all_call_heads_compat
  \<open>
    (PrimitiveCompat::zero(), PrimitiveCompat::zero(), PrimitiveCompat::zero(),
     PrimitiveCompat::zero(), PrimitiveCompat::zero(), PrimitiveCompat::zero(),
     PrimitiveCompat::zero())
  \<close>

lemma primitive_path_all_call_heads_equal:
  \<open> primitive_path_all_call_heads = primitive_path_all_call_heads_compat \<close>
  unfolding primitive_path_all_call_heads_def primitive_path_all_call_heads_compat_def
  by (rule refl)

micro_rust_notation (literal)
  primitive_head_u64_max ("u64::Nested::<PrimitiveParam>::MAX")

micro_rust_notation (call)
  primitive_head_from ("u64::Nested::<PrimitiveParam>::from::<PrimitiveParam>")

urust_expr primitive_path_exact_generic_literal
  \<open> u64::Nested::<PrimitiveParam>::MAX \<close>

lemma primitive_path_exact_generic_literal_equal:
  \<open> primitive_path_exact_generic_literal = primitive_path_u64 \<close>
  unfolding primitive_path_exact_generic_literal_def primitive_path_u64_def
  by (rule refl)

urust_expr primitive_path_exact_generic_call
  \<open> u64::Nested::<PrimitiveParam>::from::<PrimitiveParam>(5u64) \<close>

lemma primitive_path_exact_generic_call_equal:
  \<open> primitive_path_exact_generic_call = primitive_path_call_one \<close>
  unfolding primitive_path_exact_generic_call_def primitive_path_call_one_def
  by (rule refl)

urust_expr_rejects
  \<open> u64::from::<UnregisteredParam>(5u64) \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

urust_expr_rejects
  \<open> u64::MAX::<PrimitiveParam> \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> u64::Nested::<UnregisteredParam>::MAX \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

context
begin

micro_rust_notation (field) lens_id ("u64::FIELD_ONLY")

urust_expr_rejects
  \<open> u64::FIELD_ONLY \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>
urust_expr_rejects
  \<open> u64::FIELD_ONLY() \<close>
  \<open> requires an exact micro_rust_notation (call) declaration \<close>

end

urust_expr_rejects
  \<open> u64::MAX!() \<close> \<open> syntax error \<close>

urust_expr_rejects
  \<open> match u64::MAX { u64::MAX() => true, _ => false } \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> match u64::MAX { u64::MISSING => true, _ => false } \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

urust_expr_rejects
  \<open> [u64::MAX; usize::MISSING] \<close>
  \<open> requires an exact micro_rust_notation (literal) declaration \<close>

subsection\<open> Contextual repeat lengths with primitive operands \<close>

context
  fixes count :: \<open> 64 word \<close>
begin

micro_rust_notation (literal) count ("usize::CONTEXT_COUNT")

urust_expr primitive_path_context_repeat
  \<open> [u64::MAX; count] \<close>

urust_expr primitive_path_context_repeat_registered
  \<open> [u64::MAX; usize::CONTEXT_COUNT] \<close>

lemma primitive_path_context_repeat_equal:
  \<open> primitive_path_context_repeat = primitive_path_context_repeat_registered \<close>
  unfolding primitive_path_context_repeat_def primitive_path_context_repeat_registered_def
  by (rule refl)

urust_expr primitive_path_context_inline_alias
  \<open> [const { u8::MAX as PrimitivePathAlias }; usize::CONTEXT_COUNT] \<close>

urust_expr primitive_path_context_inline_compat
  \<open> [const { PrimitiveCompat::U8Max as u64 }; count] \<close>

lemma primitive_path_context_inline_alias_equal:
  \<open> primitive_path_context_inline_alias = primitive_path_context_inline_compat \<close>
  unfolding primitive_path_context_inline_alias_def primitive_path_context_inline_compat_def
  by (rule refl)

urust_expr_rejects
  \<open> let count = 2usize; [u64::MAX; count] \<close>
  \<open> cannot use lexical local \<close>

end

chapter\<open>Parser facade\<close>

section\<open> Parser facade smoke test \<close>

declare [[urust_verbosity = 2]]

urust_expr smoke_num  \<open> 42 \<close>

urust_expr smoke_sfx  \<open> 1_u32 \<close>

urust_expr smoke_unit \<open> () \<close>

thm smoke_num_def smoke_sfx_def smoke_unit_def

chapter\<open>Typed expression and shared command API\<close>

section\<open> Typed declaration surface \<close>

urust_expr typed_closed ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>42 :: nat\<rrangle> \<close>

urust_expr typed_contextual ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_expr typed_heterogeneous ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat \<times> bool, unit, unit, unit, unit) expression\<close>
  (number, flag)
  \<open> \<llangle>(number, flag)\<rrangle> \<close>

urust_expr typed_higher_order ::
  \<open>(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit, unit) expression\<close>
  (f, item)
  \<open> \<llangle>f item\<rrangle> \<close>

urust_expr typed_polymorphic ::
  \<open>'a \<Rightarrow> ('s, 'a, 'r, 'abort, 'i, 'o) expression\<close>
  (item)
  \<open> item \<close>

urust_expr typed_sort_constrained ::
  \<open>'a::len word \<Rightarrow>
    ('s, 'a word, 'r, 'abort, 'i, 'o) expression\<close>
  (item)
  \<open> item \<close>

urust_expr typed_placeholders ::
  \<open>_ \<Rightarrow> (_, _, _, _, _, _) expression\<close>
  (item)
  \<open> item \<close>

text\<open>
A declaration ending in \<open>function_body\<close> selects function elaboration through the same
\<open>urust_expr\<close> command and therefore wraps the checked body exactly once.
\<close>

urust_expr typed_function_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr [application_def, attrs = [micro_rust_simps]]
  typed_application_expression ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, nat \<times> bool, unit, unit, unit, unit) expression\<close>
  (number, flag)
  \<open> \<llangle>(number, flag)\<rrangle> \<close>

urust_expr [application_def]
  typed_application_implicit_parameter
  (item)
  \<open> \<llangle>(item :: nat) + ambient_adjustment\<rrangle> \<close>

urust_expr typed_zero_expression_default ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

urust_expr [application_def] typed_zero_expression_application ::
  \<open>(unit, nat, unit, unit, unit, unit) expression\<close>
  \<open> \<llangle>7 :: nat\<rrangle> \<close>

text\<open>
Parenthesized expression parameters use Isabelle liberal names. Minor keywords such as
\<open>for\<close> are available unquoted, while major command keywords must be string-quoted because
command-span parsing happens before the declaration parser.

The function counterparts live in \<open>Parser_Function_Examples\<close>. The artifact checks in
\<open>Parser_Syntax_ML_Tests\<close> also inspect those imported declarations: lexical parameters
shadow registered values and direct call heads, methods retain registration-first resolution, and
independent signature holes infer through typed lexical fixes. In particular, the parameter named
\<open>zip\<close> shadows HOL \<open>List.zip\<close>.
\<close>

urust_expr [attrs = [micro_rust_simps]]
  attributed_expression ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr [attrs = []]
  empty_attributes_expression ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr parenthesized_minor_keyword_expression ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (for)
  \<open> () \<close>

text\<open>
A declaration wildcard consumes one argument type and contributes one anonymous abstraction without
entering lexical name resolution. Single, repeated, and mixed wildcard slots are accepted by both
commands; named slots retain their ordinary source-order scope.
\<close>

urust_expr wildcard_expression_single ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (_)
  \<open> () \<close>

urust_expr wildcard_expression_mixed ::
  \<open>nat \<Rightarrow> bool \<Rightarrow> 32 word \<Rightarrow>
    (unit, bool, unit, unit, unit, unit) expression\<close>
  (_, kept, _)
  \<open> kept \<close>

urust_expr  wildcard_expression_inferred
  (_)
  \<open> () \<close>

urust_expr [application_def] wildcard_expression_application ::
  \<open>nat \<Rightarrow> (unit, unit, unit, unit, unit, unit) expression\<close>
  (_)
  \<open> () \<close>

urust_expr [abbrev] wildcard_expression_abbreviation ::
  \<open>nat \<Rightarrow> bool \<Rightarrow>
    (unit, bool, unit, unit, unit, unit) expression\<close>
  (_, kept)
  \<open> kept \<close>

section\<open> Source-spelled binder names \<close>

text\<open>
Lexical locals keep distinct internal Free identities during elaboration, but direct abstractions
carry their source spellings. Application definitions turn those spellings into left-hand-side
arguments: a spelling that is not an Isabelle identifier is desymbolized, and one that clashes with
a context fix or the defined constant is renamed. Generated case subjects keep administrative names.
\<close>

urust_expr [application_def] self_named_application ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (self_named_application)
  \<open> self_named_application \<close>

urust_expr source_named_binders
  (input)
  \<open> let doubled = \<llangle>Some (input :: nat)\<rrangle>; match doubled { Some(found) \<Rightarrow> \<llangle>found\<rrangle>, None \<Rightarrow> \<llangle>0 :: nat\<rrangle> } \<close>

urust_expr source_named_closure
  \<open> |first, second| \<llangle>(first :: nat, second :: bool)\<rrangle> \<close>

urust_expr source_named_alias
  \<open> match \<llangle>Some (7 :: nat)\<rrangle> { whole @ Some(_) \<Rightarrow> whole, _ \<Rightarrow> None } \<close>

urust_expr source_named_shadowing
  \<open> let x = 1_u64; let x = x + 1_u64; x \<close>

section\<open> Anonymous declarations \<close>

text\<open>
The dummy declaration name elaborates and checks a term without installing a constant, definition,
abbreviation, theorem, or code equation.
\<close>

urust_expr [application_def] _ ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> item \<close>

urust_expr [abbrev = true] _
  \<open> () \<close>

section\<open> Definitions, abbreviations, flags, and locales \<close>

urust_expr
  [verbosity = 0, abbrev = false]
  typed_flags_000 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, verbosity = 0]
  typed_flags_001 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 1, abbrev = false]
  typed_flags_010 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev = true, verbosity = 1]
  typed_flags_011 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 0, abbrev = false]
  typed_flags_100 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, verbosity = 0]
  typed_flags_101 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 2, abbrev = false]
  typed_flags_110 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [verbosity = 2, abbrev = true]
  typed_flags_111 ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> () \<close>

urust_expr
  [abbrev, verbosity = 2]
  typed_function_abbrev_common ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  (item)
  \<open> item \<close>

urust_expr typed_parser_only ::
  \<open>32 word \<Rightarrow>
    (unit, 32 word, unit, unit, unit, unit) expression\<close>
  (operand)
  \<open> operand + 1u32 \<close>

locale typed_expression_locale =
  fixes offset :: nat
begin

urust_expr
  [abbrev]
  typed_local_add ::
  \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit, unit) expression\<close>
  (item)
  \<open> \<llangle>item + offset\<rrangle> \<close>

end

section\<open> Pretty-printer roundtrip checking \<close>

urust_expr [pp_test = false] pp_expr_disabled
  (item)
  \<open> let value = \<llangle>item :: nat\<rrangle>; (value) \<close>

urust_expr [pp_test] pp_expr_enabled
  (item)
  \<open> let value = \<llangle>item :: nat\<rrangle>; (value) \<close>

lemma pp_expr_enabled_same:
  \<open>pp_expr_enabled = pp_expr_disabled\<close>
  unfolding pp_expr_enabled_def pp_expr_disabled_def
  by (rule refl)

section\<open> Standard code equations \<close>

urust_expr regression_code_literal
  \<open> 7_u32 \<close>

urust_expr regression_code_unit
  \<open> () \<close>

urust_expr regression_code_yield
  \<open> \<y>\<i>\<e>\<l>\<d> \<close>

urust_expr regression_code_primitive_log
  \<open> \<l>\<o>\<g> \<llangle>Info\<rrangle> \<llangle>[]\<rrangle> \<close>

urust_expr regression_code_log_data
  \<open> l\<llangle>True\<rrangle> \<close>

chapter\<open> Grammar boundaries \<close>

section\<open>Expression precedence\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

context
  fixes prefix_ref :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  fixes prefix_bool_ref :: \<open>(unit, unit, bool) Global_Store.ref\<close>
begin

urust_expr grammar_deref_before_cast
  \<open> *prefix_ref as u8 \<close>

urust_expr grammar_not_deref
  \<open> !*prefix_bool_ref \<close>

end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture

urust_expr grammar_if_left_operand
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
  \<close>

urust_expr grammar_match_left_operand
  \<open>
    match true {
      true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
      false \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
    } + \<llangle>3 :: 32 word\<rrangle>
  \<close>

urust_expr grammar_semicolon_free_if_statement
  \<open> if true { () } else { () } () \<close>

urust_expr_rejects
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    (if true { \<llangle>1 :: 32 word\<rrangle> }
     else { \<llangle>2 :: 32 word\<rrangle> })
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

section\<open>Match-arm separators\<close>

text\<open>
A direct with-block arm may omit its comma when the following pattern has an unambiguous first
token. Top-level borrow and slice patterns still require a comma because \<open>&\<close> and \<open>[\<close>
can continue the preceding body as binary-and or indexing. The AST audit below checks the complete
restricted-start pattern family, both explicit-comma cases, rejection without the comma, and parser
recovery.
\<close>

urust_expr  grammar_direct_with_block_arm
  \<open>
    match true {
      true \<Rightarrow> if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> (if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> })
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> return \<llangle>1 :: nat\<rrangle>;,
      false \<Rightarrow> return \<llangle>2 :: nat\<rrangle>;
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> return;,
      false \<Rightarrow> return;
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> if true { () } else { () }
      false \<Rightarrow> return;
    }
  \<close>
  \<open> syntax error \<close>

text\<open>
Direct return arms are expressions: commas separate them, the final comma is optional, and
statement semicolons belong inside braces. Complete guard bodies retain ordinary return statements.
\<close>

urust_expr grammar_valued_return_arm_commas ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match true {
      true \<Rightarrow> return \<llangle>1 :: nat\<rrangle>,
      false \<Rightarrow> return \<llangle>2 :: nat\<rrangle>,
    }
  \<close>

urust_expr grammar_operandless_return_arm_commas ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    match true {
      true \<Rightarrow> return,
      false \<Rightarrow> return,
    }
  \<close>

urust_expr grammar_valued_return_arm_blocks ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match true {
      true \<Rightarrow> { return \<llangle>1 :: nat\<rrangle>; },
      false \<Rightarrow> { return \<llangle>2 :: nat\<rrangle>; }
    }
  \<close>

urust_expr grammar_operandless_return_arm_blocks ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    match true {
      true \<Rightarrow> { return; },
      false \<Rightarrow> { return; }
    }
  \<close>

lemma grammar_valued_return_arm_equality:
  \<open>grammar_valued_return_arm_commas = grammar_valued_return_arm_blocks\<close>
  unfolding grammar_valued_return_arm_commas_def grammar_valued_return_arm_blocks_def
  by (rule refl)

lemma grammar_operandless_return_arm_equality:
  \<open>grammar_operandless_return_arm_commas = grammar_operandless_return_arm_blocks\<close>
  unfolding grammar_operandless_return_arm_commas_def grammar_operandless_return_arm_blocks_def
  by (rule refl)

urust_expr grammar_case_return_arm_commas ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match_case Some(\<llangle>1 :: nat\<rrangle>) {
      Some(value) if true \<Rightarrow> return value,
      _ \<Rightarrow> return \<llangle>0 :: nat\<rrangle>
    }
  \<close>

urust_expr grammar_case_return_arm_blocks ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match_case Some(\<llangle>1 :: nat\<rrangle>) {
      Some(value) if true \<Rightarrow> { return value; },
      _ \<Rightarrow> { return \<llangle>0 :: nat\<rrangle>; },
    }
  \<close>

lemma grammar_case_return_arm_equality:
  \<open>grammar_case_return_arm_commas = grammar_case_return_arm_blocks\<close>
  unfolding grammar_case_return_arm_commas_def grammar_case_return_arm_blocks_def
  by (rule refl)

urust_expr grammar_switch_return_arm_commas ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> return, _ \<Rightarrow> return } \<close>

urust_expr grammar_switch_return_arm_blocks ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open> match_switch \<llangle>0 :: nat\<rrangle> { 0 \<Rightarrow> { return; }, _ \<Rightarrow> { return; }, } \<close>

lemma grammar_switch_return_arm_equality:
  \<open>grammar_switch_return_arm_commas = grammar_switch_return_arm_blocks\<close>
  unfolding grammar_switch_return_arm_commas_def grammar_switch_return_arm_blocks_def
  by (rule refl)

urust_expr grammar_case_operandless_return_arm_commas ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    match_case Some(()) {
      Some(_) \<Rightarrow> { () }
      None if true \<Rightarrow> return,
      _ \<Rightarrow> return
    }
  \<close>

urust_expr grammar_case_operandless_return_arm_blocks ::
  \<open>(unit, unit, unit, unit, unit, unit) expression\<close>
  \<open>
    match_case Some(()) {
      Some(_) \<Rightarrow> { () }
      None if true \<Rightarrow> { return; },
      _ \<Rightarrow> { return; },
    }
  \<close>

lemma grammar_case_operandless_return_arm_equality:
  \<open>grammar_case_operandless_return_arm_commas = grammar_case_operandless_return_arm_blocks\<close>
  unfolding grammar_case_operandless_return_arm_commas_def grammar_case_operandless_return_arm_blocks_def
  by (rule refl)

urust_expr grammar_switch_valued_return_arm_commas ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match_switch \<llangle>0 :: nat\<rrangle> {
      0 \<Rightarrow> { \<llangle>0 :: nat\<rrangle> }
      1 \<Rightarrow> return \<llangle>1 :: nat\<rrangle>,
      _ \<Rightarrow> return \<llangle>2 :: nat\<rrangle>
    }
  \<close>

urust_expr grammar_switch_valued_return_arm_blocks ::
  \<open>(unit, nat, nat, unit, unit, unit) expression\<close>
  \<open>
    match_switch \<llangle>0 :: nat\<rrangle> {
      0 \<Rightarrow> { \<llangle>0 :: nat\<rrangle> }
      1 \<Rightarrow> { return \<llangle>1 :: nat\<rrangle>; },
      _ \<Rightarrow> { return \<llangle>2 :: nat\<rrangle>; },
    }
  \<close>

lemma grammar_switch_valued_return_arm_equality:
  \<open>grammar_switch_valued_return_arm_commas = grammar_switch_valued_return_arm_blocks\<close>
  unfolding grammar_switch_valued_return_arm_commas_def grammar_switch_valued_return_arm_blocks_def
  by (rule refl)

urust_expr grammar_return_arm_recovery
  \<open> match true { true \<Rightarrow> return (), false \<Rightarrow> return (), } \<close>

urust_expr_rejects
  \<open>
    match true {
      true \<Rightarrow> \<llangle>1 :: nat\<rrangle>;,
      false \<Rightarrow> \<llangle>2 :: nat\<rrangle>
    }
  \<close>
  \<open> syntax error \<close>
  \<comment> \<open> Direct expression arms use commas; arbitrary semicolon arms remain invalid. \<close>

section\<open>Closures and binding RHSs\<close>

urust_expr  grammar_direct_closure_initializer
  \<open>
    let f = |x| x + \<llangle>1 :: 32 word\<rrangle>;
    ()
  \<close>

urust_expr grammar_closure_full_body
  \<open>
    |x| if true { x } else { x + \<llangle>1 :: 32 word\<rrangle> }
  \<close>

urust_expr  grammar_closure_if_let_body
  \<open>
    || if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr  grammar_closure_mixed_if_body
  \<open>
    || if true { 0 } else if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr  grammar_closure_return_body
  \<open> || return \<llangle>1 :: nat\<rrangle> \<close>

urust_expr  grammar_nested_closure_body
  \<open> || || \<llangle>1 :: nat\<rrangle> \<close>

urust_expr  grammar_if_let_operand
  \<open>
    if let Some(value) = Some(\<llangle>1 :: 32 word\<rrangle>) {
      value
    } else {
      \<llangle>0 :: 32 word\<rrangle>
    } + \<llangle>1 :: 32 word\<rrangle>
  \<close>

urust_expr  grammar_closure_match_scrutinee
  \<open> match || true { _ \<Rightarrow> () } \<close>

urust_expr  grammar_closure_match_arms
  \<open>
    match true {
      true \<Rightarrow> || true,
      false \<Rightarrow> || false
    }
  \<close>

section\<open>Integer literal bases and separators\<close>

urust_expr grammar_binary \<open> 0b1010 \<close>

urust_expr grammar_binary_suffix
  \<open> 0b1111u8 \<close>

urust_expr grammar_binary_trailing_separator
  \<open> 0b1010_ \<close>

urust_expr grammar_octal
  \<open> 0o755 \<close>

urust_expr grammar_octal_suffix
  \<open> 0o17_u16 \<close>

urust_expr grammar_octal_trailing_separator
  \<open> 0o17_ \<close>

urust_expr grammar_decimal_separators
  \<open> 1_000_000u32 \<close>

urust_expr grammar_hex_separators
  \<open> 0xff_00u32 \<close>

urust_expr grammar_decimal_trailing_separator
  \<open> 1_ \<close>

urust_expr grammar_hex_trailing_separator
  \<open> 0xff_ \<close>

section\<open>Struct expressions\<close>

datatype grammar_empty_struct = GrammarEmptyStruct

definition grammar_empty_struct_call ::
    \<open>(unit, grammar_empty_struct, unit, unit, unit) function_body\<close>
  where
    \<open>grammar_empty_struct_call \<equiv> FunctionBody (literal GrammarEmptyStruct)\<close>

micro_rust_notation (call) grammar_empty_struct_call ("GrammarEmptyStruct")

urust_expr grammar_empty_struct_expression
  \<open> GrammarEmptyStruct {} \<close>

definition grammar_empty_bool_value :: bool
  where \<open>grammar_empty_bool_value \<equiv> True\<close>

definition grammar_empty_bool_call ::
    \<open>(unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_bool_call \<equiv>
        FunctionBody (literal grammar_empty_bool_value)
    \<close>

definition grammar_empty_option_value :: \<open>unit option\<close>
  where \<open>grammar_empty_option_value \<equiv> Some ()\<close>

definition grammar_empty_option_call ::
    \<open>(unit, unit option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_option_call \<equiv>
        FunctionBody (literal grammar_empty_option_value)
    \<close>

definition grammar_empty_list_value :: \<open>unit list\<close>
  where \<open>grammar_empty_list_value \<equiv> [()]\<close>

definition grammar_empty_list_call ::
    \<open>(unit, unit list, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_list_call \<equiv>
        FunctionBody (literal grammar_empty_list_value)
    \<close>

definition grammar_empty_nat_value :: nat
  where \<open>grammar_empty_nat_value \<equiv> 1\<close>

definition grammar_empty_nat_call ::
    \<open>(unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_empty_nat_call \<equiv>
        FunctionBody (literal grammar_empty_nat_value)
    \<close>

micro_rust_notation (call)
  grammar_empty_bool_call ("grammar_empty_bool_value")

micro_rust_notation (call)
  grammar_empty_option_call ("grammar_empty_option_value")

micro_rust_notation (call)
  grammar_empty_list_call ("grammar_empty_list_value")

micro_rust_notation (call)
  grammar_empty_nat_call ("grammar_empty_nat_value")

definition grammar_propagate_bool_value :: \<open>bool option\<close>
  where \<open>grammar_propagate_bool_value \<equiv> Some True\<close>

definition grammar_propagate_bool_call ::
    \<open>(unit, bool option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_bool_call \<equiv>
        FunctionBody (literal grammar_propagate_bool_value)
    \<close>

definition grammar_propagate_option_value :: \<open>unit option option\<close>
  where \<open>grammar_propagate_option_value \<equiv> Some (Some ())\<close>

definition grammar_propagate_option_call ::
    \<open>(unit, unit option option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_option_call \<equiv>
        FunctionBody (literal grammar_propagate_option_value)
    \<close>

definition grammar_propagate_list_value :: \<open>unit list option\<close>
  where \<open>grammar_propagate_list_value \<equiv> Some [()]\<close>

definition grammar_propagate_list_call ::
    \<open>(unit, unit list option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_list_call \<equiv>
        FunctionBody (literal grammar_propagate_list_value)
    \<close>

definition grammar_propagate_nat_value :: \<open>nat option\<close>
  where \<open>grammar_propagate_nat_value \<equiv> Some 1\<close>

definition grammar_propagate_nat_call ::
    \<open>(unit, nat option, unit, unit, unit) function_body\<close>
  where
    \<open>
      grammar_propagate_nat_call \<equiv>
        FunctionBody (literal grammar_propagate_nat_value)
    \<close>

micro_rust_notation (call)
  grammar_propagate_bool_call ("grammar_propagate_bool_value")

micro_rust_notation (call)
  grammar_propagate_option_call ("grammar_propagate_option_value")

micro_rust_notation (call)
  grammar_propagate_list_call ("grammar_propagate_list_value")

micro_rust_notation (call)
  grammar_propagate_nat_call ("grammar_propagate_nat_value")

subsection\<open>Empty struct expressions in control heads\<close>

text\<open>
Each surface name below is both a genuine bare HOL value and a registered nullary call. In a
no-struct control head, its first empty braces must not be silently consumed as the control body.
Explicit grouping restores unrestricted expression parsing.
\<close>

urust_expr_rejects
  \<open> if grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if let Some(_) = grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> if let _ = GrammarEmptyStruct {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> for _ in grammar_empty_list_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    match grammar_empty_bool_value {} {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match_case grammar_empty_option_value {} {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open>
    match_switch grammar_empty_nat_value {} {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

urust_expr_rejects
  \<open> if !grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open> if true && grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if false || true && !grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

urust_expr_rejects
  \<open>
    if true == grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

text\<open>
Postfix propagation closes its operand before the control body begins. It therefore disambiguates
the following empty braces even when the operand path also names a registered nullary call.
True prefix operators surrounding the propagated expression retain that postfix boundary.
\<close>

urust_expr  grammar_propagate_empty_body_if
  \<open> if grammar_propagate_bool_value? {} else {} \<close>

urust_expr  grammar_propagate_empty_body_if_let
  \<open>
    if let Some(_) = grammar_propagate_option_value? {} else {}
  \<close>

urust_expr  grammar_propagate_empty_body_for
  \<open> for _ in grammar_propagate_list_value? {} \<close>

urust_expr  grammar_propagate_empty_body_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_propagate_option_value? {}
  \<close>

urust_expr  grammar_propagate_empty_body_match
  \<open>
    match grammar_propagate_bool_value? {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_empty_body_match_case
  \<open>
    match_case grammar_propagate_option_value? {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_empty_body_match_switch
  \<open>
    match_switch grammar_propagate_nat_value? {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_propagate_nested_prefix_empty_body
  \<open> if !grammar_propagate_bool_value? {} else {} \<close>

urust_expr  grammar_propagate_nested_binary_empty_body
  \<open>
    if false || grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr  grammar_propagate_nested_comparison_empty_body
  \<open>
    if true == grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_if
  \<open>
    if (grammar_empty_bool_value {}) {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_if_let
  \<open>
    if let Some(_) = (grammar_empty_option_value {}) {} else {}
  \<close>

urust_expr  grammar_grouped_empty_struct_for
  \<open> for _ in (grammar_empty_list_value {}) {} \<close>

urust_expr  grammar_grouped_empty_struct_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      (grammar_empty_option_value {}) {}
  \<close>

urust_expr  grammar_grouped_empty_struct_match
  \<open>
    match (grammar_empty_bool_value {}) {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_grouped_empty_struct_match_case
  \<open>
    match_case (grammar_empty_option_value {}) {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr  grammar_grouped_empty_struct_match_switch
  \<open>
    match_switch (grammar_empty_nat_value {}) {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

definition grammar_bare_flag :: bool
  where \<open>grammar_bare_flag \<equiv> True\<close>

urust_expr  grammar_bare_path_empty_body
  \<open> if grammar_bare_flag {} \<close>

urust_expr  grammar_bare_path_empty_body_sequence
  \<open> if grammar_bare_flag {} {} \<close>

urust_expr  grammar_nested_bare_path_empty_body_sequence
  \<open> if true && grammar_bare_flag {} {} \<close>

context fixes flag :: bool
begin

urust_expr  grammar_fixed_path_empty_body_sequence
  \<open> if flag {} {} \<close>

end

urust_expr  grammar_struct_trailing_comma
  \<open>
    D21Pair {
      second: 2_u64,
      first: 1_u64,
    }
  \<close>

chapter\<open>Logging\<close>

text\<open>
This suite is evaluated after \<open>Parser_Expression_Examples\<close>, so the logging import does
not affect that theory's built-in macro coverage. The parser-test logging fixture imports
\<open>StdLib_Logging\<close>, which registers the syntax used by
\<open>l\<llangle>...\<rrangle>\<close> together with \<open>fatal!\<close>, \<open>info!\<close>,
and the other logger calls. In particular, registered \<open>fatal!\<close> takes precedence over
the built-in macro in this context. Keeping the import isolated preserves the main suite's built-in
\<open>fatal!\<close> coverage.
\<close>

section\<open> Logging-data expressions \<close>

urust_expr log_data_one_string
  \<open> l\<llangle>"one"\<rrangle> \<close>

context
  fixes context_value :: nat
begin

urust_expr log_data_one_identifier
  \<open> l\<llangle>context_value\<rrangle> \<close>

urust_expr log_data_mixed
  \<open> l\<llangle>"value = ", context_value, "."\<rrangle> \<close>

urust_expr log_data_repeated_identifier
  \<open> l\<llangle>context_value, context_value, context_value\<rrangle> \<close>

end

urust_expr log_data_long
  \<open>
    l\<llangle>
      "a", True, "b", False, "c", True,
      "d", False, "e", True, "f", False
    \<rrangle>
  \<close>

urust_expr log_data_empty_string
  \<open> l\<llangle>""\<rrangle> \<close>

urust_expr log_data_multiline
  \<open>
    l\<llangle>
      "first",
      True,
      "second",
      False
    \<rrangle>
  \<close>

subsection\<open> String-token boundaries \<close>

urust_expr log_data_escaped_quote
  \<open> l\<llangle>"say: \"hello\""\<rrangle> \<close>

urust_expr log_data_escaped_backslash
  \<open> l\<llangle>"left\\right"\<rrangle> \<close>

urust_expr log_data_comma_in_string
  \<open> l\<llangle>"left, right"\<rrangle> \<close>

urust_expr log_data_comment_text
  \<open> l\<llangle>"https://example.invalid//path"\<rrangle> \<close>

urust_expr log_data_keyword_text
  \<open> l\<llangle>"true false let const return log yield l"\<rrangle> \<close>

subsection\<open> Identifier resolution and lexical scope \<close>

definition logging_collision :: nat
  where \<open> logging_collision = 17 \<close>

definition logging_notation_target :: nat
  where \<open> logging_notation_target = 99 \<close>

micro_rust_notation (literal) logging_notation_target ("logging_collision")

urust_expr log_data_hol_constant
  \<open> l\<llangle>logging_collision\<rrangle> \<close>

urust_expr log_data_boolean_constant
  \<open> l\<llangle>True, False\<rrangle> \<close>

urust_expr log_data_local
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    l\<llangle>"value = ", value\<rrangle>
  \<close>

urust_expr log_data_nested_shadowing
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    let outer = l\<llangle>value\<rrangle>;
    let value = \<llangle>7 :: nat\<rrangle>;
    (outer, l\<llangle>value\<rrangle>)
  \<close>

urust_expr log_data_constant_named_binder
  \<open>
    let Some = \<llangle>11 :: nat\<rrangle>;
    l\<llangle>Some, Some\<rrangle>
  \<close>

subsection\<open> Registered logging calls \<close>

urust_expr registered_fatal_logger
  \<open> fatal!(l\<llangle>"fatal", True\<rrangle>) \<close>

urust_expr registered_info_logger
  \<open> info!(l\<llangle>"info", True\<rrangle>) \<close>

urust_expr registered_error_logger
  \<open> error!(l\<llangle>"error", True\<rrangle>) \<close>

urust_expr registered_debug_logger
  \<open> debug!(l\<llangle>"debug", False\<rrangle>) \<close>

urust_expr registered_trace_logger
  \<open> trace!(l\<llangle>"trace", True\<rrangle>) \<close>

text\<open>
The first row specifically checks that the adjacent registered \<open>fatal!\<close> call wins over the
built-in message macro in this import context. The expression suite does not import
\<open>StdLib_Logging\<close>, so its built-in \<open>fatal!\<close> coverage remains unchanged.
\<close>

chapter\<open>Comments\<close>

section\<open> Isabelle formal comments \<close>

text\<open>
Formal comments are layout for the dedicated parser. The lexer reports their complete source span
with Isabelle's inner-syntax comment style, while Isabelle's document machinery remains responsible
for checking document antiquotations inside the cartouche.
\<close>

subsection\<open> Expression and function parity \<close>

urust_expr isabelle_comment_standalone
  \<open>
    \<comment> \<open>Standalone comment before the expression, with literal block markers /* */.\<close>
    ()
  \<close>

urust_expr isabelle_comment_inline
  \<open>
    1_u64\<comment>\<open>Comment between operands: + - * / { } [ ] ( ) , ; :: =>.\<close>+2_u64
  \<close>

urust_expr isabelle_comment_trailing
  \<open>
    ();
    () \<comment> \<open>Trailing comment after the complete expression.\<close>
  \<close>

urust_expr isabelle_comment_multiline_nested
  \<open>
    \<comment> \<open>
      Outer document text with \<open>nested { grammar } punctuation\<close> and
      \<open>another \<open>deeply nested\<close> cartouche\<close>.
      Escaped Isabelle symbols remain document text: \<alpha> \<Rightarrow> \<forall>.
    \<close>
    if true {
      \<comment> \<open>Then branch.\<close>
      3_u64
    } else {
      4_u64
    }
  \<close>

urust_expr isabelle_comment_document_antiquotations
  \<open>
    \<comment> \<open>
      Modern controls: \<^term>\<open>True\<close>, \<^const>\<open>False\<close>, and
      \<^verbatim>\<open>{ grammar punctuation, :: => }\<close>.
      Legacy antiquotations: @{term True} and
      @{verbatim \<open>[legacy punctuation; + - *]\<close>}.
    \<close>
    ()
  \<close>

urust_fn isabelle_comment_function
  \<open>
  fn isabelle_comment_function(item: \<tau>\<open>nat\<close>) -> \<tau>\<open>nat\<close> {
    \<comment> \<open>Function-body comment with \<^term>\<open>item\<close> treated as document text.\<close>
    item \<comment> \<open>Inline function-body comment.\<close>
  }
  \<close>

subsection\<open> Specialized lexer contexts \<close>

definition isabelle_comment_generic ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>isabelle_comment_generic parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument)\<close>

micro_rust_notation (call) isabelle_comment_generic ("Comment::generic")

urust_expr isabelle_comment_generic_layout
  \<open>
    Comment::generic::<
      1 \<comment> \<open>Generic-state layout with \<open>> , + ::\<close>.\<close> + 2
    >(3)
  \<close>

urust_expr isabelle_comment_log_data_layout
  \<open>
    l\<llangle>
      \<comment> \<open>Log-data layout before the first entry.\<close>
      "value = ",
      \<comment> \<open>Log-data layout after a separator.\<close>
      True
    \<rrangle>
  \<close>

subsection\<open> Literal comment-shaped text \<close>

text\<open>
The structural audit below feeds complete comment-shaped text directly to the lexer and verifies that
quoted strings and both uRust antiquotation states retain it byte-for-byte.
\<close>

end
