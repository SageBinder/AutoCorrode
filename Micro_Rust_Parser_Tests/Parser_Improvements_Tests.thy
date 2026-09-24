(* Accepted-surface improvements and intentional checked-term corrections.
   Test order is significant and matches the former focused theory. *)

theory Parser_Improvements_Tests
  imports
    Parser_Expression_Tests
    Parser_Function_Tests
    Parser_Cast_Alias_Fixtures
    Misc.Simple_Word_Enums
begin

declare [[urust_pp_test = true]]

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


section\<open>Nested Rust block comments\<close>

text\<open>
Nested \<open>/* ... */\<close> comments are ordinary-source layout. Strings and both antiquotation states
retain the same marker text as literal content.
\<close>

urust_expr improvement_block_comment_empty
  \<open> /**/ () \<close>

urust_expr improvement_block_comment_leading
  \<open>
    /** ordinary documentation-shaped comment */
    ()
  \<close>

urust_expr improvement_block_comment_trailing
  \<open>
    ()
    /*! ordinary inner-documentation-shaped comment */
  \<close>

urust_expr improvement_block_comment_token_adjacent
  \<open> 1_u64/* left */+/* right */2_u64 \<close>

urust_expr improvement_block_comment_multiline_nested
  \<open>
    1_u64 /*
      Operators and delimiters are inert: + - * / // => { [ ( , ;.
      Quotes are inert too: "/* not an opener in a string language */".
      Formal-comment-shaped text remains body text:
        \<comment> \<open>not an Isabelle comment at this lexer layer\<close>
      Escaped symbols remain body text: \<alpha> \<Rightarrow>.
      /* nested /* deeply nested */ comment */
    */ + 2_u64
  \<close>

urust_expr improvement_block_comment_division_adjacent
  \<open> 8_u64/**//2_u64 \<close>

urust_expr improvement_block_comment_multiplication_adjacent
  \<open> 2_u64*/* layout after multiplication */3_u64 \<close>

urust_expr improvement_block_comment_nested_control
  \<open>
    if true {
      /* outer /* inner */ */
      3_u64
    } else {
      4_u64 /* trailing branch layout */
    }
  \<close>


section\<open>Array repeats\<close>

text\<open>
Ordinary repeats evaluate their operand once and replicate the resulting value. Repeat-local
inline-const bodies use the same lowering.
\<close>

lemma improvement_array_repeat_unat_word64_2 [simp]:
  \<open>unat (2 :: 64 word) = 2\<close>
  by eval

lemma improvement_array_repeat_unat_word64_3 [simp]:
  \<open>unat (3 :: 64 word) = 3\<close>
  by eval

lemma improvement_array_repeat_take_bit_word64_2 [simp]:
  \<open>take_bit LENGTH(64) (2 :: nat) = 2\<close>
  by (rule take_bit_nat_eq_self; simp)

lemma improvement_array_repeat_take_bit_word64_3 [simp]:
  \<open>take_bit LENGTH(64) (3 :: nat) = 3\<close>
  by (rule take_bit_nat_eq_self; simp)

urust_expr improvement_array_repeat_ordinary ::
  \<open>(unit, nat list, unit, unit, unit, unit) expression\<close>
  \<open> [\<llangle>1 :: nat\<rrangle>; 3] \<close>

lemma improvement_array_repeat_ordinary_result:
  \<open>
    evaluate improvement_array_repeat_ordinary () =
      Success [1, 1, 1] ()
  \<close>
  by
    (simp add:
      improvement_array_repeat_ordinary_def
      evaluate_def
      literal_def
      Core_Expression.bind.simps;
      simp add: eval_nat_numeral)

urust_expr improvement_array_repeat_inline_const ::
  \<open>(unit, nat option list, unit, unit, unit, unit) expression\<close>
  \<open> [const { Some(\<llangle>1 :: nat\<rrangle>) }; 2] \<close>

lemma improvement_array_repeat_inline_const_result:
  \<open>
    evaluate improvement_array_repeat_inline_const () =
      Success [Some 1, Some 1] ()
  \<close>
  apply (simp add: improvement_array_repeat_inline_const_def)
  apply (simp add: micro_rust_simps)
  apply
    (simp add:
      Core_Expression.bind.simps
      Core_Expression.call_function_body.simps
      evaluate_def
      literal_def
      call_def
      fun_literal_def)
  apply
    (simp add:
      eval_nat_numeral
      list_sequence.simps
      evaluate_def
      literal_def
      Core_Expression.bind.simps)
  done


section\<open>Scoped cast-target aliases\<close>

text\<open>
An explicitly included bundle activates exact path aliases for the existing primitive cast targets.
The alias changes only source spelling: checked terms remain identical to primitive casts.
\<close>

context includes module_cast_aliases
begin

context
  fixes improvement_cast_alias_word :: "64 word"
begin

urust_expr improvement_cast_target_alias_integral
  \<open> improvement_cast_alias_word as types::U16Alias \<close>

end

context
  fixes improvement_cast_alias_raw :: "('address, 'global) gref"
begin

urust_expr improvement_cast_target_alias_pointer
  \<open> improvement_cast_alias_raw as MutUsizePointer \<close>

end

end


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

no_adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture


section\<open>Recursive reference-prefix composition\<close>

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

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open>Rust-aligned dereference/postfix precedence\<close>

text\<open>
Postfix operators bind before dereference uniformly. The dedicated parser therefore reads an
unparenthesized index or field chain as the dereference operand. Parenthesizing the dereference
itself retains the \<open>(*base)[index]\<close> meaning.
\<close>

datatype_record deref_postfix_fixture =
  deref_postfix_fixture_field ::
    \<open>(unit, unit, 64 word) Global_Store.ref\<close>
micro_rust_record deref_postfix_fixture
  (deref_postfix_fixture_field = "field")

definition deref_postfix_identity ::
    \<open>
      deref_postfix_fixture \<Rightarrow>
      (unit, deref_postfix_fixture, unit, unit, unit) function_body
    \<close>
  where \<open>deref_postfix_identity \<equiv> lift_fun1 (\<lambda>value. value)\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes references :: \<open>(unit, unit, 64 word) Global_Store.ref list\<close>
    and base :: deref_postfix_fixture
    and array_ref ::
      \<open>(unit, unit, (64 word, 4) array) Global_Store.ref\<close>
begin

urust_expr improvement_deref_index_operand
  \<open> *references[0_usize] \<close>

urust_expr improvement_deref_grouped_field_operand
  \<open> *(base).field \<close>

urust_expr improvement_deref_call_field_operand
  \<open> *deref_postfix_identity(base).field \<close>

urust_expr improvement_deref_simple_field_operand
  \<open> *base.field \<close>

urust_expr improvement_group_deref_before_index
  \<open> (*array_ref)[0_usize] \<close>

end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open>Expression-antiquotation places\<close>

text\<open>
Expression antiquotations may serve as assignment places. These rows cover a
fixed reference and capture of a mutable local inside the antiquotation body.
\<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
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

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture


section\<open>Compositional field places\<close>

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

no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture


section\<open>Composable postfix expressions\<close>

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

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

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

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


chapter\<open>Intentional semantic corrections\<close>

section\<open>Checked-term corrections\<close>

text\<open>
These sources exercise intentional checked-term corrections.
\<open>Parser_Pattern_Matching_Tests.thy\<close> pins the associated term shapes.
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
end
