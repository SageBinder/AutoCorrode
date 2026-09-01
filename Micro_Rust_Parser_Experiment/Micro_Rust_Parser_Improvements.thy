theory Micro_Rust_Parser_Improvements
  imports Micro_Rust_Parser_Conformance
  keywords
    "old_urust_rejects" :: thy_decl
begin

section\<open> Test support \<close>

text\<open>
Each example is accepted by the new parser. Where an equivalent old-frontend
spelling exists, \<open>urust_expr_with_check'\<close> checks the two results by \<open>refl\<close>.
The paired command feeds the new spelling to the old frontend and requires it to reject.
\<close>

ML\<open>
fun old_urust_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (old_urust_source "()")

fun old_urust_rejects source lthy =
  let
    val pos = Input.pos_of source
    val wrapped = old_urust_source (Input.string_of source)
    fun fail term =
      error ("old_urust_rejects: expected the old frontend to reject, but it accepted:\n" ^
        Syntax.string_of_term lthy term ^ Position.here pos)
  in
    (case Exn.result (Syntax.read_term lthy) wrapped of
       Exn.Res term => fail term
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (writeln ("old frontend rejected as expected: " ^ Runtime.exn_message exn);
            lthy))
  end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>old_urust_rejects\<close>
  "Assert that the old inner-syntax uRust frontend rejects a source expression"
  (Parse.input Parse.cartouche >> old_urust_rejects)
\<close>


section\<open> Rust line comments \<close>

text\<open>
The production lexer skips \<open>//\<close> comments only in its ordinary Rust state.
The old inner-syntax frontend has no Rust comment token, so these accepted
spellings are tested against the corresponding comment-free frontend terms.
Literal \<open>//\<close> inside strings and both antiquotation states remains content;
the shared spellings are covered in the conformance theory.
\<close>

urust_expr_with_check' improvement_line_comment_full_line
  \<open>
    // full-line comment
    ()
  \<close>
  \<open> \<lbrakk> () \<rbrakk> \<close>
old_urust_rejects
  \<open>
    // full-line comment
    ()
  \<close>

urust_expr_with_check' improvement_line_comment_end_of_line
  \<open>
    ();
    () // end-of-line comment
  \<close>
  \<open> \<lbrakk> (); () \<rbrakk> \<close>
old_urust_rejects
  \<open>
    ();
    () // end-of-line comment
  \<close>

urust_expr_with_check' improvement_line_comment_between_tokens
  \<open>
    \<llangle>1 :: 32 word\<rrangle> // between the operands and operator
      + \<llangle>2 :: 32 word\<rrangle>
  \<close>
  \<open> \<lbrakk> \<llangle>1 :: 32 word\<rrangle> + \<llangle>2 :: 32 word\<rrangle> \<rbrakk> \<close>
old_urust_rejects
  \<open>
    \<llangle>1 :: 32 word\<rrangle> // between the operands and operator
      + \<llangle>2 :: 32 word\<rrangle>
  \<close>

urust_expr_with_check' improvement_line_comment_operator_text
  \<open>
    () // += => \<Rightarrow> /= /* block-shaped text */
  \<close>
  \<open> \<lbrakk> () \<rbrakk> \<close>
old_urust_rejects
  \<open>
    () // += => \<Rightarrow> /= /* block-shaped text */
  \<close>

urust_expr_with_check' improvement_line_comment_empty
  \<open>
    {
      //
      ()
    }
  \<close>
  \<open> \<lbrakk> { () } \<rbrakk> \<close>
old_urust_rejects
  \<open>
    {
      //
      ()
    }
  \<close>

urust_expr_with_check' improvement_line_comment_eof
  \<open> () // comment at EOF \<close>
  \<open> \<lbrakk> () \<rbrakk> \<close>
old_urust_rejects \<open> () // comment at EOF \<close>

urust_expr_with_check' improvement_line_comment_nested_adjacent
  \<open>
    if true {// then branch
      {// nested block
        ()// body value
      }// after nested block
    } else {// else branch
      ()
    }
  \<close>
  \<open> \<lbrakk> if true { { () } } else { () } \<rbrakk> \<close>
old_urust_rejects
  \<open>
    if true {// then branch
      {// nested block
        ()// body value
      }// after nested block
    } else {// else branch
      ()
    }
  \<close>


section\<open> Rust-compatible integer suffixes \<close>

text\<open>
The custom lexer accepts Rust's glued integer suffixes. Each decimal and hexadecimal
form is equal to the old frontend's underscore spelling, which remains accepted.
The old frontend rejects every glued spelling below.
\<close>

urust_expr_with_check' improvement_integer_suffix_decimal_u8
  \<open> 1u8 \<close>
  \<open> \<lbrakk> 1_u8 \<rbrakk> \<close>
old_urust_rejects \<open> 1u8 \<close>

urust_expr_with_check' improvement_integer_suffix_hex_u8
  \<open> 0xffu8 \<close>
  \<open> \<lbrakk> 0xff_u8 \<rbrakk> \<close>
old_urust_rejects \<open> 0xffu8 \<close>

urust_expr_with_check' improvement_integer_suffix_decimal_u16
  \<open> 2u16 \<close>
  \<open> \<lbrakk> 2_u16 \<rbrakk> \<close>
old_urust_rejects \<open> 2u16 \<close>

urust_expr_with_check' improvement_integer_suffix_hex_u16
  \<open> 0x12abu16 \<close>
  \<open> \<lbrakk> 0x12ab_u16 \<rbrakk> \<close>
old_urust_rejects \<open> 0x12abu16 \<close>

urust_expr_with_check' improvement_integer_suffix_decimal_u32
  \<open> 3u32 \<close>
  \<open> \<lbrakk> 3_u32 \<rbrakk> \<close>
old_urust_rejects \<open> 3u32 \<close>

urust_expr_with_check' improvement_integer_suffix_hex_u32
  \<open> 0x1234abcdu32 \<close>
  \<open> \<lbrakk> 0x1234abcd_u32 \<rbrakk> \<close>
old_urust_rejects \<open> 0x1234abcdu32 \<close>

urust_expr_with_check' improvement_integer_suffix_decimal_u64
  \<open> 4u64 \<close>
  \<open> \<lbrakk> 4_u64 \<rbrakk> \<close>
old_urust_rejects \<open> 4u64 \<close>

urust_expr_with_check' improvement_integer_suffix_hex_u64
  \<open> 0x123456789abcdef0u64 \<close>
  \<open> \<lbrakk> 0x123456789abcdef0_u64 \<rbrakk> \<close>
old_urust_rejects \<open> 0x123456789abcdef0u64 \<close>

urust_expr_with_check' improvement_integer_suffix_decimal_usize
  \<open> 5usize \<close>
  \<open> \<lbrakk> 5_usize \<rbrakk> \<close>
old_urust_rejects \<open> 5usize \<close>

urust_expr_with_check' improvement_integer_suffix_hex_usize
  \<open> 0xffffffff0usize \<close>
  \<open> \<lbrakk> 0xffffffff0_usize \<rbrakk> \<close>
old_urust_rejects \<open> 0xffffffff0usize \<close>


section\<open> ASCII match arrows \<close>

urust_expr_with_check' improvement_ascii_match_arrow
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>
  \<open> \<lbrakk> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> 0 } \<rbrakk> \<close>
old_urust_rejects
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>

urust_expr_with_check' improvement_ascii_match_arrow_guarded
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) if True => x, None => 0 } \<close>
  \<open> \<lbrakk> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) if True \<Rightarrow> x, None \<Rightarrow> 0 } \<rbrakk> \<close>
old_urust_rejects
  \<open> match \<llangle>Some (1 :: nat)\<rrangle> { Some(x) if True => x, None => 0 } \<close>

urust_expr_with_check' improvement_ascii_match_arrow_nested
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) => match x { 0 => 0, _ => x },
      None => 0
    }
  \<close>
  \<open>
    \<lbrakk>
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(x) \<Rightarrow> match x { 0 \<Rightarrow> 0, _ \<Rightarrow> x },
        None \<Rightarrow> 0
      }
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) => match x { 0 => 0, _ => x },
      None => 0
    }
  \<close>

urust_expr_with_check' improvement_ascii_match_arrow_case
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>
  \<open> \<lbrakk> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) \<Rightarrow> x, None \<Rightarrow> 0 } \<rbrakk> \<close>
old_urust_rejects
  \<open> match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) => x, None => 0 } \<close>

urust_expr_with_check' improvement_ascii_match_arrow_switch
  \<open>
    match_switch \<llangle>1 :: nat\<rrangle> {
      0 => \<llangle>False\<rrangle>,
      _ => \<llangle>True\<rrangle>
    }
  \<close>
  \<open>
    \<lbrakk>
      match_switch \<llangle>1 :: nat\<rrangle> {
        0 \<Rightarrow> \<llangle>False\<rrangle>,
        _ \<Rightarrow> \<llangle>True\<rrangle>
      }
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    match_switch \<llangle>1 :: nat\<rrangle> {
      0 => \<llangle>False\<rrangle>,
      _ => \<llangle>True\<rrangle>
    }
  \<close>


section\<open> Empty blocks \<close>

urust_expr_with_check' improvement_empty_block_value
  \<open> {} \<close>
  \<open> \<lbrakk> { () } \<rbrakk> \<close>
old_urust_rejects
  \<open> {} \<close>

urust_expr_with_check' improvement_empty_block_branches
  \<open> if true {} else {} \<close>
  \<open> \<lbrakk> if true { () } else { () } \<rbrakk> \<close>
old_urust_rejects
  \<open> if true {} else {} \<close>

urust_expr_with_check' improvement_empty_block_nested
  \<open> {{}} \<close>
  \<open> \<lbrakk> {{ () }} \<rbrakk> \<close>
old_urust_rejects
  \<open> {{}} \<close>

urust_expr_with_check' improvement_empty_block_statement
  \<open> {} () \<close>
  \<open> \<lbrakk> { () } () \<rbrakk> \<close>
old_urust_rejects
  \<open> {} () \<close>

urust_expr_with_check' improvement_empty_unsafe_block
  \<open> unsafe {} \<close>
  \<open> \<lbrakk> unsafe { () } \<rbrakk> \<close>
old_urust_rejects
  \<open> unsafe {} \<close>


section\<open> Trailing commas \<close>

text\<open>
The old frontend accepts trailing commas only in slice patterns, whose shared
cases are in \<open>Micro_Rust_Parser_Conformance\<close>. Calls, arms, constructor
patterns, tuples, and struct patterns reject there. Each source below is checked
against the same old-frontend term with only its terminal comma removed.
\<close>

urust_expr_with_check' improvement_trailing_direct_call
  \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>,) \<close>
  \<open> \<lbrakk> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close>
old_urust_rejects
  \<open> cf2(\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>,) \<close>

urust_expr_with_check' improvement_trailing_method_call
  \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>,) \<close>
  \<open> \<lbrakk> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>) \<rbrakk> \<close>
old_urust_rejects
  \<open> \<llangle>1 :: 64 word\<rrangle>.cf2(\<llangle>2 :: 64 word\<rrangle>,) \<close>

urust_expr_with_check' improvement_trailing_guarded_arm
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if True \<Rightarrow> x,
      None \<Rightarrow> 0,
    }
  \<close>
  \<open>
    \<lbrakk>
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(x) if True \<Rightarrow> x,
        None \<Rightarrow> 0
      }
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    match \<llangle>Some (1 :: nat)\<rrangle> {
      Some(x) if True \<Rightarrow> x,
      None \<Rightarrow> 0,
    }
  \<close>

urust_expr_with_check' improvement_trailing_constructor_pattern
  \<open> match_case \<llangle>P2 1 2\<rrangle> { P2(x, y,) \<Rightarrow> x } \<close>
  \<open> \<lbrakk> match_case \<llangle>P2 1 2\<rrangle> { P2(x, y) \<Rightarrow> x } \<rbrakk> \<close>
old_urust_rejects
  \<open> match_case \<llangle>P2 1 2\<rrangle> { P2(x, y,) \<Rightarrow> x } \<close>

urust_expr_with_check' improvement_trailing_tuple_expression
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>,) \<close>
  \<open> \<lbrakk> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>) \<rbrakk> \<close>
old_urust_rejects
  \<open> (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>,) \<close>

urust_expr_with_check' improvement_trailing_tuple_pattern
  \<open>
    let (x, y,) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>);
    x
  \<close>
  \<open>
    \<lbrakk>
      let (x, y) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>);
      x
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    let (x, y,) = (\<llangle>1 :: nat\<rrangle>, \<llangle>True\<rrangle>);
    x
  \<close>

urust_expr_with_check' improvement_trailing_struct_pattern
  \<open>
    match \<llangle>AdvStruct 1 2\<rrangle> {
      AdvStruct { adv_left: x, adv_right: y, } \<Rightarrow> x,
      _ \<Rightarrow> 0
    }
  \<close>
  \<open>
    \<lbrakk>
      match \<llangle>AdvStruct 1 2\<rrangle> {
        AdvStruct { adv_left: x, adv_right: y } \<Rightarrow> x,
        _ \<Rightarrow> 0
      }
    \<rbrakk>
  \<close>
old_urust_rejects
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

urust_expr_with_check' improvement_trailing_composed
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
  \<open>
    \<lbrakk>
      let (x, y) = (\<llangle>1 :: 64 word\<rrangle>, \<llangle>2 :: 64 word\<rrangle>);
      cf2(
        match \<llangle>TrailingComma (Some 3) [4, 5]\<rrangle> {
          TrailingComma {
            trailing_option: Some(z),
            trailing_values: [head, .., tail]
          } if True \<Rightarrow>
            x.cf2(z),
          _ \<Rightarrow>
            y
        },
        y
      )
    \<rbrakk>
  \<close>
old_urust_rejects
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


section\<open> Compositional range patterns \<close>

datatype improvement_packet =
    ImprovementPacket
      (improvement_tag: nat)
      (improvement_values: "nat list")
  | ImprovementEmpty

text\<open>
The new pattern grammar permits ranges wherever another pattern is expected. Here
one range occupies a struct field and another occupies a nonfinal slice element.
The old frontend's mixfix priorities cannot parse either composition.
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
old_urust_rejects
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
argument. The old grammar accepts a range only where its low-priority parse
cannot be interrupted by the argument comma.
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
old_urust_rejects
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
The shared pattern grammar admits both range forms directly, while the old
frontend's low-priority range mixfix cannot fill its high-priority binder slot.
\<close>

urust_expr improvement_while_let_range_exclusive
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 1..3 =
      \<llangle>2 :: nat\<rrangle> {
      ()
    }
  \<close>
old_urust_rejects
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
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let 1..=3 =
      \<llangle>2 :: nat\<rrangle> {
      ()
    }
  \<close>

section\<open> Structural while-let lowering \<close>

text\<open>
Structurally irrefutable patterns lower directly without a generated false
fallback. Grouping and borrow syntax are transparent, aliases bind the complete
scrutinee before applying their inner pattern, and tuple direct lowering is
reserved for tuples whose children are all irrefutable.
\<close>

urust_expr_with_check' improvement_while_let_grouped_tuple
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let ((left, right)) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>left + right\<rrangle>;
    }
  \<close>
  \<open>
    \<lbrakk>
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let (left, right) =
        (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
        \<llangle>left + right\<rrangle>;
      }
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let ((left, right)) =
      (\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>left + right\<rrangle>;
    }
  \<close>

urust_expr_with_check' improvement_while_let_refutable_tuple
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let (Some(value), other) =
      (\<llangle>Some (1 :: nat)\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
      \<llangle>value + other\<rrangle>;
    }
  \<close>
  \<open>
    \<lbrakk>
      #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let ((Some(value), other)) =
        (\<llangle>Some (1 :: nat)\<rrangle>, \<llangle>2 :: nat\<rrangle>) {
        \<llangle>value + other\<rrangle>;
      }
    \<rbrakk>
  \<close>
old_urust_rejects
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
old_urust_rejects
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
old_urust_rejects
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
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let whole @ _ =
      \<llangle>1 :: nat\<rrangle> {
      let _ = whole;
      ()
    }
  \<close>

urust_expr improvement_while_let_borrow
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let &value =
      \<llangle>1 :: nat\<rrangle> {
      let _ = value;
      ()
    }
  \<close>
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let &value =
      \<llangle>1 :: nat\<rrangle> {
      let _ = value;
      ()
    }
  \<close>

urust_expr improvement_while_let_borrow_mut
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let & mut value =
      \<llangle>1 :: nat\<rrangle> {
      let _ = value;
      ()
    }
  \<close>
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let & mut value =
      \<llangle>1 :: nat\<rrangle> {
      let _ = value;
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
old_urust_rejects
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
old_urust_rejects
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) =
      return \<llangle>Some (1 :: nat)\<rrangle> {
      let _ = value;
      ()
    }
  \<close>


section\<open> Hygienic aliases across nested lowering \<close>

text\<open>
Slice-rest patterns require generated nested matches. The new parser represents
the alias structurally, so \<open>whole\<close> remains bound to the packet rather than to
an internal list value. The old frontend captures its generated helper instead
and the expression becomes ill-typed.
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
old_urust_rejects
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


section\<open> Hygienic mutable wildcard \<close>

definition improvement_reference_fixture ::
  \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> improvement_reference_fixture \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture

text\<open>
The custom pattern AST gives \<open>let mut _\<close> the same allocated-reference term shape
as a legacy mutable name that is not used, while representing the continuation binder
as an anonymous abstraction. The old frontend has no wildcard production at this site.
\<close>

urust_expr_with_check' improvement_mutable_wildcard
  \<open>
    let keep = \<llangle>5 :: nat\<rrangle>;
    let mut _ = \<llangle>7 :: nat\<rrangle>;
    keep
  \<close>
  \<open>
    \<lbrakk>
      let keep = \<llangle>5 :: nat\<rrangle>;
      let mut ignored = \<llangle>7 :: nat\<rrangle>;
      keep
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    let keep = \<llangle>5 :: nat\<rrangle>;
    let mut _ = \<llangle>7 :: nat\<rrangle>;
    keep
  \<close>

no_adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture


section\<open> Recursive reference-prefix composition \<close>

text\<open>
The recursive reference-prefix tier accepts mixed and deeper unparenthesized
compositions. The old frontend has individual single-prefix productions and one
dedicated double-dereference production, so it requires explicit parentheses for
the equivalent mixed terms and cannot spell a triple dereference directly.
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

urust_expr_with_check' improvement_recursive_borrow_deref
  \<open> &*rr \<close>
  \<open> \<lbrakk> &(*rr) \<rbrakk> \<close>
old_urust_rejects \<open> &*rr \<close>

urust_expr_with_check' improvement_recursive_deref_mut_borrow
  \<open> *& mut r \<close>
  \<open> \<lbrakk> *(& mut r) \<rbrakk> \<close>
old_urust_rejects \<open> *& mut r \<close>

urust_expr_with_check' improvement_recursive_triple_deref
  \<open> ***rrr \<close>
  \<open> \<lbrakk> *(*(*rrr)) \<rbrakk> \<close>
old_urust_rejects \<open> ***rrr \<close>

end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Expression-antiquotation places \<close>

text\<open>
The old frontend declares an internal expression-antiquotation place constructor and
lowers it correctly, but exposes no concrete-syntax production for that constructor.
The custom parser makes the intended surface reachable. These rows compare its exact
term against the equivalent identifier-place frontend term, including capture of a
mutable local inside the antiquotation body.
\<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

context
  fixes r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
    and lhs rhs :: \<open>32 word\<close>
begin

urust_expr_with_check' improvement_antiquotation_place
  \<open> \<epsilon>\<open>\<up>r\<close> = rhs \<close>
  \<open> \<lbrakk> r = rhs \<rbrakk> \<close>
old_urust_rejects \<open> \<epsilon>\<open>\<up>r\<close> = rhs \<close>

urust_expr_with_check' improvement_antiquotation_place_capture
  \<open> let mut x = lhs; \<epsilon>\<open>\<up>x\<close> = rhs; *x \<close>
  \<open> \<lbrakk> let mut x = lhs; x = rhs; *x \<rbrakk> \<close>
old_urust_rejects \<open> let mut x = lhs; \<epsilon>\<open>\<up>x\<close> = rhs; *x \<close>

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture
no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture


section\<open> Compositional field places \<close>

text\<open>
The explicit place conversion admits a field chain whose base is a parenthesized
dereference. The old frontend declares all of those place constructors, but its
concrete grammar cannot compose a field postfix after that parenthesized base.
The accepted frontend spelling dereferences the complete field chain instead; both
lower to the same focused reference before update.
\<close>

adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture

context
  fixes rp :: \<open>(unit, unit, postfix_outer) Global_Store.ref\<close>
    and field_value :: \<open>64 word\<close>
begin

urust_expr_with_check' improvement_grouped_deref_field_place
  \<open> (*rp).inner.value = field_value \<close>
  \<open> \<lbrakk> (*rp.inner.value) = field_value \<rbrakk> \<close>
old_urust_rejects \<open> (*rp).inner.value = field_value \<close>

end

no_adhoc_overloading store_update_const \<rightleftharpoons> parser_update_fixture


section\<open> Composable postfix expressions \<close>

text\<open>
The custom parser treats propagation, fields, and methods as one left-associative
postfix tier. The old frontend requires parentheses after propagation before a method
postfix.
\<close>

context fixes self :: postfix_outer
begin
urust_expr_with_check' improvement_propagate_method
  \<open> self.optional?.to_value() \<close>
  \<open> \<lbrakk> (self.optional?).to_value() \<rbrakk> \<close>
old_urust_rejects
  \<open> self.optional?.to_value() \<close>
end


section\<open> Rust-compatible return expressions \<close>

text\<open>
Return is a low-precedence value expression whose operand and semicolon are independently
optional. The old frontend requires the semicolon as part of the return production.
\<close>

urust_expr_with_check' improvement_tail_return
  \<open> return \<close>
  \<open> \<lbrakk> return; \<rbrakk> \<close>
old_urust_rejects \<open> return \<close>

urust_expr_with_check' improvement_tail_return_value
  \<open> return \<llangle>1 :: nat\<rrangle> \<close>
  \<open> \<lbrakk> return \<llangle>1 :: nat\<rrangle>; \<rbrakk> \<close>
old_urust_rejects \<open> return \<llangle>1 :: nat\<rrangle> \<close>

urust_expr_with_check' improvement_branch_returns
  \<open>
    if \<llangle>True\<rrangle> {
      return \<llangle>1 :: nat\<rrangle>
    } else {
      return \<llangle>2 :: nat\<rrangle>
    }
  \<close>
  \<open>
    \<lbrakk>
      if \<llangle>True\<rrangle> {
        return \<llangle>1 :: nat\<rrangle>;
      } else {
        return \<llangle>2 :: nat\<rrangle>;
      }
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    if \<llangle>True\<rrangle> {
      return \<llangle>1 :: nat\<rrangle>
    } else {
      return \<llangle>2 :: nat\<rrangle>
    }
  \<close>

urust_expr_with_check' improvement_return_initializer
  \<open>
    let result = return \<llangle>1 :: nat\<rrangle>;
    result
  \<close>
  \<open>
    \<lbrakk>
      let result = { return \<llangle>1 :: nat\<rrangle>; };
      result
    \<rbrakk>
  \<close>
old_urust_rejects
  \<open>
    let result = return \<llangle>1 :: nat\<rrangle>;
    result
  \<close>

end
