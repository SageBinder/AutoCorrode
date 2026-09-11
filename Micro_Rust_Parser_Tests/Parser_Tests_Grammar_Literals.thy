theory Parser_Tests_Grammar_Literals
  imports Parser_Tests_Improvements Parser_Tests_Negative_Conformance
begin

declare [[urust_conformance_check = true]]
declare [[urust_verbose = 0]]

section\<open>Explicit precedence tiers\<close>

adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes prefix_ref :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  fixes prefix_bool_ref :: \<open>(unit, unit, bool) Global_Store.ref\<close>
begin

urust_expr grammar_deref_before_cast
  \<open> *prefix_ref as u8 \<close>
  against \<open> \<lbrakk> (*prefix_ref) as u8 \<rbrakk> \<close>

urust_expr grammar_not_deref
  \<open> !*prefix_bool_ref \<close>
  against \<open> \<lbrakk> !(*prefix_bool_ref) \<rbrakk> \<close>

end

no_adhoc_overloading store_reference_const \<rightleftharpoons> parser_reference_fixture
no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

urust_expr grammar_if_left_operand
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
  \<close>
  against
  \<open>
    \<lbrakk>
      (if true { \<llangle>1 :: 32 word\<rrangle> }
       else { \<llangle>2 :: 32 word\<rrangle> })
      + \<llangle>3 :: 32 word\<rrangle>
    \<rbrakk>
  \<close>

urust_expr grammar_match_left_operand
  \<open>
    match true {
      true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
      false \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
    } + \<llangle>3 :: 32 word\<rrangle>
  \<close>
  against
  \<open>
    \<lbrakk>
      (match true {
        true \<Rightarrow> \<llangle>1 :: 32 word\<rrangle>,
        false \<Rightarrow> \<llangle>2 :: 32 word\<rrangle>
      }) + \<llangle>3 :: 32 word\<rrangle>
    \<rbrakk>
  \<close>

urust_expr grammar_semicolon_free_if_statement
  \<open> if true { () } else { () } () \<close>

new_urust_rejects audit
  \<open>
    if true { \<llangle>1 :: 32 word\<rrangle> }
    else { \<llangle>2 :: 32 word\<rrangle> }
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open>
    (if true { \<llangle>1 :: 32 word\<rrangle> }
     else { \<llangle>2 :: 32 word\<rrangle> })
    + \<llangle>3 :: 32 word\<rrangle>
    ()
  \<close>
  \<open> syntax error \<close>

section\<open>Match-arm separators\<close>

urust_expr [conformance_check = false] grammar_direct_with_block_arm
  \<open>
    match true {
      true \<Rightarrow> if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> }
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>

new_urust_rejects audit
  \<open>
    match true {
      true \<Rightarrow> (if true { \<llangle>1 :: nat\<rrangle> } else { \<llangle>2 :: nat\<rrangle> })
      false \<Rightarrow> \<llangle>3 :: nat\<rrangle>
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open>
    match true {
      true \<Rightarrow> return \<llangle>1 :: nat\<rrangle>;
    }
  \<close>
  \<open> syntax error found at ; \<close>

section\<open>Closures and binding RHSs\<close>

urust_expr [conformance_check = false] grammar_direct_closure_initializer
  \<open>
    let f = |x| x + \<llangle>1 :: 32 word\<rrangle>;
    ()
  \<close>

urust_expr grammar_closure_full_body
  \<open>
    |x| if true { x } else { x + \<llangle>1 :: 32 word\<rrangle> }
  \<close>

urust_expr [conformance_check = false] grammar_closure_if_let_body
  \<open>
    || if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr [conformance_check = false] grammar_closure_mixed_if_body
  \<open>
    || if true { 0 } else if let Some(x) = Some(\<llangle>1 :: nat\<rrangle>) { x } else { 0 }
  \<close>

urust_expr [conformance_check = false] grammar_closure_return_body
  \<open> || return \<llangle>1 :: nat\<rrangle> \<close>

urust_expr [conformance_check = false] grammar_nested_closure_body
  \<open> || || \<llangle>1 :: nat\<rrangle> \<close>

urust_expr [conformance_check = false] grammar_if_let_operand
  \<open>
    if let Some(value) = Some(\<llangle>1 :: 32 word\<rrangle>) {
      value
    } else {
      \<llangle>0 :: 32 word\<rrangle>
    } + \<llangle>1 :: 32 word\<rrangle>
  \<close>

urust_expr [conformance_check = false] grammar_closure_match_scrutinee
  \<open> match || true { _ \<Rightarrow> () } \<close>

urust_expr [conformance_check = false] grammar_closure_match_arms
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
  against \<open> \<lbrakk> 15_u8 \<rbrakk> \<close>
urust_expr grammar_binary_trailing_separator
  \<open> 0b1010_ \<close>
  against \<open> \<lbrakk> 10 \<rbrakk> \<close>
urust_expr grammar_octal
  \<open> 0o755 \<close>
  against \<open> \<lbrakk> 493 \<rbrakk> \<close>
urust_expr grammar_octal_suffix
  \<open> 0o17_u16 \<close>
  against \<open> \<lbrakk> 15_u16 \<rbrakk> \<close>
urust_expr grammar_octal_trailing_separator
  \<open> 0o17_ \<close>
  against \<open> \<lbrakk> 15 \<rbrakk> \<close>
urust_expr grammar_decimal_separators
  \<open> 1_000_000u32 \<close>
  against \<open> \<lbrakk> 1000000_u32 \<rbrakk> \<close>
urust_expr grammar_hex_separators
  \<open> 0xff_00u32 \<close>
  against \<open> \<lbrakk> 0xff00_u32 \<rbrakk> \<close>
urust_expr grammar_decimal_trailing_separator
  \<open> 1_ \<close>
  against \<open> \<lbrakk> 1 \<rbrakk> \<close>
urust_expr grammar_hex_trailing_separator
  \<open> 0xff_ \<close>
  against \<open> \<lbrakk> 0xff \<rbrakk> \<close>

old_urust_rejects \<open> 1_000_000u32 \<close>
old_urust_rejects \<open> 0xff_00u32 \<close>
old_urust_rejects \<open> 1_ \<close>
old_urust_rejects \<open> 0xff_ \<close>

section\<open>Struct expressions\<close>

datatype grammar_empty_struct = GrammarEmptyStruct

definition grammar_empty_struct_call ::
    \<open>(unit, grammar_empty_struct, unit, unit, unit) function_body\<close>
  where
    \<open>grammar_empty_struct_call \<equiv> FunctionBody (literal GrammarEmptyStruct)\<close>

micro_rust_notation (call) grammar_empty_struct_call ("GrammarEmptyStruct")

urust_expr grammar_empty_struct_expression
  \<open> GrammarEmptyStruct {} \<close>
  against \<open> \<lbrakk> GrammarEmptyStruct() \<rbrakk> \<close>

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

new_urust_rejects audit
  \<open> if grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open>
    if let Some(_) = grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open> if let _ = GrammarEmptyStruct {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open> for _ in grammar_empty_list_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_empty_option_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open>
    match grammar_empty_bool_value {} {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open>
    match_case grammar_empty_option_value {} {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open>
    match_switch grammar_empty_nat_value {} {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>
  \<open> syntax error \<close>

new_urust_rejects audit
  \<open> if !grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open> if true && grammar_empty_bool_value {} {} \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open>
    if false || true && !grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

new_urust_rejects audit
  \<open>
    if true == grammar_empty_bool_value {} {}
  \<close>
  \<open> empty struct expression in a control head must be parenthesized \<close>

text\<open>
Postfix propagation closes its operand before the control body begins. It therefore disambiguates
the following empty braces even when the operand path also names a registered nullary call.
True prefix operators surrounding the propagated expression retain that postfix boundary.
\<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_if
  \<open> if grammar_propagate_bool_value? {} else {} \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_if_let
  \<open>
    if let Some(_) = grammar_propagate_option_value? {} else {}
  \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_for
  \<open> for _ in grammar_propagate_list_value? {} \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      grammar_propagate_option_value? {}
  \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_match
  \<open>
    match grammar_propagate_bool_value? {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_match_case
  \<open>
    match_case grammar_propagate_option_value? {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr [conformance_check = false] grammar_propagate_empty_body_match_switch
  \<open>
    match_switch grammar_propagate_nat_value? {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

urust_expr [conformance_check = false] grammar_propagate_nested_prefix_empty_body
  \<open> if !grammar_propagate_bool_value? {} else {} \<close>

urust_expr [conformance_check = false] grammar_propagate_nested_binary_empty_body
  \<open>
    if false || grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr [conformance_check = false] grammar_propagate_nested_comparison_empty_body
  \<open>
    if true == grammar_propagate_bool_value? {} else {}
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_if
  \<open>
    if (grammar_empty_bool_value {}) {} else {}
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_if_let
  \<open>
    if let Some(_) = (grammar_empty_option_value {}) {} else {}
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_for
  \<open> for _ in (grammar_empty_list_value {}) {} \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_while_let
  \<open>
    #[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) =
      (grammar_empty_option_value {}) {}
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_match
  \<open>
    match (grammar_empty_bool_value {}) {
      true \<Rightarrow> (),
      false \<Rightarrow> ()
    }
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_match_case
  \<open>
    match_case (grammar_empty_option_value {}) {
      Some(_) \<Rightarrow> (),
      None \<Rightarrow> ()
    }
  \<close>

urust_expr [conformance_check = false] grammar_grouped_empty_struct_match_switch
  \<open>
    match_switch (grammar_empty_nat_value {}) {
      1 \<Rightarrow> (),
      _ \<Rightarrow> ()
    }
  \<close>

definition grammar_bare_flag :: bool
  where \<open>grammar_bare_flag \<equiv> True\<close>

urust_expr [conformance_check = false] grammar_bare_path_empty_body
  \<open> if grammar_bare_flag {} \<close>

urust_expr [conformance_check = false] grammar_bare_path_empty_body_sequence
  \<open> if grammar_bare_flag {} {} \<close>

urust_expr [conformance_check = false] grammar_nested_bare_path_empty_body_sequence
  \<open> if true && grammar_bare_flag {} {} \<close>

context fixes flag :: bool
begin

urust_expr [conformance_check = false] grammar_fixed_path_empty_body_sequence
  \<open> if flag {} {} \<close>

end

urust_expr [conformance_check = false] grammar_struct_trailing_comma
  \<open>
    D21Pair {
      second: 2_u64,
      first: 1_u64,
    }
  \<close>

section\<open>AST and grammar-shape audit\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>
    fun parse source =
      (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source source) of
         SOME expression => expression
       | NONE => error "expected a nonempty uRust expression")
    fun assert message true = ()
      | assert message false = error message
  in
    val _ =
      (case parse "*x as usize" of
         UE_Cast (UE_Unary (U_Deref, UE_Path _, _), CT_Unsigned UT_Usize, _) => ()
       | _ => error "unary-before-cast AST shape changed")
    val _ =
      (case parse "!*p" of
         UE_Unary (U_Not, UE_Unary (U_Deref, UE_Path _, _), _) => ()
       | _ => error "mixed not/dereference prefix shape changed")
    val _ =
      (case parse "*& mut r" of
         UE_Unary
           (U_Deref, UE_Unary (U_Borrow BM_Mut, UE_Path _, _), _) => ()
       | _ => error "mixed dereference/mutable-borrow prefix shape changed")
    val _ =
      (case parse "&!x" of
         UE_Unary (U_Borrow BM_Imm, UE_Unary (U_Not, UE_Path _, _), _) => ()
       | _ => error "mixed borrow/not prefix shape changed")
    val _ =
      (case parse "**p" of
         UE_Unary (U_Deref, UE_Unary (U_Deref, UE_Path _, _), _) => ()
       | _ => error "repeated dereference prefix shape changed")
    val _ =
      (case parse "if true { 1 } else { 2 } + 3" of
         UE_Bin (Add, UE_If _, UE_Literal _, _) => ()
       | _ => error "direct with-block operand AST shape changed")
    val _ =
      (case parse "if true { () } else { () } ()" of
         UE_Seq (UE_If _, UE_Unit _) => ()
       | _ => error "semicolon-free direct with-block statement shape changed")
    val _ =
      (case parse "0b10_01u8" of
         UE_Literal (LP_Integer ("0b10_01u8", _)) => ()
       | _ => error "integer literal raw spelling was not retained")
    val _ =
      (case parse "GrammarEmptyStruct {}" of
         UE_Struct (_, [], _) => ()
       | _ => error "empty struct expression AST shape changed")
    val _ =
      (case parse "AdvStruct { adv_right: 2, adv_left: 1, }" of
         UE_Struct
           (_, [SE_Field ("adv_right", _, _), SE_Field ("adv_left", _, _)], _) => ()
       | _ => error "struct field source order or trailing-comma shape changed")
    val _ =
      (case parse "r = match flag { true => lhs, false => rhs }" of
         UE_Assign (Assign, _, UE_Match _, _) => ()
       | _ => error "direct match assignment RHS shape changed")
    val _ =
      (case parse "r += if flag { lhs } else { rhs }" of
         UE_Assign (AssignAdd, _, UE_If _, _) => ()
       | _ => error "direct conditional compound-assignment RHS shape changed")
    val _ =
      (case parse "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } == ()" of
         UE_Bin (Eq, UE_Loop _, UE_Unit _, _) => ()
       | _ => error "direct loop binary-operand shape changed")
    val _ =
      (case parse "for value in \<llangle>[1 :: nat]\<rrangle> { () } == ()" of
         UE_Bin (Eq, UE_For _, UE_Unit _, _) => ()
       | _ => error "direct for-loop binary-operand shape changed")
    val _ =
      (case parse
          "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(value) = \<llangle>Some (1 :: nat)\<rrangle> { () } == ()" of
         UE_Bin (Eq, UE_WhileLet _, UE_Unit _, _) => ()
       | _ => error "direct while-let binary-operand shape changed")
    val _ =
      (case parse "target = || 1" of
         UE_Assign (Assign, _, UE_Closure _, _) => ()
       | _ => error "closure assignment RHS shape changed")
    val _ =
      (case parse "|| target = 1" of
         UE_Closure (_, UE_Assign (Assign, _, _, _), _) => ()
       | _ => error "assignment closure-body shape changed")
    val _ =
      (case parse "|| #[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }" of
         UE_Closure (_, UE_Loop _, _) => ()
       | _ => error "loop closure-body shape changed")
    val _ =
      (case parse "|| (); ()" of
         UE_Seq (UE_Closure (_, UE_Unit _, _), UE_Unit _) => ()
       | _ => error "closure statement sequencing shape changed")
    val _ =
      (case parse "|| \<llangle>1 :: nat\<rrangle>; ()" of
         UE_Seq (UE_Closure (_, UE_Literal _, _), UE_Unit _) => ()
       | _ => error "closure left-sequencing shape changed")
    val literal_text = "0b10_01u8"
    val literal_start =
      Position.make0 23 400 0 "" "" "grammar-literal-markup-audit"
    val literal_stop =
      Position.symbol_explode literal_text literal_start
    val captured_reports =
      Synchronized.var "grammar_literal_reports" ([] : string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                (case URust_Parser.parse_source ctxt
                    (Parser_Lex_Util.positioned_content_source
                      literal_text literal_start) of
                   SOME _ => ()
                 | NONE => error "integer markup audit parsed empty input")) ())
          ())
    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val literal_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun property_matches name value properties =
      Properties.get properties name = Option.map Value.print_int value
    val _ =
      assert "integer candidate lost whole-token numeral markup"
        (exists
          (fn (name, properties) =>
            name = Markup.numeralN andalso
              property_matches Markup.offsetN
                (Position.offset_of literal_start) properties andalso
              property_matches Markup.end_offsetN
                (Position.offset_of literal_stop) properties)
          literal_markup)
    val _ =
      (case Exn.result
          (Parser_Test_Elaboration.expression ctxt)
          (Parser_Lex_Util.text_source "0b102u32") of
         Exn.Exn exn =>
           assert "malformed integer candidate changed diagnostic"
             (String.isSubstring
               "cannot read integer literal \"0b102u32\""
               (Runtime.exn_message exn))
       | Exn.Res _ => error "malformed integer candidate was accepted")
    val _ =
      (case parse "0x2a" of
         UE_Literal (LP_Integer ("0x2a", _)) => ()
       | _ => error "integer parser did not recover after malformed input")
    val _ = assert "ordinary/no-struct audit fixture did not run" true
  end
\<close>

end
