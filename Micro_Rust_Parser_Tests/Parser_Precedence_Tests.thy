theory Parser_Precedence_Tests
  imports Parser_Expression_Tests
begin

declare [[urust_verbosity = 0]]

section\<open>Rust dereference and postfix precedence\<close>

text\<open>
Postfix operators bind before dereference. Grouping the complete operand makes that boundary
explicit; grouping the dereference instead selects dereference-before-index. These checked
equations cover the index and grouped/call field shapes whose migration compatibility previously
changed their meaning.
\<close>

datatype_record deref_postfix_fixture =
  deref_postfix_fixture_field :: \<open>(unit, unit, 64 word) Global_Store.ref\<close>
micro_rust_record deref_postfix_fixture (deref_postfix_fixture_field = "field")

definition deref_postfix_identity ::
    \<open>deref_postfix_fixture \<Rightarrow>
      (unit, deref_postfix_fixture, unit, unit, unit) function_body\<close>
  where \<open> deref_postfix_identity \<equiv> lift_fun1 (\<lambda>value. value) \<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes references :: \<open>(unit, unit, 64 word) Global_Store.ref list\<close>
    and base :: deref_postfix_fixture
    and array_ref :: \<open>(unit, unit, (64 word, 4) array) Global_Store.ref\<close>
begin

urust_expr precedence_index_operand \<open> *references[0_usize] \<close>
urust_expr precedence_grouped_index_operand \<open> *(references[0_usize]) \<close>

lemma precedence_index_grouping:
  \<open>precedence_index_operand = precedence_grouped_index_operand\<close>
  unfolding precedence_index_operand_def precedence_grouped_index_operand_def by (rule refl)

urust_expr precedence_grouped_field_operand \<open> *(base).field \<close>
urust_expr precedence_explicit_grouped_field_operand \<open> *((base).field) \<close>

lemma precedence_grouped_field_grouping:
  \<open>precedence_grouped_field_operand = precedence_explicit_grouped_field_operand\<close>
  unfolding precedence_grouped_field_operand_def
    precedence_explicit_grouped_field_operand_def by (rule refl)

urust_expr precedence_call_field_operand \<open> *deref_postfix_identity(base).field \<close>
urust_expr precedence_grouped_call_field_operand \<open> *(deref_postfix_identity(base).field) \<close>

lemma precedence_call_field_grouping:
  \<open>precedence_call_field_operand = precedence_grouped_call_field_operand\<close>
  unfolding precedence_call_field_operand_def precedence_grouped_call_field_operand_def by (rule refl)

urust_expr precedence_simple_field_operand \<open> *base.field \<close>
urust_expr precedence_grouped_simple_field_operand \<open> *(base.field) \<close>

lemma precedence_simple_field_grouping:
  \<open>precedence_simple_field_operand = precedence_grouped_simple_field_operand\<close>
  unfolding precedence_simple_field_operand_def precedence_grouped_simple_field_operand_def by (rule refl)

urust_expr precedence_group_deref_before_index \<open> (*array_ref)[0_usize] \<close>

end

context
  fixes flags :: \<open>(unit, unit, bool) Global_Store.ref list\<close>
begin

urust_expr precedence_control_head \<open> if *flags[0_usize] { true } else { false } \<close>
urust_expr precedence_grouped_control_head
  \<open> if *(flags[0_usize]) { true } else { false } \<close>

lemma precedence_control_head_grouping:
  \<open>precedence_control_head = precedence_grouped_control_head\<close>
  unfolding precedence_control_head_def precedence_grouped_control_head_def by (rule refl)

end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

section\<open>Both expression families and assignment places\<close>

ML_val\<open>
  let
    open URust_AST
    val ctxt = \<^context>
    fun parse text =
      (case URust_Parser.parse_source ctxt (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "precedence audit: empty parse")
    fun indexed_operand (UE_Unary (U_Deref, UE_Index (UE_Path _, UE_Path _, _), _)) = true
      | indexed_operand _ = false
    fun assert label condition =
      if condition then () else error ("precedence audit: " ^ label)
    val _ = assert "ordinary expression" (indexed_operand (parse "*base[index]"))
    val _ =
      (case parse "if *base[index] { () }" of
         UE_If (condition, _, _, _) => assert "if head" (indexed_operand condition)
       | _ => error "precedence audit: if shape")
    val _ =
      (case parse "if let Some(item) = *base[index] { item }" of
         UE_IfLet (_, value, _, _, _) => assert "if-let head" (indexed_operand value)
       | _ => error "precedence audit: if-let shape")
    val _ =
      (case parse "match *base[index] { _ => () }" of
         UE_Match (_, value, _, _) => assert "match head" (indexed_operand value)
       | _ => error "precedence audit: match shape")
    val _ =
      (case parse "for item in *base[index] { () }" of
         UE_For (_, value, _, _) => assert "for head" (indexed_operand value)
       | _ => error "precedence audit: for shape")
    val _ =
      (case parse "if *(base).field { () }" of
         UE_If (UE_Unary (U_Deref, UE_Field (UE_Group _, "field", _), _), _, _, _) => ()
       | _ => error "precedence audit: grouped field in control head")
    val _ =
      (case parse "if *make().field { () }" of
         UE_If (UE_Unary (U_Deref, UE_Field (UE_Call _, "field", _), _), _, _, _) => ()
       | _ => error "precedence audit: call field in control head")
    val _ =
      (case parse "**base[index]" of
         UE_Unary (U_Deref, operand, _) => assert "repeated dereference" (indexed_operand operand)
       | _ => error "precedence audit: repeated dereference shape")
    val _ =
      (case parse "*base[index] as u64 + tail" of
         UE_Bin (Add, UE_Cast (operand, CT_Unsigned UT_U64, _), UE_Path _, _) =>
           assert "cast and binary boundary" (indexed_operand operand)
       | _ => error "precedence audit: cast and binary shape")
    val _ =
      (case parse "&*base[index]" of
         UE_Unary (U_Borrow BM_Imm, operand, _) =>
           assert "borrow boundary" (indexed_operand operand)
       | _ => error "precedence audit: borrow shape")
    val _ =
      (case parse "*base[index] = value" of
         UE_Assign (Assign, UP_Deref (UE_Index (UE_Path _, UE_Path _, _), _), UE_Path _, _) => ()
       | _ => error "precedence audit: indexed dereference assignment place")
    val _ =
      (case parse "(*base)[index] = value" of
         UE_Assign (Assign, UP_Index (UP_Deref (UE_Path _, _), UE_Path _, _), UE_Path _, _) => ()
       | _ => error "precedence audit: explicitly grouped assignment place")
    val _ =
      (case parse "*base[index].field.0.method()?" of
         UE_Unary
           (U_Deref,
            UE_Unary
              (U_Propagate,
               UE_Call
                 (UC_Method
                   (UE_TupleProjection
                     (UE_Field (UE_Index _, "field", _), 0, _),
                    Path_Segment ("method", _, _)),
                  [], _),
               _),
            _) => ()
       | _ => error "precedence audit: complete postfix chain")
  in () end
\<close>

end
