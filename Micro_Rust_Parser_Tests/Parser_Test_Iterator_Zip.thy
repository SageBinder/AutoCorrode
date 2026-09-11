theory Parser_Test_Iterator_Zip
  imports
    Micro_Rust_Parser_Impl.Parser_Impl_Command
    Shallow_Micro_Rust.Eval
begin

declare [[urust_conformance_check = true]]

section\<open>Shared iterator zip\<close>

type_synonym zip_left_iterator =
  \<open>(nat list, nat, unit, unit, unit) iterator\<close>

type_synonym zip_right_iterator =
  \<open>(nat list, bool, unit, unit, unit) iterator\<close>

type_synonym zip_pair_iterator =
  \<open>(nat list, nat \<times> bool \<times> tnil, unit, unit, unit) iterator\<close>

definition zip_left_empty :: zip_left_iterator where
  \<open>zip_left_empty \<equiv> make_iterator []\<close>

definition zip_left_two :: zip_left_iterator where
  \<open>zip_left_two \<equiv> make_iterator [fun_literal 1, fun_literal 2]\<close>

definition zip_left_one :: zip_left_iterator where
  \<open>zip_left_one \<equiv> make_iterator [fun_literal 1]\<close>

definition zip_right_one :: zip_right_iterator where
  \<open>zip_right_one \<equiv> make_iterator [fun_literal True]\<close>

definition zip_right_two :: zip_right_iterator where
  \<open>zip_right_two \<equiv> make_iterator [fun_literal True, fun_literal False]\<close>

lemma iterator_zip_empty:
  shows \<open>iterator_zip zip_left_empty zip_right_two =
    fun_literal (make_iterator [])\<close>
  by (simp add: iterator_zip_def zip_left_empty_def zip_right_two_def)

lemma iterator_zip_empty_right:
  shows \<open>iterator_zip zip_left_two
    (make_iterator [] :: zip_right_iterator) =
    fun_literal (make_iterator [])\<close>
  by (simp add: iterator_zip_def zip_left_two_def)

lemma iterator_zip_equal_length:
  shows \<open>iterator_zip zip_left_two zip_right_two =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True),
       iterator_zip_thunk (fun_literal 2) (fun_literal False)])\<close>
  by (simp add: iterator_zip_def zip_left_two_def zip_right_two_def)

lemma iterator_zip_truncates_to_shorter:
  shows \<open>iterator_zip zip_left_two zip_right_one =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True)])\<close>
  by (simp add: iterator_zip_def zip_left_two_def zip_right_one_def)

lemma iterator_zip_truncates_when_left_is_shorter:
  shows \<open>iterator_zip zip_left_one zip_right_two =
    fun_literal (make_iterator
      [iterator_zip_thunk (fun_literal 1) (fun_literal True)])\<close>
  by (simp add: iterator_zip_def zip_left_one_def zip_right_two_def)

definition zip_effect_thunk ::
    \<open>nat \<Rightarrow> 'value \<Rightarrow>
     (nat list, 'value, unit, unit, unit) function_body\<close>
  where
  \<open>zip_effect_thunk marker value \<equiv> FunctionBody (
    bind (put (\<lambda>trace. trace @ [marker])) (\<lambda>_. literal value))\<close>

lemma iterator_zip_effect_order_and_single_evaluation:
  shows \<open>evaluate
    (call (iterator_zip_thunk
      (zip_effect_thunk 1 (10 :: nat))
      (zip_effect_thunk 2 True))) [] =
    Success (10, True, TNil) [1, 2]\<close>
  by (simp add: iterator_zip_thunk_def zip_effect_thunk_def call_def
      evaluate_call_function_body bind_evaluate put_def literal_def
      Core_Expression.bind.simps Core_Expression.call_function_body.simps
      evaluate_def)

text\<open>
The direct, method, and chained forms all use the normal call pipeline. The
method form contributes exactly one receiver and one explicit argument.
\<close>

urust_fn iterator_zip_direct ::
  \<open>zip_left_iterator \<Rightarrow> zip_right_iterator \<Rightarrow>
   (nat list, zip_pair_iterator, unit, unit, unit) function_body\<close>
  (left, right)
  \<open> zip(left, right) \<close>

urust_fn iterator_zip_method ::
  \<open>zip_left_iterator \<Rightarrow> zip_right_iterator \<Rightarrow>
   (nat list, zip_pair_iterator, unit, unit, unit) function_body\<close>
  (left, right)
  \<open> left.zip(right) \<close>

urust_fn iterator_zip_chained ::
  \<open>zip_left_iterator \<Rightarrow> zip_right_iterator \<Rightarrow>
   (nat list, zip_pair_iterator, unit, unit, unit) function_body\<close>
  (left, right)
  \<open> left.into_iter().zip(right.into_iter()) \<close>

thm iterator_zip_direct_conformance
thm iterator_zip_method_conformance
thm iterator_zip_chained_conformance

lemma hol_list_zip_is_unchanged:
  shows \<open>List.zip [1 :: nat, 2] [True] = [(1, True)]\<close>
  by simp

ML\<open>
local
  fun assert message condition =
    if condition then () else error message

  fun theorem_term name =
    Thm.prop_of (Proof_Context.get_thm \<^context> name)

  val iterator_zip_name = \<^const_name>\<open>iterator_zip\<close>
  val hol_zip_name = \<^const_name>\<open>List.zip\<close>
  val funcall1_name = \<^const_name>\<open>funcall1\<close>
  val funcall2_name = \<^const_name>\<open>funcall2\<close>

  fun contains_const name =
    Term.exists_subterm
      (fn Const (actual, _) => actual = name | _ => false)

  val direct = theorem_term "iterator_zip_direct_def"
  val method = theorem_term "iterator_zip_method_def"
  val chained = theorem_term "iterator_zip_chained_def"

  val _ =
    assert "direct zip did not resolve through iterator_zip notation"
      (contains_const iterator_zip_name direct)
  val _ =
    assert "method zip did not resolve through iterator_zip notation"
      (contains_const iterator_zip_name method)
  val _ =
    assert "chained zip did not resolve through iterator_zip notation"
      (contains_const iterator_zip_name chained)
  val _ =
    assert "method zip did not lower with receiver-prepended binary arity"
      (contains_const funcall2_name method)
  val _ =
    assert "chained zip lost ordinary into_iter call lowering"
      (contains_const funcall1_name chained)
  val _ =
    assert "chained zip did not lower with receiver-prepended binary arity"
      (contains_const funcall2_name chained)
  val _ =
    assert "pure HOL List.zip leaked into direct uRust call lowering"
      (not (contains_const hol_zip_name direct))
  val _ =
    assert "pure HOL List.zip leaked into method uRust call lowering"
      (not (contains_const hol_zip_name method))

  val registrations =
    Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NFunction "zip"
  val _ =
    assert "zip notation is not registered to iterator_zip"
      (exists
        (fn {hol_term, ...} => contains_const iterator_zip_name hol_term)
        registrations)

  val over_arity_source =
    Parser_Lex_Util.positioned_content_source
      "unknown.zip(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14)"
      (Position.line 1)
  val _ =
    (case Exn.result
        (fn () =>
          URust_Command.elaborate \<^context>
            {kind = URust_Command.Expression,
             source = over_arity_source,
             arguments = [],
             arguments_pos = Position.none,
             declared_type = NONE}) () of
       Exn.Res _ =>
         error "over-arity zip method unexpectedly elaborated"
     | Exn.Exn exn =>
         assert "zip method did not use structural receiver-prepending arity preflight"
           (String.isSubstring "unsupported call arity 15"
             (Runtime.exn_message exn)))
in
end
\<close>

end
