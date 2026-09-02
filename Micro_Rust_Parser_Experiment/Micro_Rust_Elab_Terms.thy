theory Micro_Rust_Elab_Terms
  imports
    Micro_Rust_Parser_AST
    Shallow_Micro_Rust.Bool_Type_Lemmas
    Shallow_Micro_Rust.Core_Expression_Lemmas
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
    Shallow_Micro_Rust.Numeric_Types_Lemmas
begin

section\<open> Shallow term vocabulary \<close>

subsection\<open> Semantic matcher runtime \<close>

type_synonym
  ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
    urust_matcher =
  \<open>
    'a \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression
  \<close>

definition urust_matcher_fail ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open> urust_matcher_fail value success failure = failure \<close>

definition urust_matcher_succeed ::
  \<open>
    ('a \<Rightarrow> 'payload) \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_succeed payload value success failure =
      success (payload value) failure
  \<close>

definition urust_matcher_choice ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_choice left right value success failure =
      left value success (right value success failure)
  \<close>

definition urust_matcher_map ::
  \<open>
    ('a \<Rightarrow> 'payload \<Rightarrow> 'mapped) \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'mapped, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_map mapping matcher value success failure =
      matcher value
        (\<lambda>payload remaining. success (mapping value payload) remaining)
        failure
  \<close>

definition urust_matcher_product ::
  \<open>
    ('s, 'a, 'left_payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'b, 'right_payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a \<times> 'b, 'left_payload \<times> 'right_payload,
      'value, 'return, 'abort, 'input, 'output) urust_matcher
  \<close>
where
  \<open>
    urust_matcher_product left right values success failure =
      left (fst values)
        (\<lambda>left_payload remaining_left.
          right (snd values)
            (\<lambda>right_payload remaining_right.
              success (left_payload, right_payload) remaining_right)
            remaining_left)
        failure
  \<close>

definition urust_matcher_test ::
  \<open>
    ('a \<Rightarrow>
      ('s, bool, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'a, 'a, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_test predicate value success failure =
      two_armed_conditional
        (predicate value) (success value failure) failure
  \<close>

definition urust_matcher_lift ::
  \<open>
    ('a \<Rightarrow>
      ('s, 'b, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'b, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_lift lifting matcher value success failure =
      bind (lifting value) (\<lambda>lifted. matcher lifted success failure)
  \<close>

definition urust_matcher_destructure ::
  \<open>
    ('a \<Rightarrow>
      ('b \<Rightarrow>
        ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'b, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher
  \<close>
where
  \<open>
    urust_matcher_destructure selector matcher value success failure =
      selector value
        (\<lambda>fields. matcher fields success failure)
        failure
  \<close>

definition urust_matcher_run ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression
  \<close>
where
  \<open>
    urust_matcher_run matcher scrutinee success failure =
      bind scrutinee
        (\<lambda>value.
          matcher value (\<lambda>payload remaining. success payload) failure)
  \<close>

definition urust_matcher_run_guarded ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    ('s, 'a, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, bool, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression
  \<close>
where
  \<open>
    urust_matcher_run_guarded matcher scrutinee guard success failure =
      bind scrutinee
        (\<lambda>value.
          matcher value
            (\<lambda>payload remaining.
              two_armed_conditional
                (guard payload) (success payload) failure)
            failure)
  \<close>

definition urust_matcher_run_value ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    'a \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression
  \<close>
where
  \<open>
    urust_matcher_run_value matcher value success failure =
      matcher value (\<lambda>payload remaining. success payload) failure
  \<close>

definition urust_matcher_run_guarded_value ::
  \<open>
    ('s, 'a, 'payload, 'value, 'return, 'abort, 'input, 'output)
      urust_matcher \<Rightarrow>
    'a \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, bool, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('payload \<Rightarrow>
      ('s, 'value, 'return, 'abort, 'input, 'output) expression) \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression \<Rightarrow>
    ('s, 'value, 'return, 'abort, 'input, 'output) expression
  \<close>
where
  \<open>
    urust_matcher_run_guarded_value
        matcher value guard success failure =
      matcher value
        (\<lambda>payload remaining.
          two_armed_conditional
            (guard payload) (success payload) failure)
        failure
  \<close>

named_theorems urust_matcher_evaluation
named_theorems urust_matcher_conformance
named_theorems urust_matcher_code

declare
  urust_matcher_fail_def
  urust_matcher_succeed_def
  urust_matcher_choice_def
  urust_matcher_map_def
  urust_matcher_product_def
  urust_matcher_test_def
  urust_matcher_lift_def
  urust_matcher_destructure_def
  urust_matcher_run_def
  urust_matcher_run_guarded_def
  urust_matcher_run_value_def
  urust_matcher_run_guarded_value_def
  [urust_matcher_code]

lemma urust_matcher_run_fail [urust_matcher_conformance]:
  \<open>
    urust_matcher_run urust_matcher_fail scrutinee success failure =
      bind scrutinee (\<lambda>_. failure)
  \<close>
  by (simp add: urust_matcher_run_def urust_matcher_fail_def)

lemma urust_matcher_run_succeed [urust_matcher_conformance]:
  \<open>
    urust_matcher_run (urust_matcher_succeed payload)
      scrutinee success failure =
      bind scrutinee (\<lambda>value. success (payload value))
  \<close>
  by (simp add: urust_matcher_run_def urust_matcher_succeed_def)

lemma urust_matcher_run_guarded_fail [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded urust_matcher_fail
      scrutinee guard success failure =
      bind scrutinee (\<lambda>_. failure)
  \<close>
  by (simp add:
    urust_matcher_run_guarded_def urust_matcher_fail_def)

lemma urust_matcher_run_guarded_succeed [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded (urust_matcher_succeed payload)
      scrutinee guard success failure =
      bind scrutinee
        (\<lambda>value.
          two_armed_conditional
            (guard (payload value)) (success (payload value)) failure)
  \<close>
  by (simp add:
    urust_matcher_run_guarded_def urust_matcher_succeed_def)

lemma urust_matcher_run_value_fail [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_value urust_matcher_fail
      value success failure =
      failure
  \<close>
  by (simp add:
    urust_matcher_run_value_def urust_matcher_fail_def)

lemma urust_matcher_run_value_succeed [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_value (urust_matcher_succeed payload)
      value success failure =
      success (payload value)
  \<close>
  by (simp add:
    urust_matcher_run_value_def urust_matcher_succeed_def)

lemma urust_matcher_run_guarded_value_fail
    [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded_value urust_matcher_fail
      value guard success failure =
      failure
  \<close>
  by (simp add:
    urust_matcher_run_guarded_value_def urust_matcher_fail_def)

lemma urust_matcher_run_guarded_value_succeed
    [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded_value
      (urust_matcher_succeed payload)
      value guard success failure =
      two_armed_conditional
        (guard (payload value)) (success (payload value)) failure
  \<close>
  by (simp add:
    urust_matcher_run_guarded_value_def urust_matcher_succeed_def)

lemma evaluate_urust_matcher_run [urust_matcher_evaluation]:
  \<open>
    evaluate (urust_matcher_run matcher scrutinee success failure) state =
      (case evaluate scrutinee state of
        Success value state' \<Rightarrow>
          evaluate
            (matcher value
              (\<lambda>payload remaining. success payload) failure)
            state'
      | Return result state' \<Rightarrow> Return result state'
      | Abort reason state' \<Rightarrow> Abort reason state'
      | Yield request state' continuation \<Rightarrow>
          Yield request state'
            (\<lambda>response.
              bind (continuation response)
                (\<lambda>value.
                  matcher value
                    (\<lambda>payload remaining. success payload)
                    failure)))
  \<close>
  by (simp add: urust_matcher_run_def bind_evaluate)

lemma evaluate_urust_matcher_lift [urust_matcher_evaluation]:
  \<open>
    evaluate
      (urust_matcher_lift lifting matcher value success failure)
      state =
      (case evaluate (lifting value) state of
        Success lifted state' \<Rightarrow>
          evaluate (matcher lifted success failure) state'
      | Return result state' \<Rightarrow> Return result state'
      | Abort reason state' \<Rightarrow> Abort reason state'
      | Yield request state' continuation \<Rightarrow>
          Yield request state'
            (\<lambda>response.
              bind (continuation response)
                (\<lambda>lifted. matcher lifted success failure)))
  \<close>
  by (simp add: urust_matcher_lift_def bind_evaluate)

lemma urust_matcher_choice_left_to_right [urust_matcher_conformance]:
  \<open>
    urust_matcher_choice left right value success failure =
      left value success (right value success failure)
  \<close>
  by (simp add: urust_matcher_choice_def)

lemma urust_matcher_product_backtracks [urust_matcher_conformance]:
  \<open>
    urust_matcher_product left right values success failure =
      left (fst values)
        (\<lambda>left_payload remaining_left.
          right (snd values)
            (\<lambda>right_payload remaining_right.
              success (left_payload, right_payload) remaining_right)
            remaining_left)
        failure
  \<close>
  by (simp add: urust_matcher_product_def)

lemma urust_matcher_destructure_selects [urust_matcher_conformance]:
  \<open>
    urust_matcher_destructure selector matcher value success failure =
      selector value
        (\<lambda>fields. matcher fields success failure)
        failure
  \<close>
  by (simp add: urust_matcher_destructure_def)

lemma urust_matcher_guard_false_skips_alternatives
    [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded matcher scrutinee guard success failure =
      bind scrutinee
        (\<lambda>value.
          matcher value
            (\<lambda>payload remaining.
              two_armed_conditional
                (guard payload) (success payload) failure)
            failure)
  \<close>
  by (simp add: urust_matcher_run_guarded_def)

lemma urust_matcher_guard_false_skips_value_alternatives
    [urust_matcher_conformance]:
  \<open>
    urust_matcher_run_guarded_value
      matcher value guard success failure =
      matcher value
        (\<lambda>payload remaining.
          two_armed_conditional
            (guard payload) (success payload) failure)
        failure
  \<close>
  by (simp add: urust_matcher_run_guarded_value_def)

ML\<open>
signature URUST_ELAB_TERMS =
sig
  val literal: term -> term
  val boolean_expression: bool -> term
  val string_value: string -> Position.T -> term
  val integer_value: Position.T -> string -> term

  val function_call: Position.T -> term -> term list -> term
  val bind: term -> term -> term
  val sequence: term -> term -> term
  val return_value: term -> term
  val case_product: term -> term
  val allocate_reference: Position.T -> term -> term
  val update: Position.T -> term -> term -> term
  val assign_add: Position.T -> term -> term -> term
  val focus_field: term -> term -> term
  val tuple: term list -> term
  val conditional: term -> term -> term -> term
  val bounded_while: term -> term -> term -> term
  val bounded_loop: term -> term -> term
  val for_loop: term -> term -> term
  val into_iterator: term -> term
  val skip: term
  val binary: URust_AST.binop -> term -> term -> term
  val unary: URust_AST.unaryop -> Position.T -> term -> term
  val assignment_binary: URust_AST.assign_binop -> term -> term -> term

  val option_some: term -> term
  val option_none: term
  val pair: term -> term -> term
  val list_cons: term -> term -> term
  val list_nil: term
  val numeral_case_selector: term -> term
  val reverse_list: term -> term

  val true_value: term
  val false_value: term
  val undefined_value: term
  val list_cons_constructor: term
  val list_nil_constructor: term
  val pair_constructor: term
  val tuple_nil_constructor: term

  val case_guard: term -> term -> term -> term
  val case_cons: term -> term -> term
  val case_nil: term
  val case_element: term -> term -> term
  val case_abstraction: term -> term

  val matcher_fail: term
  val matcher_succeed: term -> term
  val matcher_choice: term -> term -> term
  val matcher_map: term -> term -> term
  val matcher_product: term -> term -> term
  val matcher_test: term -> term
  val matcher_lift: term -> term -> term
  val matcher_destructure: term -> term -> term
  val matcher_run: term -> term -> term -> term -> term
  val matcher_run_guarded:
    term -> term -> term -> term -> term -> term
  val matcher_run_value: term -> term -> term -> term -> term
  val matcher_run_guarded_value:
    term -> term -> term -> term -> term -> term
end
\<close>

text\<open>
This module owns the pure vocabulary used to construct the existing shallow embedding. All terms use
\<open>dummyT\<close>; the command layer still performs the single final \<open>Syntax.check_term\<close>.
\<close>

ML\<open>
structure URust_Elab_Terms : URUST_ELAB_TERMS =
struct
  open URust_AST

  fun constant name args = Term.list_comb (Const (name, dummyT), args)

  (* Direct check_term input uses the post-parse representation of source positions: an internal type
     constraint whose TFree is decoded by Type_Infer_Context.prepare_positions. *)
  fun positioned_constant name pos args =
    let val posT = TFree (Term_Position.encode_syntax [pos], dummyS)
    in Term.list_comb (Type.constraint posT (Const (name, dummyT)), args) end

  fun literal value = constant \<^const_name>\<open>literal\<close> [value]
  fun bindlift1 f expression = constant \<^const_name>\<open>bindlift1\<close> [f, expression]

  fun boolean_expression value =
    Const (if value then \<^const_name>\<open>Bool_Type.true\<close>
           else \<^const_name>\<open>Bool_Type.false\<close>, dummyT)

  fun string_value raw pos =
    let
      fun bit value =
        Const (if value = 1 then \<^const_name>\<open>True\<close>
               else \<^const_name>\<open>False\<close>, dummyT)
      fun character c =
        constant \<^const_name>\<open>Char\<close>
          (map bit (Integer.radicify 2 8 (String_Syntax.ascii_ord_of c)))
      val characters = map fst (Lexicon.explode_string (raw, pos))
      val list =
        fold_rev (fn c => fn rest =>
            constant \<^const_name>\<open>List.Cons\<close> [character c, rest])
          characters (Const (\<^const_name>\<open>List.Nil\<close>, dummyT))
    in constant \<^const_name>\<open>String.implode\<close> [list] end

  (* The frontend surface supports arities 0..14. Keep every HOL target compile-checked. *)
  val function_constants = Vector.fromList
    [\<^const_name>\<open>funcall0\<close>,  \<^const_name>\<open>funcall1\<close>,
     \<^const_name>\<open>funcall2\<close>,  \<^const_name>\<open>funcall3\<close>,
     \<^const_name>\<open>funcall4\<close>,  \<^const_name>\<open>funcall5\<close>,
     \<^const_name>\<open>funcall6\<close>,  \<^const_name>\<open>funcall7\<close>,
     \<^const_name>\<open>funcall8\<close>,  \<^const_name>\<open>funcall9\<close>,
     \<^const_name>\<open>funcall10\<close>, \<^const_name>\<open>funcall11\<close>,
     \<^const_name>\<open>funcall12\<close>, \<^const_name>\<open>funcall13\<close>,
     \<^const_name>\<open>funcall14\<close>]
  val maximum_function_arity = Vector.length function_constants - 1

  fun function_constant pos arity =
    if 0 <= arity andalso arity <= maximum_function_arity
    then Vector.sub (function_constants, arity)
    else
      error ("urust_expr: unsupported call arity " ^ string_of_int arity ^ " (max " ^
        string_of_int maximum_function_arity ^
        "; the frontend's surface lowering caps here)" ^ Position.here pos)

  fun function_call pos function arguments =
    constant (function_constant pos (length arguments)) (function :: arguments)

  (* Integer-literal suffix knowledge has one owner. *)
  val integer_suffix_types =
    [("u8", \<^typ>\<open>8 word\<close>),
     ("u16", \<^typ>\<open>16 word\<close>),
     ("u32", \<^typ>\<open>32 word\<close>),
     ("u64", \<^typ>\<open>64 word\<close>),
     ("usize", \<^typ>\<open>64 word\<close>)]

  fun integer_suffix_type suffix =
    AList.lookup (op =) integer_suffix_types suffix

  val supported_integer_suffixes =
    space_implode " " (map fst integer_suffix_types)

  fun is_decimal_digit c = #"0" <= c andalso c <= #"9"
  fun is_hex_digit c =
    is_decimal_digit c orelse
    (#"a" <= c andalso c <= #"f") orelse
    (#"A" <= c andalso c <= #"F")

  fun scan_while predicate text start =
    if start < size text andalso predicate (String.sub (text, start))
    then scan_while predicate text (start + 1)
    else start

  fun split_integer_lexeme pos lexeme =
    let
      val hex = String.isPrefix "0x" lexeme
      val number_end =
        if hex then scan_while is_hex_digit lexeme 2
        else scan_while is_decimal_digit lexeme 0
      val _ =
        if number_end = (if hex then 2 else 0)
        then
          error ("urust_expr: cannot read integer literal " ^ quote lexeme ^
            Position.here pos)
        else ()
      val number_text = String.substring (lexeme, 0, number_end)
      val suffix_spelling = String.extract (lexeme, number_end, NONE)
      val suffix =
        if String.isPrefix "_" suffix_spelling
        then String.extract (suffix_spelling, 1, NONE)
        else suffix_spelling
    in (number_text, suffix_spelling, suffix) end

  fun parse_integer pos lexeme =
    let
      val (number_text, suffix_spelling, suffix) =
        split_integer_lexeme pos lexeme
      val value =
        (case (if String.isPrefix "0x" number_text
               then StringCvt.scanString (Int.scan StringCvt.HEX)
                 (String.extract (number_text, 2, NONE))
               else Int.fromString number_text) of
           SOME value => value
         | NONE =>
             error ("urust_expr: cannot read integer literal " ^ quote number_text ^
               Position.here pos))
    in
      if suffix_spelling = ""
      then (value, NONE)
      else
        (case integer_suffix_type suffix of
           SOME typ => (value, SOME typ)
         | NONE =>
             error ("urust_expr: unsupported integer-literal suffix " ^
               quote suffix_spelling ^
               " (supported: " ^ supported_integer_suffixes ^
               "; optional compatibility underscore)" ^
               Position.here (Position.symbol_explode number_text pos)))
    end

  fun integer_value pos lexeme =
    (case parse_integer pos lexeme of
       (value, NONE) => HOLogic.mk_number dummyT value
     | (value, SOME typ) => HOLogic.mk_number typ value)

  (* Sequencing must use sequence: replacing it with an anonymous bind changes the generated term. *)
  fun bind expression abstraction =
    constant \<^const_name>\<open>Core_Expression.bind\<close> [expression, abstraction]
  fun sequence first second =
    constant \<^const_name>\<open>Core_Expression.sequence\<close> [first, second]
  fun return_value value = constant \<^const_name>\<open>return_func\<close> [value]
  fun case_product abstraction = constant \<^const_name>\<open>case_prod\<close> [abstraction]

  fun allocate_reference pos expression =
    constant \<^const_name>\<open>funcall1\<close>
      [positioned_constant \<^const_name>\<open>store_reference_const\<close> pos [], expression]

  fun borrow mode pos expression =
    bindlift1
      (positioned_constant
        (case mode of
           BM_Imm => \<^const_name>\<open>ro_ref_from_ref\<close>
         | BM_Mut => \<^const_name>\<open>mut_ref_from_ref\<close>)
        pos [])
      expression

  fun dereference pos expression =
    bind expression
      (constant \<^const_name>\<open>deep_compose1\<close>
        [Const (\<^const_name>\<open>call\<close>, dummyT),
         positioned_constant \<^const_name>\<open>store_dereference_const\<close> pos []])

  fun update pos place rhs =
    constant \<^const_name>\<open>bind2\<close>
      [constant \<^const_name>\<open>deep_compose2\<close>
        [Const (\<^const_name>\<open>call\<close>, dummyT),
         positioned_constant \<^const_name>\<open>store_update_const\<close> pos []],
       place, rhs]

  fun assign_add pos place rhs =
    constant \<^const_name>\<open>funcall2\<close>
      [positioned_constant \<^const_name>\<open>assign_add_const\<close> pos [], place, rhs]

  fun focus_field field receiver =
    bindlift1 (constant \<^const_name>\<open>focus_lens_const\<close> [field]) receiver

  fun tuple_lift terminal first second =
    let
      val x = Free ("x", dummyT)
      val y = Free ("y", dummyT)
      fun pair_term left right =
        constant \<^const_name>\<open>Product_Type.Pair\<close> [left, right]
      val result =
        if terminal
        then pair_term x (pair_term y (Const (\<^const_name>\<open>TNil\<close>, dummyT)))
        else pair_term x y
      val abstraction = Term.lambda x (Term.lambda y result)
    in constant \<^const_name>\<open>bindlift2\<close> [abstraction, first, second] end

  fun tuple [first, second] = tuple_lift true first second
    | tuple (first :: rest) = tuple_lift false first (tuple rest)
    | tuple _ = error "urust_expr: internal tuple with fewer than two elements"

  fun conditional condition then_branch else_branch =
    constant \<^const_name>\<open>two_armed_conditional\<close>
      [condition, then_branch, else_branch]

  fun bounded_while fuel condition body =
    constant \<^const_name>\<open>bounded_while\<close> [fuel, condition, body]

  fun bounded_loop fuel body =
    bounded_while fuel
      (literal (Const (\<^const_name>\<open>True\<close>, dummyT))) body

  fun for_loop iterator body =
    constant \<^const_name>\<open>for_loop\<close> [iterator, body]

  fun into_iterator iterable =
    constant \<^const_name>\<open>funcall1\<close>
      [Const (\<^const_name>\<open>into_iter\<close>, dummyT), iterable]

  val skip = literal HOLogic.unit

  fun propagate pos expression =
    positioned_constant \<^const_name>\<open>propagate_const\<close> pos [expression]

  fun unary U_Not _ expression =
        constant \<^const_name>\<open>negation_const\<close> [expression]
    | unary (U_Borrow mode) pos expression = borrow mode pos expression
    | unary U_Deref pos expression = dereference pos expression
    | unary U_Propagate pos expression = propagate pos expression

  fun binary_constant Add = \<^const_name>\<open>urust_add\<close>
    | binary_constant Sub = \<^const_name>\<open>word_minus_no_wrap\<close>
    | binary_constant Mul = \<^const_name>\<open>word_mul_no_wrap\<close>
    | binary_constant Div = \<^const_name>\<open>word_udiv\<close>
    | binary_constant Mod = \<^const_name>\<open>word_umod\<close>
    | binary_constant Shl = \<^const_name>\<open>word_shift_left_shift64\<close>
    | binary_constant Shr = \<^const_name>\<open>word_shift_right_shift64\<close>
    | binary_constant BAnd = \<^const_name>\<open>word_bitwise_and\<close>
    | binary_constant BOr = \<^const_name>\<open>word_bitwise_or\<close>
    | binary_constant BXor = \<^const_name>\<open>word_bitwise_xor\<close>
    | binary_constant Eq = \<^const_name>\<open>urust_eq\<close>
    | binary_constant Ne = \<^const_name>\<open>urust_neq\<close>
    | binary_constant Lt = \<^const_name>\<open>comp_lt\<close>
    | binary_constant Le = \<^const_name>\<open>comp_le\<close>
    | binary_constant Gt = \<^const_name>\<open>comp_gt\<close>
    | binary_constant Ge = \<^const_name>\<open>comp_ge\<close>
    | binary_constant And = \<^const_name>\<open>urust_conj\<close>
    | binary_constant Or = \<^const_name>\<open>urust_disj\<close>

  fun assigned_binary_operator AssignSub = Sub
    | assigned_binary_operator AssignMul = Mul
    | assigned_binary_operator AssignMod = Mod
    | assigned_binary_operator AssignBAnd = BAnd
    | assigned_binary_operator AssignBOr = BOr
    | assigned_binary_operator AssignBXor = BXor
    | assigned_binary_operator AssignShl = Shl
    | assigned_binary_operator AssignShr = Shr

  fun binary operator left right = constant (binary_constant operator) [left, right]
  fun assignment_binary operator left right =
    binary (assigned_binary_operator operator) left right

  fun option_some value = constant \<^const_name>\<open>Option.Some\<close> [value]
  val option_none = Const (\<^const_name>\<open>Option.None\<close>, dummyT)
  fun pair left right = constant \<^const_name>\<open>Product_Type.Pair\<close> [left, right]
  fun list_cons head tail = constant \<^const_name>\<open>List.Cons\<close> [head, tail]
  val list_nil = Const (\<^const_name>\<open>List.Nil\<close>, dummyT)
  fun numeral_case_selector alternatives =
    constant \<^const_name>\<open>ncase_selector\<close> [alternatives]
  fun reverse_list expression =
    bindlift1 (Const (\<^const_name>\<open>List.rev\<close>, dummyT)) expression

  val true_value = \<^term>\<open>True\<close>
  val false_value = \<^term>\<open>False\<close>
  val undefined_value = Const (\<^const_name>\<open>undefined\<close>, dummyT)
  val list_cons_constructor = Const (\<^const_name>\<open>List.Cons\<close>, dummyT)
  val list_nil_constructor = Const (\<^const_name>\<open>List.Nil\<close>, dummyT)
  val pair_constructor = Const (\<^const_name>\<open>Product_Type.Pair\<close>, dummyT)
  val tuple_nil_constructor = Const (\<^const_name>\<open>TNil\<close>, dummyT)

  fun case_guard guard scrutinee cases =
    constant \<^const_name>\<open>case_guard\<close> [guard, scrutinee, cases]
  fun case_cons head tail = constant \<^const_name>\<open>case_cons\<close> [head, tail]
  val case_nil = Const (\<^const_name>\<open>case_nil\<close>, dummyT)
  fun case_element pattern body =
    constant \<^const_name>\<open>case_elem\<close> [pattern, body]
  fun case_abstraction abstraction =
    constant \<^const_name>\<open>case_abs\<close> [abstraction]

  val matcher_fail =
    Const (\<^const_name>\<open>urust_matcher_fail\<close>, dummyT)
  fun matcher_succeed payload =
    constant \<^const_name>\<open>urust_matcher_succeed\<close> [payload]
  fun matcher_choice left right =
    constant \<^const_name>\<open>urust_matcher_choice\<close> [left, right]
  fun matcher_map mapping matcher =
    constant \<^const_name>\<open>urust_matcher_map\<close> [mapping, matcher]
  fun matcher_product left right =
    constant \<^const_name>\<open>urust_matcher_product\<close> [left, right]
  fun matcher_test predicate =
    constant \<^const_name>\<open>urust_matcher_test\<close> [predicate]
  fun matcher_lift lifting matcher =
    constant \<^const_name>\<open>urust_matcher_lift\<close> [lifting, matcher]
  fun matcher_destructure destructor matcher =
    constant \<^const_name>\<open>urust_matcher_destructure\<close>
      [destructor, matcher]
  fun matcher_run matcher scrutinee success failure =
    constant \<^const_name>\<open>urust_matcher_run\<close>
      [matcher, scrutinee, success, failure]
  fun matcher_run_guarded matcher scrutinee guard success failure =
    constant \<^const_name>\<open>urust_matcher_run_guarded\<close>
      [matcher, scrutinee, guard, success, failure]
  fun matcher_run_value matcher value success failure =
    constant \<^const_name>\<open>urust_matcher_run_value\<close>
      [matcher, value, success, failure]
  fun matcher_run_guarded_value matcher value guard success failure =
    constant \<^const_name>\<open>urust_matcher_run_guarded_value\<close>
      [matcher, value, guard, success, failure]
end
\<close>

end
