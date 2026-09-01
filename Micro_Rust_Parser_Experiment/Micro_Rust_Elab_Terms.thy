theory Micro_Rust_Elab_Terms
  imports
    Micro_Rust_Parser_AST
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
begin

section\<open> Shallow term vocabulary \<close>

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
  fun integer_suffix_type "u8" = SOME \<^typ>\<open>8 word\<close>
    | integer_suffix_type "u16" = SOME \<^typ>\<open>16 word\<close>
    | integer_suffix_type "u32" = SOME \<^typ>\<open>32 word\<close>
    | integer_suffix_type "u64" = SOME \<^typ>\<open>64 word\<close>
    | integer_suffix_type "usize" = SOME \<^typ>\<open>64 word\<close>
    | integer_suffix_type _ = NONE

  fun parse_integer pos lexeme =
    let
      val (number_text, suffix) =
        (case first_field "_" lexeme of
           SOME (number_text, suffix) => (number_text, SOME suffix)
         | NONE => (lexeme, NONE))
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
      (case suffix of
         NONE => (value, NONE)
       | SOME suffix_text =>
           (case integer_suffix_type suffix_text of
              SOME typ => (value, SOME typ)
            | NONE =>
                error ("urust_expr: unsupported integer-literal suffix " ^
                  quote ("_" ^ suffix_text) ^
                  " (supported: _u8 _u16 _u32 _u64 _usize)" ^ Position.here pos)))
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
end
\<close>

end
