theory Parser_Impl_Shallow_Terms
  imports
    Parser_Impl_AST
    Shallow_Micro_Rust.Micro_Rust_Shallow_Embedding
begin

section\<open> Shallow term vocabulary \<close>

ML\<open>
signature URUST_SHALLOW_TERMS =
sig
  val literal: term -> term
  val boolean_expression: bool -> term
  val string_value: string -> Position.T -> term
  val string_from_characters: term -> term
  val integer_value: Position.T -> string -> term
  val closure: term list -> term -> term

  val apply_parameters: term -> term list -> term
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
  val array_literal: term list -> term
  val bounded_range: URust_AST.range_kind -> term -> term -> term
  val index: term -> term -> term
  val cast: URust_AST.cast_target -> term -> term
  val assertion: term -> term
  val assertion_equal: term -> term -> term
  val assertion_not_equal: term -> term -> term
  val panic_message: term -> term
  val fatal_message: term -> term
  val unimplemented_message: term -> term
  val address_of: term -> term
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
end
\<close>

text\<open>
This module owns the pure vocabulary used to construct the existing shallow embedding. All terms use
\<open>dummyT\<close>; the command layer still performs the single final \<open>Syntax.check_term\<close>.
\<close>

ML\<open>
(* Shallow-term construction boundary. URust_Shallow_Terms owns the unchecked HOL vocabulary and exact
   term shapes used to target the existing shallow embedding. It does not resolve names, allocate
   source binders, inspect complete expression or pattern ASTs, type-check terms, or install
   definitions. Its results are composable unchecked terms that may contain dummy types; callers must
   send the final assembled term through the command layer's single Syntax.check_term in the
   originating proof context. Source positions are used for diagnostics and to encode positions on
   overloaded constants where required.

   URUST_SHALLOW_TERMS is the complete public interface:

   * literal wraps a HOL value as a shallow expression. boolean_expression constructs the dedicated
     shallow true/false expression constants, while string_value and integer_value construct raw HOL
     values for later wrapping. string_value decodes the lexer-preserved string spelling at the given
     position. integer_value accepts the parser's decimal or 0x hexadecimal lexeme, with no suffix or
     one of u8, u16, u32, u64, and usize, optionally separated by one compatibility underscore; it
     reports malformed numbers and unsupported suffixes at the source position.
   * closure wraps one FunctionBody around the already-lowered body, abstracts the ordered formal
     Frees in source order, and then applies one outer literal. It imposes no call-arity limit.
   * function_call maps a function term and its argument list to funcall0 through funcall14 and rejects
     larger arities at its call position. bind takes an expression and a continuation abstraction;
     sequence, return_value, and case_product preserve the corresponding shallow-embedding constructors
     rather than interchangeable HOL encodings.
   * allocate_reference, update, and assign_add construct the positioned overloaded store operations.
     update takes place then RHS; assign_add uses the same order. focus_field takes a resolved field
     lens then its receiver. tuple accepts at least two expression terms and emits the frontend's
     right-nested bindlift2/product representation ending in TNil, rejecting shorter lists.
     array_literal emits right-nested bindlift2/List.Cons applications ending in literal List.Nil.
     bounded_range selects range_new or range_eq_new and applies it through funcall2. index applies the
     overloaded index_const through funcall2. cast selects one of the legacy integral or raw-pointer
     conversion constants from one closed table. usize selects the u64 conversion, and raw-pointer
     const/mut targets remain distinct AST values while selecting the same shallow constant.
   * conditional, bounded_while, bounded_loop, for_loop, and into_iterator expose the control-flow
     combinators. Their arguments follow source order; for_loop takes the iterator expression then its
     body abstraction. bounded_loop supplies the true condition. skip is literal unit.
   * binary maps every URust_AST.binop to its shallow operation and takes left then right operands.
     unary maps negation, borrow, dereference, and propagation; its position is attached where the
     selected overloaded operation requires one. assignment_binary maps the non-additive
     URust_AST.assign_binop cases to the pure operation used to compute a compound-assignment RHS;
     addition remains the separate assign_add operation.
   * option_some, option_none, pair, list_cons, list_nil, numeral_case_selector, and reverse_list
     provide the value vocabulary used by switch and pattern lowering. true_value, false_value, and
     undefined_value are raw HOL values. list_cons_constructor, list_nil_constructor,
     pair_constructor, and tuple_nil_constructor are unapplied constructor terms for pattern trees.
   * case_guard takes guard, scrutinee, then a case list. case_cons and case_nil build that list;
     case_element takes pattern then body, and case_abstraction wraps the resulting abstraction.

   The raw constant builders, position encoding mechanics, function-constant vector, suffix-table
   representation and integer scanners, tuple recursion, and operator lookup functions are
   implementation details. Their representations may change, but the supported arities, literal
   spellings, operator meanings, diagnostics, argument order, and shallow term shapes described above
   are interface behavior relied on by resolution, pattern compilation, translation, and frontend
   conformance checks. No additional declarations in the structure are public through the signature. *)
structure URust_Shallow_Terms :> URUST_SHALLOW_TERMS =
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

  fun closure formals body =
    literal
      (fold_rev Term.lambda formals
        (constant \<^const_name>\<open>FunctionBody\<close> [body]))

  fun apply_parameters function parameters =
    Term.list_comb (function, parameters)

  fun boolean_expression value =
    Const (if value then \<^const_name>\<open>Bool_Type.true\<close>
           else \<^const_name>\<open>Bool_Type.false\<close>, dummyT)

  fun string_from_characters characters =
    constant \<^const_name>\<open>String.implode\<close> [characters]

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
    in string_from_characters list end

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

  fun array_literal [] = literal (Const (\<^const_name>\<open>List.Nil\<close>, dummyT))
    | array_literal (first :: rest) =
        constant \<^const_name>\<open>bindlift2\<close>
          [Const (\<^const_name>\<open>List.Cons\<close>, dummyT),
           first, array_literal rest]

  fun bounded_range kind lower upper =
    constant \<^const_name>\<open>funcall2\<close>
      [Const
        ((case kind of
            RK_Exclusive => \<^const_name>\<open>range_new\<close>
          | RK_Inclusive => \<^const_name>\<open>range_eq_new\<close>),
         dummyT),
       lower, upper]

  fun index expression subscript =
    constant \<^const_name>\<open>funcall2\<close>
      [Const (\<^const_name>\<open>index_const\<close>, dummyT),
       expression, subscript]

  fun cast_result_type typ =
    Term.map_atyps
      (fn TFree _ => dummyT | TVar _ => dummyT | atomic => atomic)
      typ

  val cast_functions =
    [(CT_Unsigned UT_U8,
      (\<^term>\<open>ucastu8\<close>,
       cast_result_type
         \<^typ>\<open>('s, 8 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Unsigned UT_U16,
      (\<^term>\<open>ucastu16\<close>,
       cast_result_type
         \<^typ>\<open>('s, 16 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Unsigned UT_U32,
      (\<^term>\<open>ucastu32\<close>,
       cast_result_type
         \<^typ>\<open>('s, 32 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Unsigned UT_U64,
      (\<^term>\<open>ucastu64\<close>,
       cast_result_type
         \<^typ>\<open>('s, 64 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Unsigned UT_Usize,
      (\<^term>\<open>ucastu64\<close>,
       cast_result_type
         \<^typ>\<open>('s, 64 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Signed ST_I32,
      (\<^term>\<open>ucasti32\<close>,
       cast_result_type
         \<^typ>\<open>('s, 32 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_Signed ST_I64,
      (\<^term>\<open>ucasti64\<close>,
       cast_result_type
         \<^typ>\<open>('s, 64 word, 'c, 'abort, 'i, 'o) expression\<close>)),
     (CT_RawPointer (RPM_Const, UT_U8),
      (\<^term>\<open>raw_ptr_cast_u8\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 8 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Const, UT_U16),
      (\<^term>\<open>raw_ptr_cast_u16\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 16 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Const, UT_U32),
      (\<^term>\<open>raw_ptr_cast_u32\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 32 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Const, UT_U64),
      (\<^term>\<open>raw_ptr_cast_u64\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 64 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Const, UT_Usize),
      (\<^term>\<open>raw_ptr_cast_u64\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 64 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Mut, UT_U8),
      (\<^term>\<open>raw_ptr_cast_u8\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 8 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Mut, UT_U16),
      (\<^term>\<open>raw_ptr_cast_u16\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 16 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Mut, UT_U32),
      (\<^term>\<open>raw_ptr_cast_u32\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 32 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Mut, UT_U64),
      (\<^term>\<open>raw_ptr_cast_u64\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 64 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>)),
     (CT_RawPointer (RPM_Mut, UT_Usize),
      (\<^term>\<open>raw_ptr_cast_u64\<close>,
       cast_result_type
         \<^typ>\<open>
           ('s, ('addr, 'gv, 64 word) Global_Store.ref,
            'c, 'abort, 'i, 'o) expression
         \<close>))]

  fun cast target expression =
    (case AList.lookup (op =) cast_functions target of
       SOME (target_function, result_type) =>
         Type.constraint result_type
           (Term.list_comb
             (Term.map_types (K dummyT) target_function, [expression]))
     | NONE => error "urust_expr: internal unsupported cast target")

  fun assertion expression =
    constant \<^const_name>\<open>assert\<close> [expression]

  fun assertion_equal left right =
    constant \<^const_name>\<open>assert_eq\<close> [left, right]

  fun assertion_not_equal left right =
    constant \<^const_name>\<open>assert_ne\<close> [left, right]

  fun panic_message message =
    constant \<^const_name>\<open>abort\<close>
      [constant \<^const_name>\<open>Panic\<close> [message]]

  fun fatal_message message =
    constant \<^const_name>\<open>fatal\<close> [message]

  fun unimplemented_message message =
    constant \<^const_name>\<open>abort\<close>
      [constant \<^const_name>\<open>Unimplemented\<close> [message]]

  val legacy_ref_address =
    Term.map_types (K dummyT) \<^term>\<open>ref_address\<close>

  fun address_of expression =
    bindlift1 legacy_ref_address expression

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
end
\<close>

end
