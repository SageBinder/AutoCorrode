theory Parser_Impl_Translate
  imports
    Parser_Impl_Macros
    Parser_Impl_Auto_Deref
begin

section\<open> Expression elaboration \<close>

ML\<open>
signature URUST_TRANSLATE =
sig
  val mk_expression:
    Proof.context ->
      ((string * Position.T) * typ) list ->
      URust_AST.ur_expr ->
      term
  val mk_function:
    Proof.context ->
      ((string * Position.T) * typ) list ->
      URust_AST.ur_expr ->
      term
end
\<close>

text\<open>
Expression lowering orchestrates recursive traversal across the feature-specific elaboration layers.
Terms remain based on \<open>dummyT\<close>, and the command performs the single final
\<open>Syntax.check_term\<close>.
\<close>

ML\<open>
(* Final expression-translation boundary. This structure owns recursive lowering of a complete
   URust_AST.ur_expr, including place translation and the orchestration of bindings and regular loops.
   It delegates matching and macro lowering to their sealed feature layers; it does not parse source,
   type-check terms, or install definitions.

   The public operations accept the Proof.context, typed declaration slots, and one expression AST.
   Named slots become lexical arguments; wildcard slots retain their type and source-order abstraction
   but enter no lexical environment. mk_expression lowers under that environment and applies the
   ordered abstractions without adding a FunctionBody wrapper. mk_function performs the same lowering,
   wraps the body once in FunctionBody, and then applies the abstractions. Untyped clients represent
   inferred slot types with dummyT. Both operations return one unchecked HOL term: the command layer
   optionally constrains the complete term and passes it to Syntax.check_term exactly once in the same
   context. Successful lowering preserves lexical scope and the established shallow-embedding term
   shape. Resolution and pattern-validation failures are propagated with their source positions. The
   signature exposes no public types or constructors.

   Value boundaries wrap only auto-dereference-eligible results in an internal read adjustment.
   Mutable scalar bindings are allocated places; field and index results are provisional projected
   places whose checked receiver type decides whether they really project through a core reference.
   Declaration parameters, immutable bindings, borrows, and other reference-valued expressions
   remain values and are never candidates. Assignment targets plus borrow and explicit-dereference
   operands bypass the adjustment. All lower_* functions, the recursive traversal order, module
   aliases, and the division of work among helper functions are implementation details hidden by
   URUST_TRANSLATE. *)
structure URust_Translate :> URUST_TRANSLATE =
struct
  open URust_AST
  structure T = URust_Shallow_Terms
  structure D = URust_Auto_Deref
  structure A = URust_Cast_Aliases
  structure R = URust_Resolution
  structure P = URust_Patterns
  structure M = URust_Matching
  structure X = URust_Macros
  structure Navigation = Micro_Rust_Semantic_Navigation

  fun with_token layout token action =
    Navigation.with_source
      (source_token_positions layout token) action

  fun with_keyword layout keyword action =
    with_token layout (Keyword_Token keyword) action

  fun with_delimiter layout delimiter action =
    with_token layout (Delimiter_Token delimiter) action

  fun with_tokens layout tokens action =
    Navigation.with_source
      (source_token_positions_for layout tokens) action

  fun with_delimiters layout delimiters action =
    with_tokens layout (map Delimiter_Token delimiters) action

  val word_type_name =
    (case \<^typ>\<open>64 word\<close> of
       Type (name, _) => name
     | _ => error "urust_expr: internal word type is not a type constructor")

  fun annotate_literal body =
    Navigation.annotate Navigation.Primary
      (Const (\<^const_name>\<open>Core_Expression.literal\<close>, dummyT))
      body

  fun with_literal_positions positions action =
    Navigation.with_source positions (fn () =>
      annotate_literal (action ()))

  fun lower_value_antiquotation ctxt environment antiquotation =
    with_literal_positions
      (source_tokens
        (value_antiquotation_source_layout antiquotation)
        |> map #2)
      (fn () =>
        R.parse_antiquotation ctxt environment
          (value_antiquotation_source antiquotation))

  fun lower_source_literal ctxt environment payload =
    (case payload of
       LP_Integer integer =>
         let
           val _ =
             Option.app
               (fn suffix_pos =>
                 Navigation.defer_type ctxt suffix_pos word_type_name)
               (integer_literal_suffix_position integer)
         in
           with_literal_positions
             [integer_literal_numeric_position integer]
             (fn () =>
               R.literal_expression ctxt environment payload)
         end
     | LP_Bool (value, _) =>
         with_keyword (literal_source_layout payload)
           (if value then "true" else "false")
           (fn () =>
             R.literal_expression ctxt environment payload)
     | LP_String (_, pos) =>
         with_literal_positions [pos] (fn () =>
           R.literal_expression ctxt environment payload)
     | LP_ValAntiq antiquotation =>
         with_literal_positions
           (source_tokens
             (value_antiquotation_source_layout antiquotation)
             |> map #2)
           (fn () =>
             R.literal_expression ctxt environment payload))

  fun index_positions layout =
    source_token_positions_for layout
      [Delimiter_Token "[", Delimiter_Token "]"]

  fun function_literal_positions antiquotation suffix_pos =
    source_token_positions
      (value_antiquotation_source_layout antiquotation)
      Literal_Token @ [suffix_pos]

  fun lower_place lower_raw lower_value ctxt environment place =
    (case place of
       UP_Path path =>
         R.literal_path ctxt environment path
     | UP_Deref (expression, layout) =>
         let
           val pos =
             the_source_token_position layout Operator_Token
           val lowered = D.raw_term (lower_raw environment expression)
         in
           with_token layout Operator_Token (fn () =>
             Navigation.probe
               (T.unary U_Deref pos lowered) lowered)
         end
     | UP_Field (base, name, layout) =>
         let
           val lowered_base =
             lower_place lower_raw lower_value ctxt environment base
         in
           with_delimiter layout "." (fn () =>
             R.field_expression ctxt environment lowered_base name
               (the_source_token_position layout Name_Token))
         end
     | UP_Index (base, index, layout) =>
         let
           val lowered_base =
             lower_place lower_raw lower_value ctxt environment base
           val lowered_index = lower_value environment index
         in
           Navigation.with_source (index_positions layout) (fn () =>
             T.index lowered_base lowered_index)
         end
     | UP_Antiq source =>
         R.parse_antiquotation ctxt environment source)

  fun lower_binding lower_value ctxt site environment
      (pattern, rhs, body, layout, keyword) =
    let
      val lowered_rhs = lower_value environment rhs
      val prepared =
        P.prepare_binding site ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower_value body_environment body
      val binding =
        with_tokens layout
          [Keyword_Token keyword, Delimiter_Token "="] (fn () =>
          P.bind_prepared prepared lowered_rhs lowered_body)
    in
      Navigation.with_source
        (source_token_positions layout (Delimiter_Token ";"))
        (fn () =>
          Navigation.annotate Navigation.Primary
            (Const
              (\<^const_name>\<open>Core_Expression.sequence\<close>,
               dummyT))
            binding)
    end

  fun lower_fuel ctxt environment source =
    R.parse_antiquotation ctxt environment source

  fun lower_log_data ctxt environment entries =
    let
      fun lower_entry (LDE_String (raw, pos)) =
            T.log_string_entry raw pos
        | lower_entry (LDE_Identifier identifier) =
            T.generate_debug_entry
              (R.ordinary_identifier_value ctxt environment identifier)
    in T.log_data (map lower_entry entries) end

  fun lower_for lower_value ctxt environment
      (pattern, iterable, body, layout) =
    let
      val lowered_iterable = lower_value environment iterable
      val prepared =
        P.prepare_binding P.For_Binder ctxt environment pattern
      val body_environment = P.binding_environment prepared
      val lowered_body = lower_value body_environment body
      val iterator =
        with_keyword layout "in" (fn () =>
          T.into_iterator lowered_iterable)
      val abstraction =
        P.binding_abstraction prepared lowered_body
    in
      with_keyword layout "for" (fn () =>
        T.for_loop iterator abstraction)
    end

  fun lower_closure lower_value ctxt environment
      (formals, body, layout) =
    let
      fun formal_signature (P_Ident formal) = formal
        | formal_signature (P_Wild pos) =
            error
              ("urust_expr: closure formal must be an identifier" ^
                Position.here pos)
        | formal_signature _ =
            error "urust_expr: internal non-identifier closure formal"
      val signatures = map formal_signature formals
      val (formal_terms, body_environment) =
        R.allocate_closure_formals ctxt environment signatures
      val lowered_body = lower_value body_environment body
    in
      with_token layout Operator_Token (fn () =>
        T.closure formal_terms lowered_body)
    end

  fun lower_repeat_length ctxt environment allow_sized length =
    (case length of
       RL_Integer integer =>
         let
           val _ =
             Option.app
               (fn suffix_pos =>
                 Navigation.defer_type ctxt suffix_pos word_type_name)
               (integer_literal_suffix_position integer)
         in
           with_literal_positions
             [integer_literal_numeric_position integer]
             (fn () =>
               T.literal
                 (T.repeat_length_integer allow_sized
                   (integer_literal_position integer)
                   (integer_literal_lexeme integer)))
         end
     | RL_Path path =>
         T.literal
           (R.global_constant_path_value ctxt environment path)
     | RL_Bin (operator, left, right, layout) =>
         let
           val lowered_left =
             lower_repeat_length ctxt environment allow_sized left
           val lowered_right =
             lower_repeat_length ctxt environment allow_sized right
         in
           with_token layout Operator_Token (fn () =>
             T.binary operator lowered_left lowered_right)
         end
     | RL_Group (inner, _) =>
         lower_repeat_length ctxt environment allow_sized inner
     | RL_CastUsize (inner, layout) =>
         let
           val lowered_inner =
             lower_repeat_length ctxt environment true inner
         in
           with_keyword layout "as" (fn () =>
             T.cast (CT_Unsigned UT_Usize) lowered_inner)
         end)

  fun empty_block (UE_Block (UE_Unit _, _)) = true
    | empty_block _ = false

  (* In a no-struct control head, an empty struct at the right source boundary can be parsed as a bare
     path followed by the control body's empty braces. Delimiters and postfixes stop the boundary walk:
     their closing token means the following braces cannot belong to an inner struct expression.
     U_Propagate shares the unary AST node with true prefix operators, but its source token is postfix
     and therefore stops rather than continuing this walk. *)
  fun trailing_ungrouped_path expression =
    (case expression of
       UE_Path path => SOME path
     | UE_Return (SOME value, _) => trailing_ungrouped_path value
     | UE_Closure (_, body, _) => trailing_ungrouped_path body
     | UE_Bin (_, _, right, _) => trailing_ungrouped_path right
     | UE_Range (_, _, upper, _) => trailing_ungrouped_path upper
     | UE_Unary (U_Not, operand, _) => trailing_ungrouped_path operand
     | UE_Unary (U_Borrow _, operand, _) => trailing_ungrouped_path operand
     | UE_Unary (U_Deref, operand, _) => trailing_ungrouped_path operand
     | UE_Unary (U_Propagate, _, _) => NONE
     | UE_Assign (_, _, rhs, _) => trailing_ungrouped_path rhs
     | _ => NONE)

  fun reject_ambiguous_empty_struct_head ctxt environment head body =
    if empty_block body then
      (case trailing_ungrouped_path head of
         SOME path =>
           if R.is_nullary_function_path ctxt environment path then
             error
               ("urust_expr: empty struct expression in a control head must be parenthesized" ^
                 Position.here (expression_position body))
           else ()
       | NONE => ())
    else ()

  (* Lexical scope is explicit: a let RHS uses the outer environment, while its body uses the exact
     environment returned by pattern binding. Closure bodies use the final duplicate-permitting formal
     environment, while every formal still contributes its own ordered abstraction. Case alternatives
     follow the same rule independently. *)
  fun lower_expression ctxt environment expression =
    (case expression of
       UE_Unit _ =>
         D.plain (T.literal HOLogic.unit)
     | UE_Tuple (arguments, layout) =>
         let
           val lowered_arguments =
             map (lower_value ctxt environment) arguments
         in
           D.plain
             (with_delimiters layout ["(", ")"] (fn () =>
               T.tuple lowered_arguments))
         end
     | UE_Array (elements, layout) =>
         let
           val lowered_elements =
             map (lower_value ctxt environment) elements
         in
           D.plain
             (with_delimiters layout ["[", "]"] (fn () =>
               T.array_literal lowered_elements))
         end
     | UE_ArrayRepeat (mode, value, length, layout) =>
         let
           val lowered_length =
             lower_repeat_length ctxt environment false length
           val lowered_value =
             lower_value ctxt environment value
           val positions =
             source_token_positions_for layout
               [Delimiter_Token "[",
                Keyword_Token "const",
                Delimiter_Token ";",
                Delimiter_Token "]"]
         in
           D.plain
             (Navigation.with_source positions (fn () =>
               (case mode of
                  AR_Ordinary =>
                    T.array_repeat lowered_length lowered_value
                | AR_InlineConst =>
                    T.array_repeat_inline_const
                      lowered_length lowered_value)))
         end
     | UE_Struct (head, fields, struct_layout) =>
         let
           val struct_pos = source_span struct_layout
           fun initializer (SE_Field (_, _, expression)) = expression
           val _ =
             T.check_function_call_arity struct_pos (length fields)
           val function =
             R.struct_function_path ctxt environment
               head (length fields)
           val _ = R.report_struct_labels ctxt head fields
           val lowered_initializers =
             map
               (lower_value ctxt environment o initializer)
               fields
         in
           D.plain
             (with_delimiters struct_layout ["{", "}"] (fn () =>
               T.function_call struct_pos function
                 lowered_initializers))
         end
     | UE_Path path =>
         let
           val (term, category) =
             R.literal_path_with_category ctxt environment path
         in
           (case category of
              R.Auto_Deref_Eligible =>
                D.eligible expression term
            | _ => D.plain term)
         end
     | UE_Literal payload =>
         D.plain
           (lower_source_literal ctxt environment payload)
     | UE_ExprAntiq source =>
         D.plain
           (R.parse_antiquotation ctxt environment source)
     | UE_Yield layout =>
         D.plain
           (with_keyword layout "yield" T.pause_expression)
     | UE_Log (priority, data, layout) =>
         let
           val lowered_priority =
             lower_value_antiquotation ctxt environment priority
           val lowered_data =
             lower_value_antiquotation ctxt environment data
         in
           D.plain
             (with_keyword layout "log" (fn () =>
               T.primitive_log lowered_priority lowered_data))
         end
     | UE_LogData (entries, layout) =>
         let
           val positions =
             source_token_positions layout (Keyword_Token "l") @
             source_token_positions layout
               (Delimiter_Token "log-data-open") @
             source_token_positions layout
               (Delimiter_Token "log-data-close")
         in
           D.plain
             (with_literal_positions positions (fn () =>
               lower_log_data ctxt environment entries))
         end
     | UE_Closure (formals, body, layout) =>
         D.plain
           (lower_closure (lower_value ctxt) ctxt environment
             (formals, body, layout))
     | UE_Seq (first, second, layout) =>
         let
           val lowered_first =
             lower_value ctxt environment first
           val lowered_second =
             lower_value ctxt environment second
         in
           D.plain
             (with_delimiter layout ";" (fn () =>
               T.sequence lowered_first lowered_second))
         end
     | UE_Return (value, layout) =>
         let
           val lowered_value =
             (case value of
                SOME expression =>
                  lower_value ctxt environment expression
              | NONE => T.literal HOLogic.unit)
         in
           D.plain
             (with_keyword layout "return" (fn () =>
               T.return_value lowered_value))
         end
     | UE_Bin (operator, left, right, layout) =>
         let
           val lowered_left =
             lower_value ctxt environment left
           val lowered_right =
             lower_value ctxt environment right
         in
           D.plain
             (with_token layout Operator_Token (fn () =>
               T.binary operator lowered_left lowered_right))
         end
     | UE_Cast (operand, target, layout) =>
         let
           val primitive_target = A.resolve ctxt target
           val _ =
             Option.app
               (fn type_pos =>
                 Navigation.defer_type ctxt type_pos word_type_name)
               (source_cast_target_type_position target)
           val lowered_operand =
             lower_value ctxt environment operand
         in
           D.plain
             (with_keyword layout "as" (fn () =>
               T.cast primitive_target lowered_operand))
         end
     | UE_Range (kind, lower, upper, layout) =>
         let
           val lowered_lower =
             lower_value ctxt environment lower
           val lowered_upper =
             lower_value ctxt environment upper
         in
           D.plain
             (with_token layout Operator_Token (fn () =>
               T.bounded_range kind lowered_lower lowered_upper))
         end
     | UE_Unary
         (U_Borrow _, UE_Array (elements, array_layout), _) =>
         let
           val lowered_elements =
             map (lower_value ctxt environment) elements
         in
           D.plain
             (with_delimiters array_layout ["[", "]"] (fn () =>
               T.array_literal lowered_elements))
         end
     | UE_Unary (operator, operand, layout) =>
         let
           val pos =
             the_source_token_position layout Operator_Token
           val lowered_operand =
             (case operator of
                U_Borrow _ =>
                  D.raw_term
                    (lower_expression ctxt environment operand)
              | U_Deref =>
                  D.raw_term
                    (lower_expression ctxt environment operand)
              | _ => lower_value ctxt environment operand)
           val positions =
             source_token_positions layout Operator_Token @
             (case operator of
                U_Borrow BM_Mut =>
                  source_token_positions layout
                    (Keyword_Token "mut")
              | _ => [])
         in
           D.plain
             (Navigation.with_source positions (fn () =>
               T.unary operator pos lowered_operand))
         end
     | UE_Group (inner, _) =>
         D.transparent expression
           (lower_expression ctxt environment inner)
     | UE_Block (inner, _) =>
         D.transparent expression
           (lower_expression ctxt environment inner)
     | UE_If (condition, then_branch, else_branch, layout) =>
         let
           val _ =
             reject_ambiguous_empty_struct_head ctxt environment
               condition then_branch
           val lowered_condition =
             lower_value ctxt environment condition
           val lowered_then =
             lower_value ctxt environment then_branch
           val lowered_else =
             (case else_branch of
                SOME branch =>
                  lower_value ctxt environment branch
              | NONE => T.literal HOLogic.unit)
           val positions =
             source_token_positions layout
               (Keyword_Token "if") @
             source_token_positions layout
               (Keyword_Token "else")
         in
           D.plain
             (Navigation.with_source positions (fn () =>
               T.conditional lowered_condition
                 lowered_then lowered_else))
         end
     | UE_IfLet
         (pattern, scrutinee, success, fallback, layout) =>
         let
           val _ =
             reject_ambiguous_empty_struct_head ctxt environment
               scrutinee success
         in
           D.plain
             (M.lower_if_let (lower_value ctxt) ctxt environment
               (pattern, scrutinee, success, fallback, layout))
         end
     | UE_LetElse
         (pattern, scrutinee, fallback, continuation, layout) =>
         D.plain
           (M.lower_let_else (lower_value ctxt) ctxt environment
             (pattern, scrutinee, fallback, continuation, layout))
     | UE_While (fuel, condition, body, layout) =>
         let
           val lowered_fuel =
             lower_fuel ctxt environment fuel
           val lowered_condition =
             lower_value ctxt environment condition
           val lowered_body =
             lower_value ctxt environment body
           val positions =
             source_token_positions_for layout
               [Delimiter_Token "#[",
                Keyword_Token "fuel",
                Delimiter_Token "]",
                Keyword_Token "while"]
         in
           D.plain
             (Navigation.with_source positions (fn () =>
               T.bounded_while lowered_fuel
                 lowered_condition lowered_body))
         end
     | UE_Loop (fuel, body, layout) =>
         let
           val lowered_fuel =
             lower_fuel ctxt environment fuel
           val lowered_body =
             lower_value ctxt environment body
           val positions =
             source_token_positions_for layout
               [Delimiter_Token "#[",
                Keyword_Token "fuel",
                Delimiter_Token "]",
                Keyword_Token "loop"]
         in
           D.plain
             (Navigation.with_source positions (fn () =>
               T.bounded_loop lowered_fuel lowered_body))
         end
     | UE_For (pattern, iterable, body, layout) =>
         let
           val _ =
             reject_ambiguous_empty_struct_head ctxt environment
               iterable body
         in
           D.plain
             (lower_for (lower_value ctxt) ctxt environment
               (pattern, iterable, body, layout))
         end
     | UE_WhileLet (fuel, pattern, scrutinee, body, layout) =>
         let
           val _ =
             reject_ambiguous_empty_struct_head ctxt environment
               scrutinee body
         in
           D.plain
             (M.lower_while_let (lower_value ctxt) ctxt environment
               (fuel, pattern, scrutinee, body, layout))
         end
     | UE_Let (pattern, rhs, body, layout) =>
         D.plain
           (lower_binding (lower_value ctxt) ctxt
             P.Let_Const_Binder environment
             (pattern, rhs, body, layout, "let"))
     | UE_LetMut (pattern, rhs, body, layout) =>
         D.plain
           (lower_binding (lower_value ctxt) ctxt
             (P.Mutable_Let_Binder
               (the_source_token_position layout
                 (Keyword_Token "mut"))) environment
             (pattern, rhs, body, layout, "let"))
     | UE_Const (pattern, rhs, body, layout) =>
         D.plain
           (lower_binding (lower_value ctxt) ctxt
             P.Let_Const_Binder environment
             (pattern, rhs, body, layout, "const"))
     | UE_Call (callee, arguments, call_layout) =>
         let
           val call_pos = source_span call_layout
           val runtime_arity =
             length arguments +
               (case callee of UC_Method _ => 1 | _ => 0)
           val _ =
             T.check_function_call_arity call_pos runtime_arity
           val (function, source_arguments) =
             (case callee of
                UC_Path path =>
                  (R.function_path ctxt environment path
                     (length arguments),
                   arguments)
              | UC_Method (receiver, segment) =>
                  (R.method_path ctxt environment
                     (UR_Path (Identifier_Head, [segment],
                       (case segment_generic_args segment of
                          SOME (Generic_Args (_, pos)) => pos
                        | NONE => #2 (segment_identifier segment)))),
                   receiver :: arguments)
              | UC_Antiq source =>
                  (R.parse_antiquotation ctxt environment source, arguments)
              | UC_FunLiteral
                  (antiquotation, lift_arity, suffix_pos,
                   generic_arguments) =>
                  let
                    val pure_function =
                      R.parse_antiquotation ctxt environment
                        (value_antiquotation_source antiquotation)
                    val lifted_function =
                      Navigation.with_source
                        (function_literal_positions
                          antiquotation suffix_pos)
                        (fn () =>
                          T.lift_function suffix_pos
                            lift_arity pure_function)
                    val parameterized_function =
                      R.apply_generic_arguments ctxt environment
                        lifted_function generic_arguments
                  in (parameterized_function, arguments) end)
           val lowered_arguments =
             map (lower_value ctxt environment) source_arguments
         in
           D.plain
             (with_delimiters call_layout ["(", ")"] (fn () =>
               T.function_call call_pos function
                 lowered_arguments))
         end
     | UE_Field (receiver, name, layout) =>
         let
           val lowered_receiver =
             D.raw_term
               (lower_expression ctxt environment receiver)
         in
           D.eligible expression
             (with_delimiter layout "." (fn () =>
               R.field_expression ctxt environment
                 lowered_receiver name
                 (the_source_token_position layout Name_Token)))
         end
     | UE_Index (receiver, index, layout) =>
         let
           val lowered_receiver =
             D.raw_term
               (lower_expression ctxt environment receiver)
           val lowered_index =
             lower_value ctxt environment index
         in
           D.eligible expression
             (Navigation.with_source (index_positions layout) (fn () =>
               T.index lowered_receiver lowered_index))
         end
     | UE_TupleProjection (receiver, index, layout) =>
         let
           val pos =
             the_source_token_position layout Name_Token
           val lowered_receiver =
             lower_value ctxt environment receiver
         in
           D.plain
             (with_token layout Name_Token (fn () =>
               T.tuple_projection pos index lowered_receiver))
         end
     | UE_Assign (operator, place, rhs, layout) =>
         let
           val pos =
             the_source_token_position layout Operator_Token
           val lowered_place =
             lower_place (lower_expression ctxt)
               (lower_value ctxt) ctxt environment place
           val lowered_rhs = lower_value ctxt environment rhs
         in
           D.plain
             (case operator of
                Assign =>
                  with_token layout Operator_Token (fn () =>
                    T.update pos lowered_place lowered_rhs)
              | AssignAdd =>
                  with_token layout Operator_Token (fn () =>
                    T.assign_add pos lowered_place lowered_rhs)
              | AssignBin binary_operator =>
                  let
                    val old_value =
                      T.unary U_Deref pos lowered_place
                    val updated_value =
                      with_token layout Operator_Token (fn () =>
                        T.assignment_binary binary_operator
                          old_value lowered_rhs)
                  in
                    with_token layout Operator_Token (fn () =>
                      T.update pos lowered_place updated_value)
                  end)
         end
     | UE_Macro (path, payload, layout) =>
         D.plain
           (X.lower_macro (lower_value ctxt) ctxt environment
             (path, payload, layout))
     | UE_Match (flavour, scrutinee, arms, layout) =>
         D.plain
           (M.lower_match (lower_value ctxt) ctxt environment
             (flavour, scrutinee, arms, layout)))

  and lower_value ctxt environment expression =
    D.value_term expression
      (lower_expression ctxt environment expression)

  fun mk_with_wrapper allocate wrapper ctxt arguments expression =
    let
      val (abstractions, environment) =
        allocate ctxt R.empty_environment arguments
      val body = lower_value ctxt environment expression
    in
      fold_rev (fn abstraction => fn term => abstraction term)
        abstractions (wrapper body)
    end

  fun mk_expression ctxt arguments expression =
    mk_with_wrapper R.allocate_expression_arguments I
      ctxt arguments expression

  fun mk_function ctxt parameters expression =
    mk_with_wrapper R.allocate_function_parameters T.function_body
      ctxt parameters expression
end
\<close>

end
