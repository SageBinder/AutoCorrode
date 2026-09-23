theory Parser_Impl_AST
  imports Parser_Utils
begin

section\<open> Reified AST \<close>

text\<open>
One constructor per uRust surface form. Composite syntax retains a complete source span for
diagnostics and exact, role-tagged token ranges for later PIDE markup.
\<close>
ML\<open>
signature URUST_AST =
sig
  datatype source_token =
      Keyword_Token of string
    | Operator_Token
    | Delimiter_Token of string
    | Name_Token
    | Bang_Token
    | Literal_Token
  datatype source_layout =
    Source_Layout of Position.T * (source_token * Position.T) list

  val make_source_layout:
    Position.T -> (source_token * Position.T) list -> source_layout
  val source_span: source_layout -> Position.T
  val source_tokens: source_layout -> (source_token * Position.T) list
  val source_token_positions:
    source_layout -> source_token -> Position.T list
  val source_token_positions_for:
    source_layout -> source_token list -> Position.T list
  val source_token_position:
    source_layout -> source_token -> Position.T option
  val the_source_token_position:
    source_layout -> source_token -> Position.T

  datatype integer_literal =
    Integer_Literal of string * source_layout * Position.T option
  datatype value_antiquotation =
    Value_Antiquotation of Input.source * source_layout
  datatype literal_payload =
      LP_Integer of integer_literal
    | LP_Bool of bool * Position.T
    | LP_String of string * Position.T
    | LP_ValAntiq of value_antiquotation

  val integer_literal_lexeme: integer_literal -> string
  val integer_literal_position: integer_literal -> Position.T
  val integer_literal_numeric_position: integer_literal -> Position.T
  val integer_literal_suffix_position: integer_literal -> Position.T option
  val value_antiquotation_source: value_antiquotation -> Input.source
  val value_antiquotation_source_layout:
    value_antiquotation -> source_layout
  val literal_position: literal_payload -> Position.T
  val literal_source_layout: literal_payload -> source_layout

  datatype borrow_mode = BM_Imm | BM_Mut
  datatype range_kind = RK_Exclusive | RK_Inclusive
  datatype unsigned_type = UT_U8 | UT_U16 | UT_U32 | UT_U64 | UT_Usize
  datatype signed_type = ST_I32 | ST_I64
  datatype raw_pointer_mutability = RPM_Const | RPM_Mut
  datatype cast_target =
      CT_Unsigned of unsigned_type
    | CT_Signed of signed_type
    | CT_RawPointer of raw_pointer_mutability * unsigned_type

  type canonical_fragment = string
  datatype generic_arg =
    Generic_Arg of canonical_fragment * Input.source
  datatype generic_args =
    Generic_Args of generic_arg list * Position.T
  datatype path_segment =
    Path_Segment of string * Position.T * generic_args option
  datatype primitive_type =
      Primitive_Unsigned of unsigned_type
    | Primitive_Signed of signed_type
  datatype path_head =
      Identifier_Head
    | Primitive_Head of primitive_type
  datatype ur_path =
    UR_Path of path_head * path_segment list * Position.T

  datatype source_cast_target =
      SCT_Primitive of cast_target * Position.T
    | SCT_Named of ur_path

  val source_cast_target_type_position:
    source_cast_target -> Position.T option

  datatype rust_primitive_type =
      DPT_U8
    | DPT_U16
    | DPT_U32
    | DPT_U64
    | DPT_U128
    | DPT_Usize
    | DPT_I8
    | DPT_I16
    | DPT_I32
    | DPT_I64
    | DPT_I128
    | DPT_Isize
    | DPT_Bool
    | DPT_Char
    | DPT_Str
    | DPT_Never
    | DPT_Unit
  datatype rust_type =
      Primitive_Type of rust_primitive_type * Position.T
    | Path_Type of rust_type_path_segment list * source_layout
    | Tuple_Type of rust_type list * source_layout
    | Group_Type of rust_type * source_layout
    | Reference_Type of borrow_mode * rust_type * source_layout
    | Raw_Pointer_Type of
        raw_pointer_mutability * rust_type * source_layout
    | Slice_Type of rust_type * source_layout
    | Array_Type of rust_type * integer_literal * source_layout
    | HOL_Type_Source of Input.source
  and rust_generic_argument =
      Rust_Type_Argument of rust_type
    | Rust_Numeric_Argument of integer_literal
  and rust_type_path_segment =
    Rust_Type_Path_Segment of
      string * Position.T * rust_generic_argument list option * source_layout

  type datatype_type = rust_type
  datatype datatype_field =
    Datatype_Field of string * Position.T * datatype_type
  datatype datatype_shape =
      Unit_Shape
    | Tuple_Shape of datatype_type list
    | Named_Shape of datatype_field list
  datatype datatype_variant =
    Datatype_Variant of string * Position.T * datatype_shape
  datatype urust_datatype =
      Struct_Item of
        string * Position.T * datatype_shape * Position.T
    | Enum_Item of
        string * Position.T * datatype_variant list * Position.T

  val rust_type_position: rust_type -> Position.T
  val datatype_type_position: datatype_type -> Position.T
  val datatype_item_position: urust_datatype -> Position.T

  val generic_argument_source: generic_arg -> Input.source
  val path_position: ur_path -> Position.T
  val path_head: ur_path -> path_head
  val is_primitive_path: ur_path -> bool
  val path_segments: ur_path -> path_segment list
  val is_qualified_path: ur_path -> bool
  val segment_identifier: path_segment -> string * Position.T
  val segment_generic_args: path_segment -> generic_args option
  val final_segment: ur_path -> path_segment
  val remove_final_generic_args: ur_path -> ur_path
  val render_path: ur_path -> string
  val make_single_path: string * Position.T -> ur_path
  val make_primitive_path:
    primitive_type * Position.T * path_segment -> ur_path

  datatype ur_pat =
      P_Wild of Position.T
    | P_Ident of string * Position.T
    | P_Path of ur_path
    | P_Literal of literal_payload
    | P_Constr of ur_path * ur_pat list * source_layout
    | P_Tuple of ur_pat list * source_layout
    | P_Group of ur_pat * source_layout
    | P_Borrow of borrow_mode * ur_pat * source_layout
    | P_Alias of string * Position.T * ur_pat * source_layout
    | P_Range of range_kind * ur_pat * ur_pat * source_layout
    | P_Slice of slice_item list * source_layout
    | P_Struct of ur_path * struct_field list * source_layout
    | P_Or of ur_pat list * source_layout
  and slice_item =
      SI_Pat of ur_pat
    | SI_Rest of Position.T
  and struct_field =
      SF_Field of string * Position.T * ur_pat
    | SF_Shorthand of string * Position.T
    | SF_Rest of Position.T

  datatype match_flavour = MF_Switch | MF_Case | MF_Auto

  datatype binop =
      Add | Sub | Mul | Div | Mod
    | Shl | Shr
    | BAnd | BOr | BXor
    | Eq | Ne | Lt | Le | Gt | Ge
    | And | Or
  datatype unaryop =
      U_Not
    | U_Borrow of borrow_mode
    | U_Deref
    | U_Propagate
  datatype assign_binop =
      AssignSub | AssignMul | AssignMod
    | AssignBAnd | AssignBOr | AssignBXor
    | AssignShl | AssignShr
  datatype assignop =
      Assign
    | AssignAdd
    | AssignBin of assign_binop

  datatype array_repeat_mode =
      AR_Ordinary
    | AR_InlineConst
  datatype repeat_length =
      RL_Integer of integer_literal
    | RL_Path of ur_path
    | RL_Bin of binop * repeat_length * repeat_length * source_layout
    | RL_Group of repeat_length * source_layout
    | RL_CastUsize of repeat_length * source_layout

  val repeat_length_position: repeat_length -> Position.T
  val repeat_length_source_layout: repeat_length -> source_layout

  datatype log_data_entry =
      LDE_String of string * Position.T
    | LDE_Identifier of string * Position.T

  datatype ur_callee =
      UC_Path of ur_path
    | UC_Method of ur_expr * path_segment
    | UC_Antiq of Input.source
    | UC_FunLiteral of
        value_antiquotation * int * Position.T * generic_args option

  and ur_expr =
      UE_Unit of source_layout
    | UE_Tuple of ur_expr list * source_layout
    | UE_Array of ur_expr list * source_layout
    | UE_ArrayRepeat of
        array_repeat_mode * ur_expr * repeat_length * source_layout
    | UE_Struct of ur_path * struct_expr_field list * source_layout
    | UE_Path of ur_path
    | UE_Literal of literal_payload
    | UE_ExprAntiq of Input.source
    | UE_Yield of source_layout
    | UE_Log of value_antiquotation * value_antiquotation * source_layout
    | UE_LogData of log_data_entry list * source_layout
    | UE_Closure of ur_pat list * ur_expr * source_layout
    | UE_Let of ur_pat * ur_expr * ur_expr * source_layout
    | UE_LetMut of ur_pat * ur_expr * ur_expr * source_layout
    | UE_Const of ur_pat * ur_expr * ur_expr * source_layout
    | UE_Seq of ur_expr * ur_expr * source_layout
    | UE_Return of ur_expr option * source_layout
    | UE_Bin of binop * ur_expr * ur_expr * source_layout
    | UE_Cast of ur_expr * source_cast_target * source_layout
    | UE_Unary of unaryop * ur_expr * source_layout
    | UE_Group of ur_expr * source_layout
    | UE_Block of ur_expr * source_layout
    | UE_If of ur_expr * ur_expr * ur_expr option * source_layout
    | UE_IfLet of
        ur_pat * ur_expr * ur_expr * ur_expr option * source_layout
    | UE_LetElse of
        ur_pat * ur_expr * ur_expr * ur_expr * source_layout
    | UE_While of Input.source * ur_expr * ur_expr * source_layout
    | UE_Loop of Input.source * ur_expr * source_layout
    | UE_For of ur_pat * ur_expr * ur_expr * source_layout
    | UE_WhileLet of Input.source * ur_pat * ur_expr * ur_expr * source_layout
    | UE_Call of ur_callee * ur_expr list * source_layout
    | UE_Field of ur_expr * string * source_layout
    | UE_Index of ur_expr * ur_expr * source_layout
    | UE_TupleProjection of ur_expr * int * source_layout
    | UE_Range of range_kind * ur_expr * ur_expr * source_layout
    | UE_Assign of assignop * ur_place * ur_expr * source_layout
    | UE_Macro of
        ur_path * macro_payload * source_layout
    | UE_Match of match_flavour * ur_expr * ur_arm list * source_layout
  and struct_expr_field =
      SE_Field of string * Position.T * ur_expr
  and macro_payload =
      MP_Arguments of ur_expr list
    | MP_Matches of ur_expr * ur_pat
  and ur_place =
      UP_Path of ur_path
    | UP_Deref of ur_expr * source_layout
    | UP_Field of ur_place * string * source_layout
    | UP_Index of ur_place * ur_expr * source_layout
    | UP_Antiq of Input.source
  and ur_arm =
      UR_Arm of ur_pat * (ur_expr * Position.T) option * ur_expr * source_layout

  datatype function_parameter =
    Function_Parameter of
      Position.T option * ur_pat * rust_type * source_layout
  datatype urust_function =
    Function_Item of
      string * Position.T * function_parameter list *
      rust_type option * ur_expr * source_layout
  datatype urust_item =
      Datatype_Item of urust_datatype
    | Function_Item_Node of urust_function

  val function_item_position: urust_function -> Position.T
  val function_source_layout: urust_function -> source_layout
  val function_body: urust_function -> ur_expr
  val function_name: urust_function -> string * Position.T
  val function_parameters: urust_function -> function_parameter list
  val function_return_type: urust_function -> rust_type option
  val function_parameter_position: function_parameter -> Position.T
  val rust_snake_case: string -> string

  datatype parse_result =
      Parsed_Expression of ur_expr
    | Parsed_Item of urust_item

  val expression_position: ur_expr -> Position.T
  val expression_source_layout: ur_expr -> source_layout
  val pattern_position: ur_pat -> Position.T
  val pattern_source_layout: ur_pat -> source_layout
  val arm_source_layout: ur_arm -> source_layout
  val mk_assign:
    assignop * Position.T -> ur_expr -> ur_expr -> ur_expr
  val mk_array_repeat:
    array_repeat_mode * ur_expr * ur_expr * source_layout ->
      ur_expr
  val finish_statement: ur_expr * Position.T -> ur_expr
  val mk_bare_path_pat: ur_path -> ur_pat
  val mk_ctor_pat: ur_path * ur_pat list * source_layout -> ur_pat
  val mk_alias_pat:
    (string * Position.T) * ur_pat * source_layout -> ur_pat
  val mk_struct_pat: ur_path * struct_field list * source_layout -> ur_pat
  val mk_closure:
    ur_pat list * ur_expr * source_layout -> ur_expr
  val mk_call:
    ur_callee * ur_expr list * source_layout -> ur_expr
  val mk_tuple_projection:
    ur_expr * string * source_layout -> ur_expr
  val mk_let_else:
    ur_pat * ur_expr * ur_expr * ur_expr *
      source_layout -> ur_expr
  val mk_or_pat: ur_pat * ur_pat * source_layout -> ur_pat
end

(*
  URust_AST owns the reified, unresolved uRust syntax shared by the generated grammar and the
  elaboration pipeline.  Its boundary ends before name/constructor resolution, site-specific pattern
  validation, literal decoding, type checking, or construction of shallow-embedding terms.  Grammar
  actions construct this representation; Resolution, Patterns, and Translate may inspect it
  exhaustively. Consequently URUST_AST exposes the complete source representation plus only the
  invariant-preserving smart constructors needed by the grammar. Adding or reshaping a constructor
  requires updating every consumer.

  The public representation comprises:

    * source_layout and source_token. A source layout pairs the complete symbol-counted construct
      span with source-ordered exact ranges for denotational keywords, operators, delimiters, names,
      macro bangs, and literal subdivisions. Layouts are syntax metadata only: they do not select
      HOL constants or report semantic entities. The accessors preserve token multiplicity and order
      so a later phase can distinguish repeated controls such as the two bars of a closure or the two
      delimiters of a value antiquotation.
    * literal_payload and LP_Integer, LP_Bool, LP_String, LP_ValAntiq. Integer literals retain their
      raw spelling, complete span, exact numeric range, and optional exact suffix range. Strings
      retain their raw spelling. Value antiquotations retain their positioned body source plus a
      complete layout whose two Literal_Token entries identify the opening and closing delimiters.
    * canonical_fragment and Generic_Arg. A generic argument pairs the grammar-produced, trivia-free
      canonical fragment with its exact positioned source slice for later binder-aware HOL parsing.
      path_head distinguishes ordinary identifier-headed paths from the seven primitive-token-headed
      associated-item paths without discarding the common ordered segment representation.
    * borrow_mode (BM_Imm, BM_Mut), range_kind (RK_Exclusive, RK_Inclusive), unsigned_type
      (UT_U8, UT_U16, UT_U32, UT_U64, UT_Usize), signed_type (ST_I32, ST_I64),
      raw_pointer_mutability (RPM_Const, RPM_Mut), primitive cast_target (CT_Unsigned, CT_Signed,
      CT_RawPointer), source_cast_target (SCT_Primitive, SCT_Named), binop (Add, Sub, Mul, Div, Mod,
      Shl, Shr, BAnd, BOr, BXor, Eq, Ne, Lt, Le, Gt, Ge, And, Or), unaryop (U_Not, U_Borrow,
      U_Deref, U_Propagate), assign_binop (AssignSub, AssignMul, AssignMod, AssignBAnd, AssignBOr,
      AssignBXor, AssignShl, AssignShr), and assignop (Assign, AssignAdd, AssignBin). These tags
      describe surface operations only; their HOL constants and semantics belong to later modules.
      SCT_Primitive retains the exact primitive type-token position; SCT_Named retains an exact
      unresolved path for context-local cast-alias resolution.
      CT_RawPointer retains source mutability even though the current shallow frontend lowers const
      and mut targets identically. log_data_entry retains each quoted string or identifier in source
      order with its token position.
    * ur_pat and P_Wild, P_Ident, P_Literal, P_Constr, P_Tuple, P_Group, P_Borrow, P_Alias, P_Range,
      P_Slice, P_Struct, P_Or, together with slice_item (SI_Pat, SI_Rest) and struct_field (SF_Field,
      SF_Shorthand, SF_Rest). Lists retain source order; grammar-produced tuple lists contain at least
      two elements and P_Or alternatives are flattened. P_Ident deliberately does not decide binder
      versus constructor.
    * match_flavour and MF_Switch, MF_Case, MF_Auto.  MF_Auto requests downstream classification; it
      is not a fourth lowering.
    * array_repeat_mode (AR_Ordinary, AR_InlineConst) and repeat_length (RL_Integer, RL_Path,
      RL_Bin, RL_Group, RL_CastUsize). The repeat-length tree is produced by validating an ordinary
      parsed expression, so unsupported runtime constructs retain their smallest source position
      without entering repeat lowering.
    * the mutually recursive expression interface ur_expr (UE_Unit, UE_Tuple, UE_Array,
      UE_ArrayRepeat, UE_Struct, UE_Path, UE_Literal, UE_ExprAntiq, UE_Yield, UE_Log, UE_LogData,
      UE_Closure, UE_Let,
      UE_LetMut, UE_Const, UE_Seq, UE_Return, UE_Bin, UE_Cast, UE_Unary, UE_Group, UE_Block, UE_If,
      UE_IfLet, UE_LetElse, UE_While, UE_Loop, UE_For, UE_WhileLet, UE_Call, UE_Field, UE_Index,
      UE_TupleProjection, UE_Range, UE_Assign, UE_Macro, UE_Match),
      struct_expr_field (SE_Field),
      macro_payload
      (MP_Arguments, MP_Matches), ur_place (UP_Path, UP_Deref, UP_Field, UP_Index, UP_Antiq), and
      ur_arm (UR_Arm). Expression and pattern lists preserve source order. A generic macro payload
      retains every parsed argument without deciding which arguments a legacy macro lowers;
      MP_Matches retains its expression and pattern in separate grammar categories. A UR_Arm
      contains its pattern, an optional guard paired with the guard-keyword position, and its body.
      UE_Struct retains its complete head-through-closing-brace span and source-ordered SE_Field
      entries; each entry retains the syntax-only label, its position, and the initializer AST.
      UE_Log retains the two value-antiquotation operands, including their delimiter layouts, and its
      complete primitive-log span.
      UE_LogData retains a nonempty source-ordered entry list and its complete opener-through-closer
      span.
      UE_Closure retains ordered pattern-shaped formals and the full closure span; its grammar admits
      only identifier spellings, while the closure-formal lowering gate rejects the normalized
      wildcard.
      UE_IfLet retains an optional source else branch; UE_LetElse retains its fallback and required
      continuation separately. A UE_Return never stores a semicolon; a method invocation is
      represented as UC_Method and prepended during lowering; UC_Antiq retains the exact positioned
      embedded HOL callee source; UC_FunLiteral additionally retains the value-antiquotation
      delimiter layout, lift arity, suffix position, and optional restricted generic arguments.
      UE_TupleProjection retains its canonical numeric index and numeric-token position; it is a
      value postfix and deliberately has no ur_place counterpart. ur_place contains only validated
      assignment-target shapes.

  Position.T fields identify the single token documented at each constructor. Composite expressions,
  patterns, places, repeat lengths, and arms instead carry source_layout values; integer and
  value-antiquotation wrappers carry layouts for their audited literal subdivisions. Consumers may
  use either kind of source metadata for markup and diagnostics, but must not infer semantic
  validity from its presence. literal_position returns the complete source position of every literal
  payload; expression_position and pattern_position return complete construct spans.

  The remaining public functions are grammar-facing construction contracts. mk_assign accepts
  identifiers, expression antiquotations, dereferences, fields and indices over recursively valid
  places, and transparent groups as assignment targets; every other expression raises the positioned
  "invalid assignment target" error. mk_tuple_projection accepts only canonical unsuffixed decimal
  indices 0 through 15 and reports every other numeric token at that token's position.
  finish_statement leaves a terminal UE_Return unchanged and otherwise sequences the expression with
  UE_Unit at the semicolon. mk_bare_ident_pat normalises "_"
  to P_Wild; the other pattern smart constructors consume ordinary (name, position) pairs without a
  parser-only wrapper datatype. Grammar actions construct every layout from the symbol-counted token
  ranges supplied by Parser_Lex_Util; smart constructors preserve those layouts while checking AST
  invariants. mk_or_pat preserves source order while flattening a right-recursive P_Or.

  Constructor-resolution policy, legal-pattern subsets at each use site, lowering choices, and the
  private expression-position/place conversion helpers remain implementation details. Directly
  constructing values outside the grammar does not imply that the corresponding source form is
  accepted or semantically valid.
*)
structure URust_AST :> URUST_AST =
struct
  datatype source_token =
      Keyword_Token of string
    | Operator_Token
    | Delimiter_Token of string
    | Name_Token
    | Bang_Token
    | Literal_Token
  datatype source_layout =
    Source_Layout of Position.T * (source_token * Position.T) list

  fun make_source_layout span tokens =
    Source_Layout (span, tokens)
  fun source_span (Source_Layout (span, _)) = span
  fun source_tokens (Source_Layout (_, tokens)) = tokens
  fun source_token_positions layout token =
    source_tokens layout
    |> map_filter
        (fn (candidate, pos) =>
          if candidate = token then SOME pos else NONE)
  fun source_token_positions_for layout tokens =
    source_tokens layout
    |> map_filter
        (fn (candidate, pos) =>
          if member (op =) tokens candidate then SOME pos else NONE)
  fun source_token_position layout token =
    get_first
      (fn (candidate, pos) =>
        if candidate = token then SOME pos else NONE)
      (source_tokens layout)
  fun the_source_token_position layout token =
    (case source_token_position layout token of
       SOME pos => pos
     | NONE => error "uRust AST source layout is missing a required token")

  datatype integer_literal =
    Integer_Literal of string * source_layout * Position.T option
  datatype value_antiquotation =
    Value_Antiquotation of Input.source * source_layout
  datatype literal_payload =
      LP_Integer  of integer_literal
    | LP_Bool     of bool * Position.T
    | LP_String   of string * Position.T
    | LP_ValAntiq of value_antiquotation

  fun integer_literal_lexeme
      (Integer_Literal (lexeme, _, _)) = lexeme
  fun integer_literal_position
      (Integer_Literal (_, layout, _)) = source_span layout
  fun integer_literal_numeric_position
      (Integer_Literal (_, layout, _)) =
        the_source_token_position layout Literal_Token
  fun integer_literal_suffix_position
      (Integer_Literal (_, _, suffix_pos)) = suffix_pos

  fun value_antiquotation_source
      (Value_Antiquotation (source, _)) = source
  fun value_antiquotation_source_layout
      (Value_Antiquotation (_, layout)) = layout

  fun literal_position (LP_Integer integer) =
        integer_literal_position integer
    | literal_position (LP_Bool (_, pos)) = pos
    | literal_position (LP_String (_, pos)) = pos
    | literal_position (LP_ValAntiq antiquotation) =
        source_span
          (value_antiquotation_source_layout antiquotation)

  fun literal_source_layout payload =
    (case payload of
       LP_Integer (Integer_Literal (_, layout, _)) => layout
     | LP_Bool (value, pos) =>
         make_source_layout pos
           [(Keyword_Token
              (if value then "true" else "false"), pos)]
     | LP_String (_, pos) => make_source_layout pos []
     | LP_ValAntiq antiquotation =>
         value_antiquotation_source_layout antiquotation)

  (* THE pattern language: ONE datatype for EVERY binding site (let / const binder, match_switch key,
     match_case arm, and later closure params, `for` patterns, fn parameters) -- Rust has one pattern
     grammar, whose sites differ only in which patterns are LEGAL there, so each site's elaborator gates
     what it accepts with a positioned error instead of the grammar forking (D28). A bare id's ROLE
     (nullary ctor vs variable binder) needs native code-constructor or case-translation metadata,
     invisible to the parser -- hence one `P_Ident`. Adding a pattern form = ONE constructor here +
     one clause per consuming site. *)
  datatype borrow_mode = BM_Imm | BM_Mut
  datatype range_kind = RK_Exclusive | RK_Inclusive
  datatype unsigned_type = UT_U8 | UT_U16 | UT_U32 | UT_U64 | UT_Usize
  datatype signed_type = ST_I32 | ST_I64
  datatype raw_pointer_mutability = RPM_Const | RPM_Mut
  datatype cast_target =
      CT_Unsigned of unsigned_type
    | CT_Signed of signed_type
    | CT_RawPointer of raw_pointer_mutability * unsigned_type

  type canonical_fragment = string
  datatype generic_arg =
    Generic_Arg of canonical_fragment * Input.source
  datatype generic_args =
    Generic_Args of generic_arg list * Position.T
  datatype path_segment =
    Path_Segment of string * Position.T * generic_args option
  datatype primitive_type =
      Primitive_Unsigned of unsigned_type
    | Primitive_Signed of signed_type
  datatype path_head =
      Identifier_Head
    | Primitive_Head of primitive_type
  datatype ur_path =
    UR_Path of path_head * path_segment list * Position.T

  datatype source_cast_target =
      SCT_Primitive of cast_target * Position.T
    | SCT_Named of ur_path

  fun source_cast_target_type_position
      (SCT_Primitive (_, pos)) = SOME pos
    | source_cast_target_type_position (SCT_Named _) = NONE

  datatype rust_primitive_type =
      DPT_U8
    | DPT_U16
    | DPT_U32
    | DPT_U64
    | DPT_U128
    | DPT_Usize
    | DPT_I8
    | DPT_I16
    | DPT_I32
    | DPT_I64
    | DPT_I128
    | DPT_Isize
    | DPT_Bool
    | DPT_Char
    | DPT_Str
    | DPT_Never
    | DPT_Unit
  datatype rust_type =
      Primitive_Type of rust_primitive_type * Position.T
    | Path_Type of rust_type_path_segment list * source_layout
    | Tuple_Type of rust_type list * source_layout
    | Group_Type of rust_type * source_layout
    | Reference_Type of borrow_mode * rust_type * source_layout
    | Raw_Pointer_Type of
        raw_pointer_mutability * rust_type * source_layout
    | Slice_Type of rust_type * source_layout
    | Array_Type of rust_type * integer_literal * source_layout
    | HOL_Type_Source of Input.source
  and rust_generic_argument =
      Rust_Type_Argument of rust_type
    | Rust_Numeric_Argument of integer_literal
  and rust_type_path_segment =
    Rust_Type_Path_Segment of
      string * Position.T * rust_generic_argument list option * source_layout

  type datatype_type = rust_type
  datatype datatype_field =
    Datatype_Field of string * Position.T * datatype_type
  datatype datatype_shape =
      Unit_Shape
    | Tuple_Shape of datatype_type list
    | Named_Shape of datatype_field list
  datatype datatype_variant =
    Datatype_Variant of string * Position.T * datatype_shape
  datatype urust_datatype =
      Struct_Item of
        string * Position.T * datatype_shape * Position.T
    | Enum_Item of
        string * Position.T * datatype_variant list * Position.T

  fun rust_type_position (Primitive_Type (_, pos)) = pos
    | rust_type_position (Path_Type (_, layout)) = source_span layout
    | rust_type_position (Tuple_Type (_, layout)) = source_span layout
    | rust_type_position (Group_Type (_, layout)) = source_span layout
    | rust_type_position (Reference_Type (_, _, layout)) = source_span layout
    | rust_type_position (Raw_Pointer_Type (_, _, layout)) = source_span layout
    | rust_type_position (Slice_Type (_, layout)) = source_span layout
    | rust_type_position (Array_Type (_, _, layout)) = source_span layout
    | rust_type_position (HOL_Type_Source source) = Input.pos_of source

  val datatype_type_position = rust_type_position

  fun datatype_item_position
      (Struct_Item (_, _, _, pos)) = pos
    | datatype_item_position
      (Enum_Item (_, _, _, pos)) = pos

  fun generic_argument_canonical (Generic_Arg (canonical, _)) = canonical
  fun generic_argument_source (Generic_Arg (_, source)) = source

  fun path_position (UR_Path (_, _, pos)) = pos
  fun path_head (UR_Path (head, _, _)) = head
  fun is_primitive_path path =
    (case path_head path of
       Identifier_Head => false
     | Primitive_Head _ => true)
  fun path_segments (UR_Path (_, segments, _)) = segments
  fun is_qualified_path (UR_Path (_, _ :: _ :: _, _)) = true
    | is_qualified_path _ = false
  fun segment_identifier (Path_Segment (name, pos, _)) = (name, pos)
  fun segment_generic_args (Path_Segment (_, _, arguments)) = arguments
  fun final_segment (UR_Path (_, segments, _)) =
    (case rev segments of
       segment :: _ => segment
     | [] => error "urust_expr: internal empty path")
  fun remove_final_generic_args (UR_Path (head, segments, pos)) =
    (case rev segments of
       Path_Segment (name, name_pos, _) :: rest =>
         UR_Path
           (head, rev (Path_Segment (name, name_pos, NONE) :: rest), pos)
     | [] => error "urust_expr: internal empty path")
  fun render_generic_args (Generic_Args (arguments, _)) =
    "::<" ^
      space_implode ","
        (map generic_argument_canonical arguments) ^
      ">"
  fun render_segment (Path_Segment (name, _, arguments)) =
    name ^ the_default "" (Option.map render_generic_args arguments)
  fun render_path (UR_Path (_, segments, _)) =
    space_implode "::" (map render_segment segments)
  fun make_single_path (name, pos) =
    UR_Path
      (Identifier_Head, [Path_Segment (name, pos, NONE)], pos)
  fun primitive_name (Primitive_Unsigned UT_U8) = "u8"
    | primitive_name (Primitive_Unsigned UT_U16) = "u16"
    | primitive_name (Primitive_Unsigned UT_U32) = "u32"
    | primitive_name (Primitive_Unsigned UT_U64) = "u64"
    | primitive_name (Primitive_Unsigned UT_Usize) = "usize"
    | primitive_name (Primitive_Signed ST_I32) = "i32"
    | primitive_name (Primitive_Signed ST_I64) = "i64"
  fun make_primitive_path (primitive, primitive_pos, segment) =
    let
      val head_segment =
        Path_Segment
          (primitive_name primitive, primitive_pos, NONE)
    in
      UR_Path
        (Primitive_Head primitive,
         [head_segment, segment],
         Position.range_position
           (primitive_pos,
            Parser_Lex_Util.exclusive_end
              (case segment_generic_args segment of
                 NONE => #2 (segment_identifier segment)
               | SOME (Generic_Args (_, pos)) => pos)))
    end

  datatype ur_pat =
      P_Wild   of Position.T                          (* _ *)
    | P_Ident  of string * Position.T                 (* bare id: nullary ctor OR variable binder *)
    | P_Path   of ur_path
    | P_Literal of literal_payload                    (* numeral switch key or equality pattern *)
    | P_Constr of ur_path * ur_pat list * source_layout
    | P_Tuple  of ur_pat list * source_layout         (* (p0, p1, ..), at least two elements *)
    | P_Group  of ur_pat * source_layout              (* (p), transparent wrapper *)
    | P_Borrow of borrow_mode * ur_pat * source_layout
                                                       (* &p / & mut p; syntax-only today *)
    | P_Alias  of string * Position.T * ur_pat * source_layout
                                                       (* name @ p *)
    | P_Range  of range_kind * ur_pat * ur_pat * source_layout
                                                       (* lo..hi / lo..=hi *)
    | P_Slice  of slice_item list * source_layout     (* [p, .., q] *)
    | P_Struct of ur_path * struct_field list * source_layout
                                                       (* Head { fields } *)
    | P_Or     of ur_pat list * source_layout         (* p | q | r  (flattened; source order) *)
  and slice_item =
      SI_Pat of ur_pat
    | SI_Rest of Position.T
  and struct_field =
      SF_Field of string * Position.T * ur_pat
    | SF_Shorthand of string * Position.T
    | SF_Rest of Position.T

  (* Which `match` surface keyword an arm set came from; the two lower DIFFERENTLY (see UE_Match), so the
     flavour is a tag rather than separate AST nodes -- the bare `match` keyword then becomes a third
     flavour that CLASSIFIES its arms into one of these two lowerings (D28/D32). *)
  datatype match_flavour = MF_Switch | MF_Case | MF_Auto

  (* Binary operators map to HOL constants. Unary source forms share one tagged node while the grammar
     retains their distinct prefix/postfix fixity and precedence tiers. *)
  datatype binop =
      Add | Sub | Mul | Div | Mod              (* + - * / %       *)
    | Shl | Shr                                (* << >>           *)
    | BAnd | BOr | BXor                        (* & | ^  (infix)  *)
    | Eq | Ne | Lt | Le | Gt | Ge              (* == != < <= > >= *)
    | And | Or                                 (* && ||           *)
  datatype unaryop =
      U_Not
    | U_Borrow of borrow_mode
    | U_Deref
    | U_Propagate
  datatype assign_binop =
      AssignSub | AssignMul | AssignMod
    | AssignBAnd | AssignBOr | AssignBXor
    | AssignShl | AssignShr
  datatype assignop =
      Assign
    | AssignAdd
    | AssignBin of assign_binop

  datatype array_repeat_mode =
      AR_Ordinary
    | AR_InlineConst
  datatype repeat_length =
      RL_Integer of integer_literal
    | RL_Path of ur_path
    | RL_Bin of binop * repeat_length * repeat_length * source_layout
    | RL_Group of repeat_length * source_layout
    | RL_CastUsize of repeat_length * source_layout

  fun repeat_length_position (RL_Integer integer) =
        integer_literal_position integer
    | repeat_length_position (RL_Path path) = path_position path
    | repeat_length_position (RL_Bin (_, _, _, layout)) =
        source_span layout
    | repeat_length_position (RL_Group (_, layout)) =
        source_span layout
    | repeat_length_position (RL_CastUsize (_, layout)) =
        source_span layout

  fun repeat_length_source_layout (RL_Integer integer) =
        let
          val Integer_Literal (_, layout, _) = integer
        in layout end
    | repeat_length_source_layout (RL_Path path) =
        make_source_layout (path_position path) []
    | repeat_length_source_layout (RL_Bin (_, _, _, layout)) = layout
    | repeat_length_source_layout (RL_Group (_, layout)) = layout
    | repeat_length_source_layout (RL_CastUsize (_, layout)) = layout

  datatype log_data_entry =
      LDE_String of string * Position.T
    | LDE_Identifier of string * Position.T

  datatype ur_callee =
      UC_Path of ur_path
    | UC_Method of ur_expr * path_segment
    | UC_Antiq of Input.source
    | UC_FunLiteral of
        value_antiquotation * int * Position.T * generic_args option

  and ur_expr =
      UE_Unit      of source_layout                   (* () *)
    | UE_Tuple     of ur_expr list * source_layout    (* (e0, e1, ..), at least two elements *)
    | UE_Array     of ur_expr list * source_layout    (* [e0, e1, ..], including empty *)
    | UE_ArrayRepeat of
        array_repeat_mode * ur_expr * repeat_length * source_layout
                                                      (* [value; length] / [const { value }; length] *)
    | UE_Struct    of ur_path * struct_expr_field list * source_layout
                                                      (* Head { label: value, ... }, at full span *)
    | UE_Path      of ur_path
    | UE_Literal   of literal_payload                 (* integer / bool / string / <<value>> *)
    | UE_ExprAntiq of Input.source                    (* eps<e> body as a POSITIONED source -> e *)
    | UE_Yield     of source_layout                   (* yield -> pause *)
    | UE_Log       of value_antiquotation * value_antiquotation * source_layout
                                                      (* log <<priority>> <<data>>, at full span *)
    | UE_LogData   of log_data_entry list * source_layout
                                                      (* l<<"text", value>>, at full span *)
    | UE_Closure   of ur_pat list * ur_expr * source_layout
                                                      (* |x, ...| body / || body, at full span *)
    | UE_Let       of ur_pat * ur_expr * ur_expr * source_layout
                                                      (* let <pat> = rhs; body -> bind *)
    | UE_LetMut    of ur_pat * ur_expr * ur_expr * source_layout
                                                      (* let mut <pat> = rhs; body *)
    | UE_Const     of ur_pat * ur_expr * ur_expr * source_layout
                                                      (* const: same desugaring as let today; distinct node
                                                         keeps the keyword for when it diverges (B7) *)
    | UE_Seq       of ur_expr * ur_expr * source_layout
                                                      (* e1; e2 -> sequence (trailing `;`: e2 = unit) *)
    | UE_Return    of ur_expr option * source_layout  (* return [value]; semicolon is never stored *)
    | UE_Bin       of binop * ur_expr * ur_expr * source_layout
                                                      (* a <binop> b *)
    | UE_Cast      of ur_expr * source_cast_target * source_layout
                                                      (* operand as target, at the `as` keyword *)
    | UE_Unary     of unaryop * ur_expr * source_layout
                                                      (* !a / &a / & mut a / *a / a? *)
    | UE_Group     of ur_expr * source_layout         (* (a), transparent during lowering *)
    | UE_Block     of ur_expr * source_layout         (* { stmts } -- ERASES to <stmts>, no `scoped`
                                                         wrapper: `_urust_scoping` is identity (D22) *)
    | UE_If        of ur_expr * ur_expr * ur_expr option * source_layout
                                                      (* NONE else-branch = one-armed -> skip (D22) *)
    | UE_IfLet     of
        ur_pat * ur_expr * ur_expr * ur_expr option * source_layout
                                                      (* if let pattern = value { success } [else] *)
    | UE_LetElse   of
        ur_pat * ur_expr * ur_expr * ur_expr * source_layout
                                                      (* let pattern = value else fallback; continuation *)
    | UE_While     of Input.source * ur_expr * ur_expr * source_layout
                                                      (* #[fuel(eps<n>)] while (condition) body *)
    | UE_Loop      of Input.source * ur_expr * source_layout
                                                      (* #[fuel(eps<n>)] loop body *)
    | UE_For       of ur_pat * ur_expr * ur_expr * source_layout
                                                      (* for pattern in iterable body *)
    | UE_WhileLet  of Input.source * ur_pat * ur_expr * ur_expr * source_layout
                                                      (* #[fuel(eps<n>)] while let pattern = value body *)
    | UE_Call      of ur_callee * ur_expr list * source_layout
                                                      (* callee(a0..aN) -> funcallN. Paths/methods use
                                                         NFunction resolution; antiquotations are direct
                                                         embedded HOL callees; function literals first
                                                         apply lift_funN and optional generic parameters.
                                                         Args and the complete call span are retained so
                                                         an arity error underlines the whole invocation. *)
    | UE_Field     of ur_expr * string * source_layout
                                                      (* e.field -> NField lens focus *)
    | UE_Index     of ur_expr * ur_expr * source_layout
                                                      (* e[i] -> index_const, at full span *)
    | UE_TupleProjection of ur_expr * int * source_layout
                                                      (* e.N -> tuple_index_N, at numeric token *)
    | UE_Range     of range_kind * ur_expr * ur_expr * source_layout
                                                      (* lo..hi / lo..=hi, at operator *)
    | UE_Assign    of assignop * ur_place * ur_expr * source_layout
                                                      (* place assignment-op rhs, at the operator *)
    | UE_Macro     of
        ur_path * macro_payload * source_layout       (* head, payload, source layout *)
    | UE_Match     of match_flavour * ur_expr * ur_arm list * source_layout
                                                      (* match_<flavour> scrut { pat => body, .. }. ONE node
                                                         for both keywords; only the LOWERING differs --
                                                         MF_Switch -> ncase_selector (first-order, D26),
                                                         MF_Case -> the Ctr_Sugar case skeleton (D27). Each
                                                         flavour's elaborator gates the patterns it cannot
                                                         lower with a positioned error. *)
  and struct_expr_field =
      SE_Field of string * Position.T * ur_expr
  and macro_payload =
      MP_Arguments of ur_expr list
    | MP_Matches of ur_expr * ur_pat
  and ur_place =
      UP_Path of ur_path
    | UP_Deref of ur_expr * source_layout
    | UP_Field of ur_place * string * source_layout
    | UP_Index of ur_place * ur_expr * source_layout
    | UP_Antiq of Input.source
  and ur_arm =
      UR_Arm of ur_pat * (ur_expr * Position.T) option * ur_expr * source_layout

  datatype function_parameter =
    Function_Parameter of
      Position.T option * ur_pat * rust_type * source_layout
  datatype urust_function =
    Function_Item of
      string * Position.T * function_parameter list *
      rust_type option * ur_expr * source_layout
  datatype urust_item =
      Datatype_Item of urust_datatype
    | Function_Item_Node of urust_function

  fun function_item_position
      (Function_Item (_, _, _, _, _, layout)) = source_span layout

  fun function_source_layout
      (Function_Item (_, _, _, _, _, layout)) = layout

  fun function_body
      (Function_Item (_, _, _, _, body, _)) = body

  fun function_name
      (Function_Item (name, pos, _, _, _, _)) = (name, pos)

  fun function_parameters
      (Function_Item (_, _, parameters, _, _, _)) = parameters

  fun function_return_type
      (Function_Item (_, _, _, return_type, _, _)) = return_type

  fun function_parameter_position
      (Function_Parameter (_, _, _, layout)) = source_span layout

  fun ascii_lower character =
    if #"A" <= character andalso character <= #"Z"
    then Char.chr
      (Char.ord character + Char.ord #"a" - Char.ord #"A")
    else character

  fun rust_snake_case name =
    let
      val characters = String.explode name
      fun upper character =
        #"A" <= character andalso character <= #"Z"
      fun lower character =
        #"a" <= character andalso character <= #"z"
      fun digit character =
        #"0" <= character andalso character <= #"9"
      fun previous index =
        if index = 0 then NONE else SOME (nth characters (index - 1))
      fun following index =
        if index + 1 >= length characters
        then NONE
        else SOME (nth characters (index + 1))
      fun boundary index character =
        upper character andalso index > 0 andalso
          (case previous index of
             SOME previous_character =>
               lower previous_character orelse
               digit previous_character orelse
               (upper previous_character andalso
                 (case following index of
                    SOME following_character => lower following_character
                  | NONE => false))
           | NONE => false)
      fun convert (index, character) =
        (if boundary index character then "_" else "") ^
          String.str (ascii_lower character)
    in String.concat (map_index convert characters) end

  datatype parse_result =
      Parsed_Expression of ur_expr
    | Parsed_Item of urust_item

  fun expression_source_layout (UE_Unit layout) = layout
    | expression_source_layout (UE_Tuple (_, layout)) = layout
    | expression_source_layout (UE_Array (_, layout)) = layout
    | expression_source_layout (UE_ArrayRepeat (_, _, _, layout)) = layout
    | expression_source_layout (UE_Struct (_, _, layout)) = layout
    | expression_source_layout (UE_Path path) =
        make_source_layout (path_position path) []
    | expression_source_layout (UE_Literal payload) =
        literal_source_layout payload
    | expression_source_layout (UE_ExprAntiq source) =
        make_source_layout (Input.pos_of source) []
    | expression_source_layout (UE_Yield layout) = layout
    | expression_source_layout (UE_Log (_, _, layout)) = layout
    | expression_source_layout (UE_LogData (_, layout)) = layout
    | expression_source_layout (UE_Closure (_, _, layout)) = layout
    | expression_source_layout (UE_Let (_, _, _, layout)) = layout
    | expression_source_layout (UE_LetMut (_, _, _, layout)) = layout
    | expression_source_layout (UE_Const (_, _, _, layout)) = layout
    | expression_source_layout (UE_Seq (_, _, layout)) = layout
    | expression_source_layout (UE_Return (_, layout)) = layout
    | expression_source_layout (UE_Bin (_, _, _, layout)) = layout
    | expression_source_layout (UE_Cast (_, _, layout)) = layout
    | expression_source_layout (UE_Unary (_, _, layout)) = layout
    | expression_source_layout (UE_Group (_, layout)) = layout
    | expression_source_layout (UE_Block (_, layout)) = layout
    | expression_source_layout (UE_If (_, _, _, layout)) = layout
    | expression_source_layout (UE_IfLet (_, _, _, _, layout)) = layout
    | expression_source_layout (UE_LetElse (_, _, _, _, layout)) = layout
    | expression_source_layout (UE_While (_, _, _, layout)) = layout
    | expression_source_layout (UE_Loop (_, _, layout)) = layout
    | expression_source_layout (UE_For (_, _, _, layout)) = layout
    | expression_source_layout (UE_WhileLet (_, _, _, _, layout)) = layout
    | expression_source_layout (UE_Call (_, _, layout)) = layout
    | expression_source_layout (UE_Field (_, _, layout)) = layout
    | expression_source_layout (UE_Index (_, _, layout)) = layout
    | expression_source_layout (UE_TupleProjection (_, _, layout)) = layout
    | expression_source_layout (UE_Range (_, _, _, layout)) = layout
    | expression_source_layout (UE_Assign (_, _, _, layout)) = layout
    | expression_source_layout (UE_Macro (_, _, layout)) = layout
    | expression_source_layout (UE_Match (_, _, _, layout)) = layout

  fun expression_position expression =
    source_span (expression_source_layout expression)

  fun pattern_source_layout (P_Wild pos) =
        make_source_layout pos [(Name_Token, pos)]
    | pattern_source_layout (P_Ident (_, pos)) =
        make_source_layout pos [(Name_Token, pos)]
    | pattern_source_layout (P_Path path) =
        make_source_layout (path_position path) []
    | pattern_source_layout (P_Literal payload) =
        literal_source_layout payload
    | pattern_source_layout (P_Constr (_, _, layout)) = layout
    | pattern_source_layout (P_Tuple (_, layout)) = layout
    | pattern_source_layout (P_Group (_, layout)) = layout
    | pattern_source_layout (P_Borrow (_, _, layout)) = layout
    | pattern_source_layout (P_Alias (_, _, _, layout)) = layout
    | pattern_source_layout (P_Range (_, _, _, layout)) = layout
    | pattern_source_layout (P_Slice (_, layout)) = layout
    | pattern_source_layout (P_Struct (_, _, layout)) = layout
    | pattern_source_layout (P_Or (_, layout)) = layout

  fun pattern_position pattern =
    source_span (pattern_source_layout pattern)

  fun arm_source_layout (UR_Arm (_, _, _, layout)) = layout

  fun spanning_position left right =
    Position.range_position
      (left, Parser_Lex_Util.exclusive_end right)

  fun expression_diagnostic_position expression =
    let
      fun locally_meaningful
          (Operator_Token, pos) = SOME pos
        | locally_meaningful
          (Name_Token, pos) = SOME pos
        | locally_meaningful
          (Keyword_Token _, pos) = SOME pos
        | locally_meaningful
          (Bang_Token, pos) = SOME pos
        | locally_meaningful _ = NONE
    in
      the_default (expression_position expression)
        (get_first locally_meaningful
          (source_tokens
            (expression_source_layout expression)))
    end

  (* Assignment parses an ordinary expression on the left, then crosses this one validation boundary.
     Keeping target recognition out of the grammar gives every invalid expression a stable positioned
     diagnostic and lets grouped/dereferenced field chains compose without parallel productions. *)
  fun expr_to_place (UE_Path path) =
        if is_primitive_path path then
          error
            ("urust_expr: primitive associated-item path is not an assignment target" ^
              Position.here (path_position path))
        else UP_Path path
    | expr_to_place (UE_ExprAntiq src) = UP_Antiq src
    | expr_to_place (UE_Group (expr, _)) = expr_to_place expr
    | expr_to_place (UE_Unary (U_Deref, expr, layout)) =
        UP_Deref (expr, layout)
    | expr_to_place (UE_Field (base, name, layout)) =
        UP_Field (expr_to_place base, name, layout)
    | expr_to_place (UE_Index (base, index, layout)) =
        UP_Index (expr_to_place base, index, layout)
    | expr_to_place expr =
        error ("urust_expr: invalid assignment target" ^
          Position.here (expression_diagnostic_position expr))

  fun mk_assign (aop, pos) lhs rhs =
    UE_Assign
      (aop, expr_to_place lhs, rhs,
       make_source_layout
         (spanning_position
           (expression_position lhs) (expression_position rhs))
         [(Operator_Token, pos)])

  fun mk_array_repeat (mode, value, raw_length, layout) =
    let
      fun repeat_operator Add = true
        | repeat_operator Sub = true
        | repeat_operator Mul = true
        | repeat_operator Div = true
        | repeat_operator Mod = true
        | repeat_operator _ = false

      fun invalid expression =
        error
          ("urust_expr: array repeat length supports only integer literals, symbolic length paths, " ^
            "parentheses, `+`, `-`, `*`, `/`, `%`, and `as usize`" ^
            Position.here
              (expression_diagnostic_position expression))

      fun validate expression =
        (case expression of
           UE_Literal (LP_Integer integer) => RL_Integer integer
         | UE_Path path => RL_Path path
         | UE_Bin (operator, left_operand, right_operand, expression_layout) =>
             if repeat_operator operator
             then
               RL_Bin
                 (operator, validate left_operand,
                  validate right_operand, expression_layout)
             else invalid expression
         | UE_Group (inner, expression_layout) =>
             RL_Group (validate inner, expression_layout)
         | UE_Cast
             (inner, SCT_Primitive (CT_Unsigned UT_Usize, _),
              expression_layout) =>
             RL_CastUsize (validate inner, expression_layout)
         | _ => invalid expression)
    in
      UE_ArrayRepeat
        (mode, value, validate raw_length, layout)
    end

  (* A terminal return statement keeps the return expression instead of sequencing it with unit. *)
  fun finish_statement (return as UE_Return _, _) = return
    | finish_statement (expression, semi_pos) =
        let
          val unit_layout = make_source_layout semi_pos []
          val sequence_layout =
            make_source_layout
              (spanning_position
                (expression_position expression) semi_pos)
              [(Delimiter_Token ";", semi_pos)]
        in
          UE_Seq (expression, UE_Unit unit_layout, sequence_layout)
        end

  (* `_` lexes as an ordinary IDENT: normalise to P_Wild in ONE place, not an `= "_"` test at every site. *)
  fun mk_bare_path_pat path =
    (case path_segments path of
       [Path_Segment ("_", pos, NONE)] => P_Wild pos
     | [Path_Segment (name, pos, NONE)] => P_Ident (name, pos)
     | _ => P_Path path)
  fun mk_ctor_pat (path, args, layout) = P_Constr (path, args, layout)
  fun mk_alias_pat ((name, pos), inner, layout) =
    P_Alias (name, pos, inner, layout)
  fun mk_struct_pat (path, fields, layout) =
    P_Struct (path, fields, layout)

  fun mk_closure (formals, body, layout) =
    UE_Closure (formals, body, layout)
  fun mk_call (callee, args, layout) =
    UE_Call (callee, args, layout)

  fun mk_tuple_projection (receiver, raw, layout) =
    let
      val pos = the_source_token_position layout Name_Token
      fun invalid () =
        error
          ("urust_expr: invalid tuple projection index " ^ quote raw ^
            " (expected an unsuffixed decimal integer from 0 through 15)" ^
            Position.here pos)
    in
      (case Int.fromString raw of
         SOME index =>
           if 0 <= index andalso index <= 15 andalso Int.toString index = raw
           then UE_TupleProjection (receiver, index, layout)
           else invalid ()
       | NONE => invalid ())
    end

  fun mk_let_else
      (pattern, scrutinee, fallback, continuation, layout) =
    UE_LetElse
      (pattern, scrutinee, fallback, continuation, layout)

  (* The grammar is right-recursive, so prepend the left alternative in O(1) while retaining source order. *)
  fun mk_or_pat (p, P_Or (alternatives, right_layout), layout) =
        P_Or
          (p :: alternatives,
           make_source_layout
             (spanning_position
               (pattern_position p) (source_span right_layout))
             (source_tokens layout @ source_tokens right_layout))
    | mk_or_pat (p, q, layout) =
        P_Or ([p, q], layout)
end
\<close>

end
