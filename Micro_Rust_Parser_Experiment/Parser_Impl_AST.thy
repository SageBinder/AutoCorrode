theory Parser_Impl_AST
  imports Main
begin

section\<open> Reified AST \<close>

text\<open> One constructor per uRust surface form. Positions are carried for markup/diagnostics. \<close>
ML\<open>
signature URUST_AST =
sig
  datatype literal_payload =
      LP_Integer of string * Position.T
    | LP_Bool of bool * Position.T
    | LP_String of string * Position.T
    | LP_ValAntiq of Input.source

  val literal_position: literal_payload -> Position.T

  datatype borrow_mode = BM_Imm | BM_Mut
  datatype range_kind = RK_Exclusive | RK_Inclusive

  datatype ur_pat =
      P_Wild of Position.T
    | P_Ident of string * Position.T
    | P_Literal of literal_payload
    | P_Constr of string * Position.T * ur_pat list
    | P_Tuple of ur_pat list * Position.T
    | P_Group of ur_pat
    | P_Borrow of borrow_mode * ur_pat * Position.T
    | P_Alias of string * Position.T * ur_pat * Position.T
    | P_Range of range_kind * ur_pat * ur_pat * Position.T
    | P_Slice of slice_item list * Position.T
    | P_Struct of string * Position.T * struct_field list
    | P_Or of ur_pat list * Position.T
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

  datatype ur_expr =
      UE_Unit of Position.T
    | UE_Tuple of ur_expr list * Position.T
    | UE_Array of ur_expr list * Position.T
    | UE_Ident of string * Position.T
    | UE_Literal of literal_payload
    | UE_ExprAntiq of Input.source
    | UE_Let of ur_pat * ur_expr * ur_expr
    | UE_LetMut of ur_pat * ur_expr * ur_expr * Position.T
    | UE_Const of ur_pat * ur_expr * ur_expr
    | UE_Seq of ur_expr * ur_expr
    | UE_Return of ur_expr option * Position.T
    | UE_Bin of binop * ur_expr * ur_expr * Position.T
    | UE_Unary of unaryop * ur_expr * Position.T
    | UE_Group of ur_expr * Position.T
    | UE_Block of ur_expr * Position.T
    | UE_If of ur_expr * ur_expr * ur_expr option * Position.T
    | UE_While of Input.source * ur_expr * ur_expr * Position.T
    | UE_Loop of Input.source * ur_expr * Position.T
    | UE_For of ur_pat * ur_expr * ur_expr * Position.T
    | UE_WhileLet of Input.source * ur_pat * ur_expr * ur_expr * Position.T
    | UE_Call of string * Position.T * ur_expr list * Position.T
    | UE_Field of ur_expr * string * Position.T
    | UE_Index of ur_expr * ur_expr * Position.T
    | UE_Range of range_kind * ur_expr * ur_expr * Position.T
    | UE_Assign of assignop * ur_place * ur_expr * Position.T
    | UE_Macro of
        string * Position.T * Position.T * macro_payload * Position.T
    | UE_Match of match_flavour * ur_expr * ur_arm list * Position.T
  and macro_payload =
      MP_Arguments of ur_expr list
    | MP_Matches of ur_expr * ur_pat
  and ur_place =
      UP_Ident of string * Position.T
    | UP_Deref of ur_expr * Position.T
    | UP_Field of ur_place * string * Position.T
    | UP_Index of ur_place * ur_expr * Position.T
    | UP_Antiq of Input.source
  and ur_arm =
      UR_Arm of ur_pat * (ur_expr * Position.T) option * ur_expr

  val expression_position: ur_expr -> Position.T
  val mk_assign:
    assignop * Position.T -> ur_expr -> ur_expr -> ur_expr
  val finish_statement: ur_expr * Position.T -> ur_expr
  val mk_bare_ident_pat: string * Position.T -> ur_pat
  val mk_ctor_pat: (string * Position.T) * ur_pat list -> ur_pat
  val mk_alias_pat:
    (string * Position.T) * ur_pat * Position.T -> ur_pat
  val mk_struct_pat:
    (string * Position.T) * struct_field list -> ur_pat
  val mk_call:
    string * Position.T * ur_expr list * Position.T * Position.T -> ur_expr
  val mk_method_call:
    ur_expr * string * Position.T * ur_expr list *
      Position.T * Position.T -> ur_expr
  val mk_or_pat: ur_pat * ur_pat * Position.T -> ur_pat
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

    * literal_payload and LP_Integer, LP_Bool, LP_String, LP_ValAntiq.  Integer and string payloads
      retain raw source spelling; antiquotations retain their positioned Input.source.
    * borrow_mode (BM_Imm, BM_Mut), range_kind (RK_Exclusive, RK_Inclusive), binop (Add, Sub, Mul,
      Div, Mod, Shl, Shr, BAnd, BOr, BXor, Eq, Ne, Lt, Le, Gt, Ge, And, Or), unaryop (U_Not,
      U_Borrow, U_Deref, U_Propagate), assign_binop (AssignSub, AssignMul, AssignMod, AssignBAnd,
      AssignBOr, AssignBXor, AssignShl, AssignShr), and assignop (Assign, AssignAdd, AssignBin).
      These tags describe surface operations only; their HOL constants and semantics belong to later
      modules.
    * ur_pat and P_Wild, P_Ident, P_Literal, P_Constr, P_Tuple, P_Group, P_Borrow, P_Alias, P_Range,
      P_Slice, P_Struct, P_Or, together with slice_item (SI_Pat, SI_Rest) and struct_field (SF_Field,
      SF_Shorthand, SF_Rest). Lists retain source order; grammar-produced tuple lists contain at least
      two elements and P_Or alternatives are flattened. P_Ident deliberately does not decide binder
      versus constructor.
    * match_flavour and MF_Switch, MF_Case, MF_Auto.  MF_Auto requests downstream classification; it
      is not a fourth lowering.
    * the mutually recursive expression interface ur_expr (UE_Unit, UE_Tuple, UE_Array, UE_Ident,
      UE_Literal, UE_ExprAntiq, UE_Let, UE_LetMut, UE_Const, UE_Seq, UE_Return, UE_Bin, UE_Unary,
      UE_Group, UE_Block, UE_If, UE_While, UE_Loop, UE_For, UE_WhileLet, UE_Call, UE_Field, UE_Index,
      UE_Range, UE_Assign, UE_Macro, UE_Match), macro_payload (MP_Arguments, MP_Matches), ur_place
      (UP_Ident, UP_Deref, UP_Field, UP_Index, UP_Antiq), and ur_arm (UR_Arm). Expression and pattern
      lists preserve source order. A generic macro payload retains every parsed argument without
      deciding which arguments a legacy macro lowers; MP_Matches retains its expression and pattern
      in separate grammar categories. A UR_Arm contains its
      pattern, an optional guard paired with the guard-keyword position, and its body.  A UE_Return
      never stores a semicolon; a method invocation is represented as UE_Call with the receiver
      prepended; ur_place contains only validated assignment-target shapes.

  Position.T fields identify the token or span documented at each constructor. Consumers may use them
  for markup and diagnostics, but must not infer semantic validity from their presence.
  literal_position returns the source position of every literal payload.

  The remaining public functions are grammar-facing construction contracts. mk_assign accepts
  identifiers, expression antiquotations, dereferences, fields and indices over recursively valid
  places, and transparent groups as assignment targets; every other expression raises the positioned
  "invalid assignment target" error. finish_statement leaves a terminal UE_Return unchanged and
  otherwise sequences the expression with UE_Unit at the semicolon. mk_bare_ident_pat normalises "_"
  to P_Wild; the other pattern smart constructors consume ordinary (name, position) pairs without a
  parser-only wrapper datatype. mk_call combines its supplied source endpoints into the call span,
  mk_method_call additionally prepends its receiver, and mk_or_pat preserves source order while
  flattening a right-recursive P_Or.

  Constructor-resolution policy, legal-pattern subsets at each use site, lowering choices, and the
  private expression-position/place conversion helpers remain implementation details. Directly
  constructing values outside the grammar does not imply that the corresponding source form is
  accepted or semantically valid.
*)
structure URust_AST :> URUST_AST =
struct
  datatype literal_payload =
      LP_Integer  of string * Position.T
    | LP_Bool     of bool * Position.T
    | LP_String   of string * Position.T
    | LP_ValAntiq of Input.source

  fun literal_position (LP_Integer (_, pos)) = pos
    | literal_position (LP_Bool (_, pos)) = pos
    | literal_position (LP_String (_, pos)) = pos
    | literal_position (LP_ValAntiq source) = Input.pos_of source

  (* THE pattern language: ONE datatype for EVERY binding site (let / const binder, match_switch key,
     match_case arm, and later closure params, `for` patterns, fn parameters) -- Rust has one pattern
     grammar, whose sites differ only in which patterns are LEGAL there, so each site's elaborator gates
     what it accepts with a positioned error instead of the grammar forking (D28). A bare id's ROLE
     (nullary ctor vs variable binder) needs `Code.is_constr`, invisible to the parser -- hence one
     `P_Ident`. Adding a pattern form = ONE constructor here + one clause per consuming site. *)
  datatype borrow_mode = BM_Imm | BM_Mut
  datatype range_kind = RK_Exclusive | RK_Inclusive

  datatype ur_pat =
      P_Wild   of Position.T                          (* _ *)
    | P_Ident  of string * Position.T                 (* bare id: nullary ctor OR variable binder *)
    | P_Literal of literal_payload                    (* numeral switch key or equality pattern *)
    | P_Constr of string * Position.T * ur_pat list   (* C(args): name, name-pos, args *)
    | P_Tuple  of ur_pat list * Position.T            (* (p0, p1, ..), at least two elements *)
    | P_Group  of ur_pat                              (* (p), transparent wrapper *)
    | P_Borrow of borrow_mode * ur_pat * Position.T   (* &p / & mut p; syntax-only today *)
    | P_Alias  of string * Position.T * ur_pat * Position.T
                                                       (* name @ p: name-pos, inner, @-pos *)
    | P_Range  of range_kind * ur_pat * ur_pat * Position.T
                                                       (* lo..hi / lo..=hi, at operator *)
    | P_Slice  of slice_item list * Position.T        (* [p, .., q], at full span *)
    | P_Struct of string * Position.T * struct_field list
                                                       (* Head { fields }, at head-pos *)
    | P_Or     of ur_pat list * Position.T            (* p | q | r  (flattened; source order) *)
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

  datatype ur_expr =
      UE_Unit      of Position.T                      (* () *)
    | UE_Tuple     of ur_expr list * Position.T       (* (e0, e1, ..), at least two elements *)
    | UE_Array     of ur_expr list * Position.T       (* [e0, e1, ..], including empty *)
    | UE_Ident     of string * Position.T             (* bare identifier at value position *)
    | UE_Literal   of literal_payload                 (* integer / bool / string / <<value>> *)
    | UE_ExprAntiq of Input.source                    (* eps<e> body as a POSITIONED source -> e *)
    | UE_Let       of ur_pat * ur_expr * ur_expr      (* let <pat> = rhs; body -> bind *)
    | UE_LetMut    of ur_pat * ur_expr * ur_expr * Position.T
                                                      (* let mut <pat> = rhs; body *)
    | UE_Const     of ur_pat * ur_expr * ur_expr      (* const: same desugaring as let today; distinct node
                                                         keeps the keyword for when it diverges (B7) *)
    | UE_Seq       of ur_expr * ur_expr               (* e1; e2 -> sequence (trailing `;`: e2 = unit) *)
    | UE_Return    of ur_expr option * Position.T     (* return [value]; semicolon is never stored *)
    | UE_Bin       of binop * ur_expr * ur_expr * Position.T   (* a <binop> b *)
    | UE_Unary     of unaryop * ur_expr * Position.T
                                                      (* !a / &a / & mut a / *a / a? *)
    | UE_Group     of ur_expr * Position.T                      (* (a), transparent during lowering *)
    | UE_Block     of ur_expr * Position.T            (* { stmts } -- ERASES to <stmts>, no `scoped`
                                                         wrapper: `_urust_scoping` is identity (D22) *)
    | UE_If        of ur_expr * ur_expr * ur_expr option * Position.T
                                                      (* NONE else-branch = one-armed -> skip (D22) *)
    | UE_While     of Input.source * ur_expr * ur_expr * Position.T
                                                      (* #[fuel(eps<n>)] while (condition) body *)
    | UE_Loop      of Input.source * ur_expr * Position.T
                                                      (* #[fuel(eps<n>)] loop body *)
    | UE_For       of ur_pat * ur_expr * ur_expr * Position.T
                                                      (* for pattern in iterable body *)
    | UE_WhileLet  of Input.source * ur_pat * ur_expr * ur_expr * Position.T
                                                      (* #[fuel(eps<n>)] while let pattern = value body *)
    | UE_Call      of string * Position.T * ur_expr list * Position.T
                                                      (* f(a0..aN) -> funcallN. Callee is an IDENTIFIER
                                                         (name, name-pos) resolved in NFunction context;
                                                         then args and the SPAN of the whole call, so an
                                                         arity error underlines the call, not just the name
                                                         (D23/D29). Non-identifier callees (antiquotation,
                                                         turbofish, path) are deferred -- D-5. *)
    | UE_Field     of ur_expr * string * Position.T   (* e.field -> NField lens focus *)
    | UE_Index     of ur_expr * ur_expr * Position.T  (* e[i] -> index_const, at full span *)
    | UE_Range     of range_kind * ur_expr * ur_expr * Position.T
                                                      (* lo..hi / lo..=hi, at operator *)
    | UE_Assign    of assignop * ur_place * ur_expr * Position.T
                                                      (* place assignment-op rhs, at the operator *)
    | UE_Macro     of
        string * Position.T * Position.T * macro_payload * Position.T
                                                      (* name, name-pos, !-pos, payload, full span *)
    | UE_Match     of match_flavour * ur_expr * ur_arm list * Position.T
                                                      (* match_<flavour> scrut { pat => body, .. }. ONE node
                                                         for both keywords; only the LOWERING differs --
                                                         MF_Switch -> ncase_selector (first-order, D26),
                                                         MF_Case -> the Ctr_Sugar case skeleton (D27). Each
                                                         flavour's elaborator gates the patterns it cannot
                                                         lower with a positioned error. *)
  and macro_payload =
      MP_Arguments of ur_expr list
    | MP_Matches of ur_expr * ur_pat
  and ur_place =
      UP_Ident of string * Position.T
    | UP_Deref of ur_expr * Position.T
    | UP_Field of ur_place * string * Position.T
    | UP_Index of ur_place * ur_expr * Position.T
    | UP_Antiq of Input.source
  and ur_arm =
      UR_Arm of ur_pat * (ur_expr * Position.T) option * ur_expr

  fun expression_position (UE_Unit pos) = pos
    | expression_position (UE_Tuple (_, pos)) = pos
    | expression_position (UE_Array (_, pos)) = pos
    | expression_position (UE_Ident (_, pos)) = pos
    | expression_position (UE_Literal payload) = literal_position payload
    | expression_position (UE_ExprAntiq src) = Input.pos_of src
    | expression_position (UE_Let _) = Position.none
    | expression_position (UE_LetMut (_, _, _, pos)) = pos
    | expression_position (UE_Const _) = Position.none
    | expression_position (UE_Seq _) = Position.none
    | expression_position (UE_Return (_, pos)) = pos
    | expression_position (UE_Bin (_, _, _, pos)) = pos
    | expression_position (UE_Unary (_, _, pos)) = pos
    | expression_position (UE_Group (_, pos)) = pos
    | expression_position (UE_Block (_, pos)) = pos
    | expression_position (UE_If (_, _, _, pos)) = pos
    | expression_position (UE_While (_, _, _, pos)) = pos
    | expression_position (UE_Loop (_, _, pos)) = pos
    | expression_position (UE_For (_, _, _, pos)) = pos
    | expression_position (UE_WhileLet (_, _, _, _, pos)) = pos
    | expression_position (UE_Call (_, _, _, pos)) = pos
    | expression_position (UE_Field (_, _, pos)) = pos
    | expression_position (UE_Index (_, _, pos)) = pos
    | expression_position (UE_Range (_, _, _, pos)) = pos
    | expression_position (UE_Assign (_, _, _, pos)) = pos
    | expression_position (UE_Macro (_, _, _, _, pos)) = pos
    | expression_position (UE_Match (_, _, _, pos)) = pos

  (* Assignment parses an ordinary expression on the left, then crosses this one validation boundary.
     Keeping target recognition out of the grammar gives every invalid expression a stable positioned
     diagnostic and lets grouped/dereferenced field chains compose without parallel productions. *)
  fun expr_to_place (UE_Ident id) = UP_Ident id
    | expr_to_place (UE_ExprAntiq src) = UP_Antiq src
    | expr_to_place (UE_Group (expr, _)) = expr_to_place expr
    | expr_to_place (UE_Unary (U_Deref, expr, pos)) = UP_Deref (expr, pos)
    | expr_to_place (UE_Field (base, name, pos)) =
        UP_Field (expr_to_place base, name, pos)
    | expr_to_place (UE_Index (base, index, pos)) =
        UP_Index (expr_to_place base, index, pos)
    | expr_to_place expr =
        error ("urust_expr: invalid assignment target" ^
          Position.here (expression_position expr))

  fun mk_assign (aop, pos) lhs rhs =
    UE_Assign (aop, expr_to_place lhs, rhs, pos)

  (* A return's legacy semicolon belongs to its surface production, not to sequencing. *)
  fun finish_statement (return as UE_Return _, _) = return
    | finish_statement (expression, semi_pos) =
        UE_Seq (expression, UE_Unit semi_pos)

  (* `_` lexes as an ordinary IDENT: normalise to P_Wild in ONE place, not an `= "_"` test at every site. *)
  fun mk_ident_pat (s, pos) = if s = "_" then P_Wild pos else P_Ident (s, pos)

  fun mk_bare_ident_pat pair = mk_ident_pat pair
  fun mk_ctor_pat ((name, pos), args) = P_Constr (name, pos, args)
  fun mk_alias_pat ((name, pos), inner, at_pos) =
    P_Alias (name, pos, inner, at_pos)
  fun mk_struct_pat ((name, pos), fields) =
    P_Struct (name, pos, fields)
  fun mk_call (name, name_pos, args, left, right) =
    UE_Call (name, name_pos, args, Position.range_position (left, right))
  fun mk_method_call (receiver, name, name_pos, args, left, right) =
    mk_call (name, name_pos, receiver :: args, left, right)

  (* The grammar is right-recursive, so prepend the left alternative in O(1) while retaining source order. *)
  fun mk_or_pat (p, P_Or (alternatives, _), pos) =
        P_Or (p :: alternatives, pos)
    | mk_or_pat (p, q, pos) =
        P_Or ([p, q], pos)
end
\<close>

end
