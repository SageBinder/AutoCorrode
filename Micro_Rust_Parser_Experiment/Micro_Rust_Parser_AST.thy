theory Micro_Rust_Parser_AST
  imports Main
begin

section\<open> Reified AST \<close>

text\<open> One constructor per uRust surface form. Positions are carried for markup/diagnostics. \<close>
ML\<open>
structure URust_AST =
struct
  datatype literal_payload =
      LP_Bool     of bool * Position.T
    | LP_String   of string * Position.T
    | LP_ValAntiq of Input.source

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
    | P_Lit    of string * Position.T                 (* numeral pattern (a match_switch key) *)
    | P_Value  of literal_payload                     (* bool / string / <<value>> equality pattern *)
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

  datatype pat_ident = PI of string * Position.T

  (* Which `match` surface keyword an arm set came from; the two lower DIFFERENTLY (see UE_Match), so the
     flavour is a tag rather than separate AST nodes -- the bare `match` keyword then becomes a third
     flavour that CLASSIFIES its arms into one of these two lowerings (D28/D32). *)
  datatype match_flavour = MF_Switch | MF_Case | MF_Auto

  (* Pure-value operators. Data-driven: each maps to one HOL const via URust_Translate.binop_const /
     unop_const, so adding an operator is one datatype line + one table row (D20). *)
  datatype binop =
      Add | Sub | Mul | Div | Mod              (* + - * / %       *)
    | Shl | Shr                                (* << >>           *)
    | BAnd | BOr | BXor                        (* & | ^  (infix)  *)
    | Eq | Ne | Lt | Le | Gt | Ge              (* == != < <= > >= *)
    | And | Or                                 (* && ||           *)
  datatype unop = Not                          (* !  (and !! = !(!_)) *)
  datatype assign_binop =
      AssignSub | AssignMul | AssignMod
    | AssignBAnd | AssignBOr | AssignBXor
    | AssignShl | AssignShr
  datatype assignop =
      Assign
    | AssignAdd
    | AssignBin of assign_binop

  datatype ur_expr =
      UE_Num       of string * Position.T             (* raw decimal or hexadecimal numeral *)
    | UE_NumSfx    of string * Position.T             (* RAW lexeme of a suffixed int (1_u32 / 0x4_u8);
                                                         split + typed by parse_int_lit -- ALL suffix
                                                         knowledge sits in that one table (D29) *)
    | UE_Unit      of Position.T                      (* () *)
    | UE_Tuple     of ur_expr list * Position.T       (* (e0, e1, ..), at least two elements *)
    | UE_Ident     of string * Position.T             (* bare identifier at value position *)
    | UE_Literal   of literal_payload                 (* true / false / string / <<value>> *)
    | UE_ExprAntiq of Input.source                    (* eps<e> body as a POSITIONED source -> e *)
    | UE_Let       of ur_pat * ur_expr * ur_expr      (* let <pat> = rhs; body -> bind *)
    | UE_LetMut    of ur_pat * ur_expr * ur_expr * Position.T
                                                      (* let mut <pat> = rhs; body *)
    | UE_Const     of ur_pat * ur_expr * ur_expr      (* const: same desugaring as let today; distinct node
                                                         keeps the keyword for when it diverges (B7) *)
    | UE_Seq       of ur_expr * ur_expr               (* e1; e2 -> sequence (trailing `;`: e2 = unit) *)
    | UE_Bin       of binop * ur_expr * ur_expr * Position.T   (* a <binop> b *)
    | UE_Un        of unop * ur_expr * Position.T              (* !a  (and !!a = !(!a)) *)
    | UE_Borrow    of borrow_mode * ur_expr * Position.T       (* &a / & mut a *)
    | UE_Deref     of ur_expr * Position.T                      (* *a *)
    | UE_Group     of ur_expr * Position.T                      (* (a), transparent during lowering *)
    | UE_Block     of ur_expr * Position.T            (* { stmts } -- ERASES to <stmts>, no `scoped`
                                                         wrapper: `_urust_scoping` is identity (D22) *)
    | UE_If        of ur_expr * ur_expr * ur_expr option * Position.T
                                                      (* NONE else-branch = one-armed -> skip (D22) *)
    | UE_Call      of string * Position.T * ur_expr list * Position.T
                                                      (* f(a0..aN) -> funcallN. Callee is an IDENTIFIER
                                                         (name, name-pos) resolved in NFunction context;
                                                         then args and the SPAN of the whole call, so an
                                                         arity error underlines the call, not just the name
                                                         (D23/D29). Non-identifier callees (antiquotation,
                                                         turbofish, path) are deferred -- D-5. *)
    | UE_Field     of ur_expr * string * Position.T   (* e.field -> NField lens focus *)
    | UE_Propagate of ur_expr * Position.T            (* e? -> overloaded propagate_const *)
    | UE_Assign    of assignop * ur_place * ur_expr * Position.T
                                                      (* place assignment-op rhs, at the operator *)
    | UE_Match     of match_flavour * ur_expr * ur_arm list * Position.T
                                                      (* match_<flavour> scrut { pat => body, .. }. ONE node
                                                         for both keywords; only the LOWERING differs --
                                                         MF_Switch -> ncase_selector (first-order, D26),
                                                         MF_Case -> the Ctr_Sugar case skeleton (D27). Each
                                                         flavour's elaborator gates the patterns it cannot
                                                         lower with a positioned error. *)
  and ur_place =
      UP_Ident of string * Position.T
    | UP_Deref of ur_expr * Position.T
    | UP_Field of ur_place * string * Position.T
    | UP_Antiq of Input.source
  and ur_arm =
      UR_Arm of ur_pat * (ur_expr * Position.T) option * ur_expr

  fun expr_pos (UE_Num (_, pos)) = pos
    | expr_pos (UE_NumSfx (_, pos)) = pos
    | expr_pos (UE_Unit pos) = pos
    | expr_pos (UE_Tuple (_, pos)) = pos
    | expr_pos (UE_Ident (_, pos)) = pos
    | expr_pos (UE_Literal (LP_Bool (_, pos))) = pos
    | expr_pos (UE_Literal (LP_String (_, pos))) = pos
    | expr_pos (UE_Literal (LP_ValAntiq src)) = Input.pos_of src
    | expr_pos (UE_ExprAntiq src) = Input.pos_of src
    | expr_pos (UE_Let _) = Position.none
    | expr_pos (UE_LetMut (_, _, _, pos)) = pos
    | expr_pos (UE_Const _) = Position.none
    | expr_pos (UE_Seq _) = Position.none
    | expr_pos (UE_Bin (_, _, _, pos)) = pos
    | expr_pos (UE_Un (_, _, pos)) = pos
    | expr_pos (UE_Borrow (_, _, pos)) = pos
    | expr_pos (UE_Deref (_, pos)) = pos
    | expr_pos (UE_Group (_, pos)) = pos
    | expr_pos (UE_Block (_, pos)) = pos
    | expr_pos (UE_If (_, _, _, pos)) = pos
    | expr_pos (UE_Call (_, _, _, pos)) = pos
    | expr_pos (UE_Field (_, _, pos)) = pos
    | expr_pos (UE_Propagate (_, pos)) = pos
    | expr_pos (UE_Assign (_, _, _, pos)) = pos
    | expr_pos (UE_Match (_, _, _, pos)) = pos

  (* Assignment parses an ordinary expression on the left, then crosses this one validation boundary.
     Keeping target recognition out of the grammar gives every invalid expression a stable positioned
     diagnostic and lets grouped/dereferenced field chains compose without parallel productions. *)
  fun expr_to_place (UE_Ident id) = UP_Ident id
    | expr_to_place (UE_ExprAntiq src) = UP_Antiq src
    | expr_to_place (UE_Group (expr, _)) = expr_to_place expr
    | expr_to_place (UE_Deref (expr, pos)) = UP_Deref (expr, pos)
    | expr_to_place (UE_Field (base, name, pos)) =
        UP_Field (expr_to_place base, name, pos)
    | expr_to_place expr =
        error ("urust_expr: invalid assignment target" ^ Position.here (expr_pos expr))

  fun mk_assign (aop, pos) lhs rhs =
    UE_Assign (aop, expr_to_place lhs, rhs, pos)

  (* `_` lexes as an ordinary IDENT: normalise to P_Wild in ONE place, not an `= "_"` test at every site. *)
  fun mk_ident_pat (s, pos) = if s = "_" then P_Wild pos else P_Ident (s, pos)

  fun mk_bare_ident_pat (PI pair) = mk_ident_pat pair
  fun mk_ctor_pat (PI (name, pos), args) = P_Constr (name, pos, args)
  fun mk_alias_pat (PI (name, pos), inner, at_pos) =
    P_Alias (name, pos, inner, at_pos)
  fun mk_struct_pat (PI (name, pos), fields) =
    P_Struct (name, pos, fields)
  fun mk_call (name, name_pos, args, left, right) =
    UE_Call (name, name_pos, args, Position.range_position (left, right))
  fun mk_method_call (receiver, name, name_pos, args, left, right) =
    mk_call (name, name_pos, receiver :: args, left, right)

  (* Flatten nested or-patterns so `a | b | c` is one P_Or in source order, whatever %left TBAR bracketed. *)
  fun mk_or_pat (p, q, pos) =
    let fun alts (P_Or (ps, _)) = ps | alts p = [p]
    in P_Or (alts p @ alts q, pos) end
end
\<close>

end
