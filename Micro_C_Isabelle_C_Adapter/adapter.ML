(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature MICRO_C_ISABELLE_C_ADAPTER =
sig
  datatype type_spec =
      PlainInt
    | Void
    | UnsupportedType of string

  type positioned_type =
    {kind: type_spec,
     position: Position.T}

  datatype integer_representation =
      Decimal
    | Hexadecimal
    | Octal

  datatype expr =
      IntLiteral of
        {value: IntInf.int,
         spelling: string,
         representation: integer_representation,
         has_suffix: bool,
         position: Position.T}
    | Identifier of
        {name: string,
         position: Position.T}
    | Add of
        {left: expr,
         right: expr,
         position: Position.T,
         operator_position: Position.T}

  type parameter =
    {type_spec: positioned_type,
     name: (string * Position.T) option,
     position: Position.T,
     plain_declarator: bool}

  datatype parameter_clause =
      VoidParameters of Position.T
    | NamedParameters of
        {parameters: parameter list,
         variadic: bool,
         position: Position.T}
    | UnspecifiedParameters of Position.T
    | IdentifierParameters of Position.T

  type function_def =
    {return_type: positioned_type,
     name: (string * Position.T) option,
     parameters: parameter_clause,
     body: expr,
     return_position: Position.T,
     position: Position.T,
     plain_declarator: bool,
     old_style_declaration_positions: Position.T list}

  val expr_position: expr -> Position.T
  val parse_function: Input.source -> theory -> function_def
end

structure Micro_C_Isabelle_C_Adapter : MICRO_C_ISABELLE_C_ADAPTER =
struct

datatype type_spec =
    PlainInt
  | Void
  | UnsupportedType of string

type positioned_type =
  {kind: type_spec,
   position: Position.T}

datatype integer_representation =
    Decimal
  | Hexadecimal
  | Octal

datatype expr =
    IntLiteral of
      {value: IntInf.int,
       spelling: string,
       representation: integer_representation,
       has_suffix: bool,
       position: Position.T}
  | Identifier of
      {name: string,
       position: Position.T}
  | Add of
      {left: expr,
       right: expr,
       position: Position.T,
       operator_position: Position.T}

type parameter =
  {type_spec: positioned_type,
   name: (string * Position.T) option,
   position: Position.T,
   plain_declarator: bool}

datatype parameter_clause =
    VoidParameters of Position.T
  | NamedParameters of
      {parameters: parameter list,
       variadic: bool,
       position: Position.T}
  | UnspecifiedParameters of Position.T
  | IdentifierParameters of Position.T

type function_def =
  {return_type: positioned_type,
   name: (string * Position.T) option,
   parameters: parameter_clause,
   body: expr,
   return_position: Position.T,
   position: Position.T,
   plain_declarator: bool,
   old_style_declaration_positions: Position.T list}

fun expr_position (IntLiteral {position, ...}) = position
  | expr_position (Identifier {position, ...}) = position
  | expr_position (Add {position, ...}) = position

fun decoded_position position =
  (case C11_Ast_Lib.toPos_positiona position of
     pos :: _ => pos
   | [] => Position.none)

fun advance_position count pos =
  Position.symbol_explode
    (String.implode (replicate count #"x")) pos

fun node_position node =
  let
    val (first, _) = C_Ast.p_first_of_NodeInfo node
    val (last, raw_length) = C_Ast.p_last_of_NodeInfo node
    val start = decoded_position first
    val last_start = decoded_position last
    val length =
      Int.max (0, IntInf.toInt raw_length)
      handle Overflow => 0
    val stop = advance_position length last_start
  in
    if start = Position.none orelse stop = Position.none
    then start
    else Position.range_position (start, stop)
  end

fun end_position pos =
  (case (Position.offset_of pos, Position.end_offset_of pos) of
     (SOME start, SOME stop) =>
       advance_position (stop - start) pos
   | _ => pos)

fun span_position left right =
  if left = Position.none then right
  else if right = Position.none then left
  else Position.range_position (left, end_position right)

fun source_text source pos fallback =
  let
    val (content, content_position) = Input.source_content source
  in
    (case
      (Position.offset_of content_position,
       Position.offset_of pos,
       Position.end_offset_of pos) of
     (SOME source_start, SOME range_start, SOME range_stop) =>
       let
         val symbols = Symbol.explode content
         val left = range_start - source_start
         val count = range_stop - range_start
       in
         if 0 <= left andalso 0 <= count andalso left + count <= length symbols
         then symbols |> drop left |> take count |> String.concat
         else fallback
       end
   | _ => fallback)
  end

fun ident_name (C_Ast.Ident0 (name, _, _)) =
  C11_Ast_Lib.toString_abr_string name

fun ident_position (C_Ast.Ident0 (_, _, node)) =
  node_position node

fun constant_node (C_Ast.CIntConst0 (_, node)) = node
  | constant_node (C_Ast.CCharConst0 (_, node)) = node
  | constant_node (C_Ast.CFloatConst0 (_, node)) = node
  | constant_node (C_Ast.CStrConst0 (_, node)) = node

fun builtin_node (C_Ast.CBuiltinVaArg0 (_, _, node)) = node
  | builtin_node (C_Ast.CBuiltinOffsetOf0 (_, _, node)) = node
  | builtin_node (C_Ast.CBuiltinTypesCompatible0 (_, _, node)) = node

fun expression_node expression =
  (case expression of
     C_Ast.CComma0 (_, node) => node
   | C_Ast.CAssign0 (_, _, _, node) => node
   | C_Ast.CCond0 (_, _, _, node) => node
   | C_Ast.CBinary0 (_, _, _, node) => node
   | C_Ast.CCast0 (_, _, node) => node
   | C_Ast.CUnary0 (_, _, node) => node
   | C_Ast.CSizeofExpr0 (_, node) => node
   | C_Ast.CSizeofType0 (_, node) => node
   | C_Ast.CAlignofExpr0 (_, node) => node
   | C_Ast.CAlignofType0 (_, node) => node
   | C_Ast.CComplexReal0 (_, node) => node
   | C_Ast.CComplexImag0 (_, node) => node
   | C_Ast.CIndex0 (_, _, node) => node
   | C_Ast.CCall0 (_, _, node) => node
   | C_Ast.CMember0 (_, _, _, node) => node
   | C_Ast.CVar0 (_, node) => node
   | C_Ast.CConst0 constant => constant_node constant
   | C_Ast.CCompoundLit0 (_, _, node) => node
   | C_Ast.CGenericSelection0 (_, _, node) => node
   | C_Ast.CStatExpr0 (_, node) => node
   | C_Ast.CLabAddrExpr0 (_, node) => node
   | C_Ast.CBuiltinExpr0 builtin => builtin_node builtin)

fun statement_node statement =
  (case statement of
     C_Ast.CLabel0 (_, _, _, node) => node
   | C_Ast.CCase0 (_, _, node) => node
   | C_Ast.CCases0 (_, _, _, node) => node
   | C_Ast.CDefault0 (_, node) => node
   | C_Ast.CExpr0 (_, node) => node
   | C_Ast.CCompound0 (_, _, node) => node
   | C_Ast.CIf0 (_, _, _, node) => node
   | C_Ast.CSwitch0 (_, _, node) => node
   | C_Ast.CWhile0 (_, _, _, node) => node
   | C_Ast.CFor0 (_, _, _, _, node) => node
   | C_Ast.CGoto0 (_, node) => node
   | C_Ast.CGotoPtr0 (_, node) => node
   | C_Ast.CCont0 node => node
   | C_Ast.CBreak0 node => node
   | C_Ast.CReturn0 (_, node) => node
   | C_Ast.CAsm0 (_, node) => node)

fun declaration_node (C_Ast.CDecl0 (_, _, node)) = node
  | declaration_node (C_Ast.CStaticAssert0 (_, _, node)) = node

fun function_node (C_Ast.CFunDef0 (_, _, _, _, node)) = node

fun external_position external =
  node_position
    (case external of
       C_Ast.CDeclExt0 declaration => declaration_node declaration
     | C_Ast.CFDefExt0 function => function_node function
     | C_Ast.CAsmExt0 (_, node) => node)

fun attribute_node (C_Ast.CAttr0 (_, _, node)) = node

fun qualifier_node qualifier =
  (case qualifier of
     C_Ast.CConstQual0 node => node
   | C_Ast.CVolatQual0 node => node
   | C_Ast.CRestrQual0 node => node
   | C_Ast.CAtomicQual0 node => node
   | C_Ast.CAttrQual0 attribute => attribute_node attribute
   | C_Ast.CNullableQual0 node => node
   | C_Ast.CNonnullQual0 node => node)

fun type_specifier_node type_specifier =
  (case type_specifier of
     C_Ast.CVoidType0 node => node
   | C_Ast.CCharType0 node => node
   | C_Ast.CShortType0 node => node
   | C_Ast.CIntType0 node => node
   | C_Ast.CLongType0 node => node
   | C_Ast.CFloatType0 node => node
   | C_Ast.CDoubleType0 node => node
   | C_Ast.CSignedType0 node => node
   | C_Ast.CUnsigType0 node => node
   | C_Ast.CBoolType0 node => node
   | C_Ast.CComplexType0 node => node
   | C_Ast.CInt128Type0 node => node
   | C_Ast.CSUType0 (_, node) => node
   | C_Ast.CEnumType0 (_, node) => node
   | C_Ast.CTypeDef0 (_, node) => node
   | C_Ast.CTypeOfExpr0 (_, node) => node
   | C_Ast.CTypeOfType0 (_, node) => node
   | C_Ast.CAtomicType0 (_, node) => node)

fun storage_specifier_node storage_specifier =
  (case storage_specifier of
     C_Ast.CAuto0 node => node
   | C_Ast.CRegister0 node => node
   | C_Ast.CStatic0 node => node
   | C_Ast.CExtern0 node => node
   | C_Ast.CTypedef0 node => node
   | C_Ast.CThread0 node => node)

fun function_specifier_node function_specifier =
  (case function_specifier of
     C_Ast.CInlineQual0 node => node
   | C_Ast.CNoreturnQual0 node => node)

fun alignment_specifier_node alignment_specifier =
  (case alignment_specifier of
     C_Ast.CAlignAsType0 (_, node) => node
   | C_Ast.CAlignAsExpr0 (_, node) => node)

fun declaration_specifier_node declaration_specifier =
  (case declaration_specifier of
     C_Ast.CStorageSpec0 specifier => storage_specifier_node specifier
   | C_Ast.CTypeSpec0 specifier => type_specifier_node specifier
   | C_Ast.CTypeQual0 qualifier => qualifier_node qualifier
   | C_Ast.CFunSpec0 specifier => function_specifier_node specifier
   | C_Ast.CAlignSpec0 specifier => alignment_specifier_node specifier)

fun describe_type_specifier type_specifier =
  (case type_specifier of
     C_Ast.CVoidType0 _ => "void"
   | C_Ast.CCharType0 _ => "char"
   | C_Ast.CShortType0 _ => "short"
   | C_Ast.CIntType0 _ => "int"
   | C_Ast.CLongType0 _ => "long"
   | C_Ast.CFloatType0 _ => "float"
   | C_Ast.CDoubleType0 _ => "double"
   | C_Ast.CSignedType0 _ => "signed"
   | C_Ast.CUnsigType0 _ => "unsigned"
   | C_Ast.CBoolType0 _ => "_Bool"
   | C_Ast.CComplexType0 _ => "_Complex"
   | C_Ast.CInt128Type0 _ => "__int128"
   | C_Ast.CSUType0 _ => "struct or union"
   | C_Ast.CEnumType0 _ => "enum"
   | C_Ast.CTypeDef0 _ => "typedef name"
   | C_Ast.CTypeOfExpr0 _ => "typeof expression"
   | C_Ast.CTypeOfType0 _ => "typeof type"
   | C_Ast.CAtomicType0 _ => "_Atomic")

fun describe_declaration_specifier declaration_specifier =
  (case declaration_specifier of
     C_Ast.CTypeSpec0 specifier => describe_type_specifier specifier
   | C_Ast.CStorageSpec0 _ => "storage-class specifier"
   | C_Ast.CTypeQual0 _ => "type qualifier"
   | C_Ast.CFunSpec0 _ => "function specifier"
   | C_Ast.CAlignSpec0 _ => "alignment specifier")

fun normalize_type fallback specs : positioned_type =
  (case specs of
     [C_Ast.CTypeSpec0 (C_Ast.CIntType0 node)] =>
       {kind = PlainInt, position = node_position node}
   | [C_Ast.CTypeSpec0 (C_Ast.CVoidType0 node)] =>
       {kind = Void, position = node_position node}
   | specifier :: _ =>
       {kind = UnsupportedType (describe_declaration_specifier specifier),
        position = node_position (declaration_specifier_node specifier)}
   | [] =>
       {kind = UnsupportedType "missing type specifier",
        position = fallback})

fun normalize_parameter declaration : parameter =
  (case declaration of
     C_Ast.CDecl0 (specifiers, declarators, declaration_info) =>
       let
         val position = node_position declaration_info
         val type_spec = normalize_type position specifiers
       in
         (case declarators of
            [] =>
              {type_spec = type_spec,
               name = NONE,
               position = position,
               plain_declarator = true}
          | [((C_Ast.Some
                (C_Ast.CDeclr0
                  (name, derived, assembly_name, attributes, _)),
               C_Ast.None),
              C_Ast.None)] =>
              {type_spec = type_spec,
               name =
                 (case name of
                    C_Ast.None => NONE
                  | C_Ast.Some identifier =>
                      SOME (ident_name identifier, ident_position identifier)),
               position = position,
               plain_declarator =
                 null derived andalso
                 (case assembly_name of C_Ast.None => true | _ => false) andalso
                 null attributes}
          | _ =>
              error
                ("c_translate: unsupported parameter declaration" ^
                 Position.here position))
       end
   | C_Ast.CStaticAssert0 (_, _, node) =>
       error
         ("c_translate: static assertions are not supported in parameter lists" ^
          Position.here (node_position node)))

fun normalize_parameter_clause function_declarator =
  (case function_declarator of
     C_Ast.CFunDeclr0
       (C_Ast.Left _, _, node) =>
       IdentifierParameters (node_position node)
   | C_Ast.CFunDeclr0
       (C_Ast.Right (declarations, variadic), _, node) =>
       let
         val position = node_position node
         val parameters = map normalize_parameter declarations
       in
         (case (parameters, variadic) of
            ([{type_spec = {kind = Void, ...},
               name = NONE,
               plain_declarator = true,
               position = void_position}], false) =>
              VoidParameters void_position
          | ([], false) => UnspecifiedParameters position
          | _ =>
              NamedParameters
                {parameters = parameters,
                 variadic = variadic,
                 position = position})
       end)

fun integer_representation representation =
  (case representation of
     C_Ast.DecRepr0 => Decimal
   | C_Ast.HexRepr0 => Hexadecimal
   | C_Ast.OctalRepr0 => Octal)

fun normalize_expression source expression =
  (case expression of
     C_Ast.CConst0
       (C_Ast.CIntConst0
         (C_Ast.CInteger0 (value, representation, C_Ast.Flags0 flags), node)) =>
       let
         val position = node_position node
       in
         IntLiteral
           {value = value,
            spelling = source_text source position (IntInf.toString value),
            representation = integer_representation representation,
            has_suffix = flags <> 0,
            position = position}
       end
   | C_Ast.CVar0 (identifier, node) =>
       Identifier
         {name = ident_name identifier,
          position = node_position node}
   | C_Ast.CBinary0 (C_Ast.CAddOp0, left, right, operator_node) =>
       let
         val left' = normalize_expression source left
         val right' = normalize_expression source right
       in
         Add
           {left = left',
            right = right',
            position = span_position (expr_position left') (expr_position right'),
            operator_position = node_position operator_node}
       end
   | C_Ast.CBinary0 (_, _, _, node) =>
       error
         ("c_translate: only the + operator is supported" ^
          Position.here (node_position node))
   | C_Ast.CCall0 (_, _, node) =>
       error
         ("c_translate: function calls are not supported" ^
          Position.here (node_position node))
   | C_Ast.CUnary0 (_, _, node) =>
       error
         ("c_translate: unary operators are not supported" ^
          Position.here (node_position node))
   | unsupported =>
       error
         ("c_translate: unsupported expression" ^
          Position.here (node_position (expression_node unsupported))))

fun block_item_position block_item =
  node_position
    (case block_item of
       C_Ast.CBlockStmt0 statement => statement_node statement
     | C_Ast.CBlockDecl0 declaration => declaration_node declaration
     | C_Ast.CNestedFunDef0 function => function_node function)

fun normalize_body source statement =
  (case statement of
     C_Ast.CCompound0
       ([], [C_Ast.CBlockStmt0
         (C_Ast.CReturn0 (C_Ast.Some expression, return_node))], _) =>
       (normalize_expression source expression, node_position return_node)
   | C_Ast.CCompound0
       ([], [C_Ast.CBlockStmt0
         (C_Ast.CReturn0 (C_Ast.None, return_node))], _) =>
       error
         ("c_translate: return without a value is not supported" ^
          Position.here (node_position return_node))
   | C_Ast.CCompound0 (_, [], node) =>
       error
         ("c_translate: the function body must contain one return statement" ^
          Position.here (node_position node))
   | C_Ast.CCompound0 (_, first :: _, _) =>
       error
         ("c_translate: locals and additional statements are not supported" ^
          Position.here (block_item_position first))
   | C_Ast.CReturn0 (C_Ast.None, node) =>
       error
         ("c_translate: return without a value is not supported" ^
          Position.here (node_position node))
   | unsupported =>
       error
         ("c_translate: the function body must be a compound return statement" ^
          Position.here (node_position (statement_node unsupported))))

fun normalize_function source
    (C_Ast.CFunDef0
      (return_specifiers,
       C_Ast.CDeclr0
         (name, derived, assembly_name, attributes, declarator_node),
       old_style_declarations,
       body,
       node)) : function_def =
  let
    val position = node_position node
    val return_type = normalize_type position return_specifiers
    val function_declarators =
      map_filter
        (fn derived_declarator =>
          case derived_declarator of
            C_Ast.CFunDeclr0 _ => SOME derived_declarator
          | _ => NONE)
        derived
    val function_declarator =
      (case function_declarators of
         [declarator] => declarator
       | _ =>
           error
             ("c_translate: malformed function declarator" ^
              Position.here (node_position declarator_node)))
    val parameters = normalize_parameter_clause function_declarator
    val (body', return_position) = normalize_body source body
  in
    {return_type = return_type,
     name =
       (case name of
          C_Ast.None => NONE
        | C_Ast.Some identifier =>
            SOME (ident_name identifier, ident_position identifier)),
     parameters = parameters,
     body = body',
     return_position = return_position,
     position = position,
     plain_declarator =
       (case derived of [C_Ast.CFunDeclr0 _] => true | _ => false) andalso
       (case assembly_name of C_Ast.None => true | _ => false) andalso
       null attributes,
     old_style_declaration_positions =
       map (node_position o declaration_node) old_style_declarations}
  end

fun normalize_translation_unit source
    (C_Ast.CTranslUnit0 (external_declarations, unit_node)) =
  (case external_declarations of
     [C_Ast.CFDefExt0 function] => normalize_function source function
   | [] =>
       error
         ("c_translate: expected exactly one function definition" ^
          Position.here (node_position unit_node))
   | [external] =>
       error
         ("c_translate: expected one function definition" ^
          Position.here (external_position external))
   | _ :: second :: _ =>
       error
         ("c_translate: multiple external declarations are not supported" ^
          Position.here (external_position second)))

fun parse_function source thy =
  let
    val parsed_context =
      C_Module.exec_eval source (Context.Theory thy)
    val parsed_theory = Context.theory_of parsed_context
    val translation_unit = get_CTranslUnit parsed_theory
  in
    normalize_translation_unit source translation_unit
  end

end
