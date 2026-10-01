(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Elaboration
  imports
    Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

section\<open>Scalar C elaboration\<close>

ML\<open>
signature C_ELABORATION =
sig
  type parameter =
    {name: string,
     position: Position.T,
     index: int}

  datatype expr =
      IntLiteral of
        {value: IntInf.int,
         position: Position.T}
    | Parameter of parameter
    | Add of
        {left: expr,
         right: expr,
         position: Position.T,
         operator_position: Position.T}

  type function_def =
    {name: string,
     name_position: Position.T,
     parameters: parameter list,
     body: expr,
     return_position: Position.T,
     position: Position.T}

  val elaborate_expression:
    parameter list -> Micro_C_Isabelle_C_Adapter.expr -> expr
  val elaborate_function:
    Micro_C_Isabelle_C_Adapter.function_def -> function_def
end

structure C_Elaboration : C_ELABORATION =
struct

type parameter =
  {name: string,
   position: Position.T,
   index: int}

datatype expr =
    IntLiteral of
      {value: IntInf.int,
       position: Position.T}
  | Parameter of parameter
  | Add of
      {left: expr,
       right: expr,
       position: Position.T,
       operator_position: Position.T}

type function_def =
  {name: string,
   name_position: Position.T,
   parameters: parameter list,
   body: expr,
   return_position: Position.T,
   position: Position.T}

fun unsupported message pos =
  error ("c_translate: " ^ message ^ Position.here pos)

fun check_plain_int what
    ({kind, position}: Micro_C_Isabelle_C_Adapter.positioned_type) =
  (case kind of
     Micro_C_Isabelle_C_Adapter.PlainInt => ()
   | Micro_C_Isabelle_C_Adapter.Void =>
       unsupported (what ^ " must have plain int type") position
   | Micro_C_Isabelle_C_Adapter.UnsupportedType description =>
       unsupported
         (what ^ " has unsupported type " ^ quote description) position)

fun decimal_spelling spelling =
  spelling <> "" andalso
  List.all Char.isDigit (String.explode spelling)

fun elaborate_expression parameters expression =
  let
    val environment =
      Symtab.make (map (fn parameter => (#name parameter, parameter)) parameters)

    fun elaborate source_expression =
      (case source_expression of
         Micro_C_Isabelle_C_Adapter.IntLiteral
           {value, spelling, representation, has_suffix, position} =>
           let
             val _ =
               (case representation of
                  Micro_C_Isabelle_C_Adapter.Decimal => ()
                | Micro_C_Isabelle_C_Adapter.Hexadecimal =>
                    unsupported
                      "hexadecimal integer literals are not supported" position
                | Micro_C_Isabelle_C_Adapter.Octal =>
                    unsupported
                      "octal integer literals are not supported" position)
             val _ =
               if has_suffix
               then unsupported "suffixed integer literals are not supported" position
               else ()
             val _ =
               if decimal_spelling spelling
               then ()
               else unsupported "expected an unsuffixed decimal integer literal" position
             val _ =
               if 0 <= value andalso value <= 2147483647
               then ()
               else unsupported
                 "integer literal is outside the prototype plain-int range" position
           in
             IntLiteral {value = value, position = position}
           end
       | Micro_C_Isabelle_C_Adapter.Identifier {name, position} =>
           (case Symtab.lookup environment name of
              SOME parameter => Parameter parameter
            | NONE =>
                unsupported ("unknown identifier " ^ quote name) position)
       | Micro_C_Isabelle_C_Adapter.Add
           {left, right, position, operator_position} =>
           Add
             {left = elaborate left,
              right = elaborate right,
              position = position,
              operator_position = operator_position})
  in
    elaborate expression
  end

fun elaborate_parameters source_parameters =
  let
    fun add_parameter
        ({type_spec, name, position, plain_declarator}:
          Micro_C_Isabelle_C_Adapter.parameter)
        (parameters, names) =
      let
        val _ = check_plain_int "parameter" type_spec
        val _ =
          if plain_declarator then ()
          else unsupported "parameter declarators must be plain identifiers" position
        val (name, name_position) =
          (case name of
             SOME named => named
           | NONE => unsupported "parameters must be named" position)
        val _ =
          if Symtab.defined names name
          then unsupported ("duplicate parameter " ^ quote name) name_position
          else ()
        val parameter =
          {name = name,
           position = name_position,
           index = length parameters}
      in
        (parameters @ [parameter], Symtab.update (name, ()) names)
      end
  in
    #1 (fold add_parameter source_parameters ([], Symtab.empty))
  end

fun elaborate_function
    ({return_type, name, parameters, body, return_position, position,
      plain_declarator, old_style_declaration_positions}:
      Micro_C_Isabelle_C_Adapter.function_def) : function_def =
  let
    val _ = check_plain_int "function return" return_type
    val (name, name_position) =
      (case name of
         SOME named => named
       | NONE => unsupported "function definitions must be named" position)
    val _ =
      if plain_declarator then ()
      else unsupported "malformed function declarator" name_position
    val _ =
      (case old_style_declaration_positions of
         [] => ()
       | declaration_position :: _ =>
           unsupported
             "old-style function declarations are not supported"
             declaration_position)
    val elaborated_parameters =
      (case parameters of
         Micro_C_Isabelle_C_Adapter.VoidParameters _ => []
       | Micro_C_Isabelle_C_Adapter.NamedParameters
           {parameters, variadic = false, ...} =>
           elaborate_parameters parameters
       | Micro_C_Isabelle_C_Adapter.NamedParameters
           {variadic = true, position, ...} =>
           unsupported "variadic functions are not supported" position
       | Micro_C_Isabelle_C_Adapter.UnspecifiedParameters parameter_position =>
           unsupported
             "zero-parameter functions must use the (void) prototype"
             parameter_position
       | Micro_C_Isabelle_C_Adapter.IdentifierParameters parameter_position =>
           unsupported
             "old-style identifier parameter lists are not supported"
             parameter_position)
  in
    {name = name,
     name_position = name_position,
     parameters = elaborated_parameters,
     body = elaborate_expression elaborated_parameters body,
     return_position = return_position,
     position = position}
  end

end
\<close>

end
