(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Elaboration_Tests
  imports Micro_C_Parsing_Frontend.C_Lowering
begin

ML_val\<open>
local
  structure A = Micro_C_Isabelle_C_Adapter
  structure E = C_Elaboration

  val pos = \<^here>
  val plain_int: A.positioned_type =
    {kind = A.PlainInt, position = pos}

  fun assert message condition =
    if condition then ()
    else error ("C elaboration test: " ^ message)

  fun literal value spelling representation has_suffix =
    A.IntLiteral
      {value = value,
       spelling = spelling,
       representation = representation,
       has_suffix = has_suffix,
       position = pos}

  fun parameter name: A.parameter =
    {type_spec = plain_int,
     name = SOME (name, pos),
     position = pos,
     plain_declarator = true}

  fun function name parameters body: A.function_def =
    {return_type = plain_int,
     name = SOME (name, pos),
     parameters = parameters,
     body = body,
     return_position = pos,
     position = pos,
     plain_declarator = true,
     old_style_declaration_positions = []}

  fun rejects label fragment thunk =
    ((thunk ();
      error ("C elaboration test: accepted " ^ label))
     handle ERROR message =>
       assert
         ("wrong rejection for " ^ label ^ ": " ^ message)
         (String.isSubstring fragment message))

  val zero =
    E.elaborate_function
      (function "zero" (A.VoidParameters pos)
        (literal 0 "0" A.Decimal false))
  val maximum =
    E.elaborate_function
      (function "maximum" (A.VoidParameters pos)
        (literal 2147483647 "2147483647" A.Decimal false))
  val _ =
    (case (#body zero, #body maximum) of
       (E.IntLiteral {value = 0, ...},
        E.IntLiteral {value = 2147483647, ...}) => ()
     | _ => error "C elaboration test: literal boundary elaboration failed")

  val _ =
    rejects "out-of-range literal" "outside the prototype plain-int range"
      (fn () =>
        E.elaborate_function
          (function "large" (A.VoidParameters pos)
            (literal 2147483648 "2147483648" A.Decimal false)))
  val _ =
    rejects "suffixed literal" "suffixed integer literals"
      (fn () =>
        E.elaborate_function
          (function "suffixed" (A.VoidParameters pos)
            (literal 1 "1U" A.Decimal true)))
  val _ =
    rejects "hexadecimal literal" "hexadecimal integer literals"
      (fn () =>
        E.elaborate_function
          (function "hexadecimal" (A.VoidParameters pos)
            (literal 1 "0x1" A.Hexadecimal false)))
  val _ =
    rejects "octal literal" "octal integer literals"
      (fn () =>
        E.elaborate_function
          (function "octal" (A.VoidParameters pos)
            (literal 1 "01" A.Octal false)))
  val _ =
    rejects "unary-negative literal" "expected an unsuffixed decimal"
      (fn () =>
        E.elaborate_function
          (function "negative" (A.VoidParameters pos)
            (literal ~1 "-1" A.Decimal false)))

  val _ =
    rejects "unknown identifier" "unknown identifier"
      (fn () =>
        E.elaborate_function
          (function "unknown"
            (A.NamedParameters
              {parameters = [parameter "x"],
               variadic = false,
               position = pos})
            (A.Identifier {name = "y", position = pos})))

  val _ =
    rejects "duplicate parameters" "duplicate parameter"
      (fn () =>
        E.elaborate_function
          (function "duplicate"
            (A.NamedParameters
              {parameters = [parameter "x", parameter "x"],
               variadic = false,
               position = pos})
            (A.Identifier {name = "x", position = pos})))

  val unnamed_parameter: A.parameter =
    {type_spec = plain_int,
     name = NONE,
     position = pos,
     plain_declarator = true}
  val _ =
    rejects "unnamed parameter" "parameters must be named"
      (fn () =>
        E.elaborate_function
          (function "unnamed"
            (A.NamedParameters
              {parameters = [unnamed_parameter],
               variadic = false,
               position = pos})
            (literal 0 "0" A.Decimal false)))

  val unsupported_return =
    {kind = A.UnsupportedType "unsigned",
     position = pos}: A.positioned_type
  val _ =
    rejects "non-int return" "unsupported type"
      (fn () =>
        E.elaborate_function
          {return_type = unsupported_return,
           name = SOME ("bad_return", pos),
           parameters = A.VoidParameters pos,
           body = literal 0 "0" A.Decimal false,
           return_position = pos,
           position = pos,
           plain_declarator = true,
           old_style_declaration_positions = []})

  val bad_parameter: A.parameter =
    {type_spec = {kind = A.Void, position = pos},
     name = SOME ("x", pos),
     position = pos,
     plain_declarator = true}
  val _ =
    rejects "non-int parameter" "must have plain int type"
      (fn () =>
        E.elaborate_function
          (function "bad_parameter"
            (A.NamedParameters
              {parameters = [bad_parameter],
               variadic = false,
               position = pos})
            (literal 0 "0" A.Decimal false)))

  val _ =
    rejects "variadic prototype" "variadic functions"
      (fn () =>
        E.elaborate_function
          (function "variadic"
            (A.NamedParameters
              {parameters = [parameter "x"],
               variadic = true,
               position = pos})
            (A.Identifier {name = "x", position = pos})))
  val _ =
    rejects "unspecified prototype" "must use the (void) prototype"
      (fn () =>
        E.elaborate_function
          (function "unspecified" (A.UnspecifiedParameters pos)
            (literal 0 "0" A.Decimal false)))
  val _ =
    rejects "identifier-list prototype" "identifier parameter lists"
      (fn () =>
        E.elaborate_function
          (function "old_style" (A.IdentifierParameters pos)
            (literal 0 "0" A.Decimal false)))
  val _ =
    rejects "malformed declarator" "malformed function declarator"
      (fn () =>
        E.elaborate_function
          {return_type = plain_int,
           name = SOME ("malformed", pos),
           parameters = A.VoidParameters pos,
           body = literal 0 "0" A.Decimal false,
           return_position = pos,
           position = pos,
           plain_declarator = false,
           old_style_declaration_positions = []})

  val pure_function =
    E.elaborate_function
      (function "pure_phase"
        (A.NamedParameters
          {parameters = [parameter "x", parameter "y"],
           variadic = false,
           position = pos})
        (A.Add
          {left = A.Identifier {name = "x", position = pos},
           right = A.Identifier {name = "y", position = pos},
           position = pos,
           operator_position = pos}))
  val thy = Proof_Context.theory_of \<^context>
  val _ = assert "pure test precondition"
    (not (Sign.declared_const thy "c_pure_phase"))
  val lowered = C_Lowering.lower_function pure_function
  val _ =
    (case lowered of
       Abs (_, _, Abs (_, _, Const (name, _) $ _)) =>
         assert "lowered FunctionBody"
           (name = \<^const_name>\<open>Core_Expression.FunctionBody\<close>)
     | _ => error "C elaboration test: wrong lowered function shape")
  val _ =
    assert "lowering installed a declaration"
      (not (Sign.declared_const
        (Proof_Context.theory_of \<^context>) "c_pure_phase"))
in
  val _ = ()
end
\<close>

end
