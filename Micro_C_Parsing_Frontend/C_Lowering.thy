(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Lowering
  imports
    C_Elaboration
    Shallow_Micro_C.C_Scalar_Profile
begin

section\<open>Lowering to neutral shallow computation terms\<close>

ML\<open>
signature C_LOWERING =
sig
  val lower_expression:
    C_Elaboration.parameter list -> C_Elaboration.expr -> term
  val lower_function: C_Elaboration.function_def -> term
end

structure C_Lowering : C_LOWERING =
struct

val c_int_type = \<^typ>\<open>c_int\<close>

fun parameter_term ({name, ...}: C_Elaboration.parameter) =
  Free (name, c_int_type)

fun literal value =
  Const (\<^const_name>\<open>Core_Expression.literal\<close>, dummyT) $ value

fun lower_expression parameters expression =
  let
    val environment =
      Symtab.make
        (map (fn parameter => (#name parameter, parameter_term parameter)) parameters)

    fun lower source_expression =
      (case source_expression of
         C_Elaboration.IntLiteral {value, ...} =>
           literal (HOLogic.mk_number c_int_type (IntInf.toInt value))
       | C_Elaboration.Parameter {name, ...} =>
           literal (the (Symtab.lookup environment name))
       | C_Elaboration.Add {left, right, ...} =>
           list_comb
             (Const (\<^const_name>\<open>Core_Expression.bind2\<close>, dummyT),
              [Const (\<^const_name>\<open>c_signed_add\<close>, dummyT),
               lower left,
               lower right]))
  in
    lower expression
  end

fun lower_function
    ({parameters, body, ...}: C_Elaboration.function_def) =
  let
    val return_expression =
      Const (\<^const_name>\<open>Core_Expression.return_func\<close>, dummyT) $
        lower_expression parameters body
    val function_body =
      Const (\<^const_name>\<open>Core_Expression.FunctionBody\<close>, dummyT) $
        return_expression
  in
    fold_rev Term.lambda (map parameter_term parameters) function_body
  end

end
\<close>

end
