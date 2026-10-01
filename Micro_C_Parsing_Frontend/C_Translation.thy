(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Translation
  imports C_Lowering
  keywords "c_translate" :: thy_decl
begin

section\<open>The provisional C translation command\<close>

ML\<open>
signature C_TRANSLATION =
sig
  val install_function:
    C_Elaboration.function_def -> local_theory -> local_theory
  val translate: Input.source -> local_theory -> local_theory
end

structure C_Translation : C_TRANSLATION =
struct

fun generated_binding name position =
  let
    val binding = Binding.make ("c_" ^ name, position)
    val _ =
      Binding.check binding
      handle ERROR message =>
        error
          ("c_translate: invalid generated HOL binding for C function " ^
           quote name ^ ": " ^ message ^ Position.here position)
  in
    binding
  end

fun install_function
    (function as
      {name, name_position, ...}: C_Elaboration.function_def) lthy =
  let
    val binding = generated_binding name name_position
    val full_name = Local_Theory.full_name lthy binding
    val _ =
      if Sign.declared_const (Proof_Context.theory_of lthy) full_name
      then
        error
          ("c_translate: generated constant " ^ quote full_name ^
           " already exists" ^ Position.here name_position)
      else ()
    val term = C_Lowering.lower_function function
    val checked_term = Syntax.check_term lthy term
    val (_, lthy') =
      Local_Theory.define
        ((binding, NoSyn),
         ((Thm.def_binding binding,
           [Attrib.internal name_position
             (K (Named_Theorems.add
               \<^named_theorems>\<open>shallow_computation_simps\<close>))]),
          checked_term)) lthy
  in
    lthy'
  end

fun translate source lthy =
  let
    val normalized =
      Micro_C_Isabelle_C_Adapter.parse_function
        source (Proof_Context.theory_of lthy)
    val elaborated = C_Elaboration.elaborate_function normalized
  in
    install_function elaborated lthy
  end

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>c_translate\<close>
    "parse one C function and install its neutral shallow denotation"
    (Parse.embedded_input >> translate)

end
\<close>

end
