(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature FRONTEND_HOL_TERM =
sig
  val binding: string -> Position.T -> binding
  val qualified_binding:
    string -> string -> Position.T -> binding

  val check_typ:
    Proof.context -> Position.T -> string -> typ -> typ
  val check_term:
    Proof.context -> Position.T -> string -> term -> term
  val check_terms:
    Proof.context ->
    (Position.T * string * term) list -> term list

  val apply: term -> term list -> term
  val abstracts: (string * typ) list -> term -> term
  val mk_bool: bool -> term
  val mk_nat: int -> term
  val mk_string: string -> term
  val mk_list: typ -> term list -> term
  val mk_option: typ -> term option -> term
end

structure Frontend_HOL_Term : FRONTEND_HOL_TERM =
struct

fun binding name position =
  let
    val result = Binding.make (name, position)
    val _ =
      Frontend_Diagnostics.protect position
        ("invalid HOL binding " ^ quote name)
        (fn () => Binding.check result)
  in
    result
  end

fun qualified_binding qualifier name position =
  binding name position
  |> Binding.qualify true qualifier

fun check_typ ctxt position description typ =
  Frontend_Diagnostics.protect position
    ("ill-formed HOL type for " ^ description)
    (fn () => Syntax.check_typ ctxt typ)

fun check_term ctxt position description term =
  Frontend_Diagnostics.protect position
    ("ill-formed HOL term for " ^ description)
    (fn () => Syntax.check_term ctxt term)

fun check_terms ctxt obligations =
  map
    (fn (position, description, term) =>
      check_term ctxt position description term)
    obligations

fun apply head arguments = list_comb (head, arguments)

fun abstracts parameters body =
  fold_rev Term.absfree parameters body

fun mk_bool true = \<^term>\<open>True\<close>
  | mk_bool false = \<^term>\<open>False\<close>

fun mk_nat value =
  if value < 0
  then error ("cannot construct a HOL natural from " ^ Int.toString value)
  else HOLogic.mk_number HOLogic.natT value

val mk_string = HOLogic.mk_string
val mk_list = HOLogic.mk_list

fun mk_option typ NONE =
      Const (\<^const_name>\<open>None\<close>, Type (\<^type_name>\<open>option\<close>, [typ]))
  | mk_option typ (SOME value) =
      Const
        (\<^const_name>\<open>Some\<close>,
         typ --> Type (\<^type_name>\<open>option\<close>, [typ])) $ value

end
