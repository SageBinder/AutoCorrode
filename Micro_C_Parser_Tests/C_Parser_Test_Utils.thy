(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Test_Utils
  imports Micro_C_Parsing_Frontend.C_To_Core_Translation
begin

lemma c_test_bounded_while_numeral:
  "bounded_while (numeral n) condition body =
    bind condition (\<lambda>continue.
      if continue then
        sequence body (bounded_while (pred_numeral n) condition body)
      else skip)"
  by (simp only: numeral_eq_Suc bounded_while.simps)

lemma c_test_upt_numeral:
  "[i..<numeral n] =
    (if i \<le> pred_numeral n then [i..<pred_numeral n] @ [pred_numeral n] else [])"
  by (simp only: numeral_eq_Suc upt_Suc)

lemmas c_test_eval_simps =
  evaluate_def literal_def call_def evaluate_call_function_body
  bind_evaluate bind.simps call_function_body.simps
  return_func_def return_val_def sequence_def
  two_armed_conditional_def raw_for_loop_def
  bounded_while.simps c_test_bounded_while_numeral c_test_upt_numeral
  abort_def c_abort_def
  c_unsigned_add_def c_unsigned_sub_def c_unsigned_mul_def
  c_unsigned_div_with_abort_def c_unsigned_mod_with_abort_def
  c_signed_add_with_abort_def c_signed_sub_with_abort_def
  c_signed_mul_with_abort_def c_signed_div_with_abort_def c_signed_mod_with_abort_def
  c_trunc_div_int_def c_trunc_mod_int_def
  c_unsigned_and_def c_unsigned_or_def c_unsigned_xor_def c_unsigned_not_def
  c_signed_and_def c_signed_or_def c_signed_xor_def c_signed_not_def
  c_unsigned_shl_with_abort_def c_unsigned_shr_with_abort_def
  c_signed_shl_with_abort_def c_signed_shr_with_abort_def
  c_signed_shr_conservative_with_abort_def
  c_unsigned_less_def c_unsigned_le_def c_unsigned_eq_def c_unsigned_neq_def
  c_signed_less_def c_signed_le_def c_signed_eq_def c_signed_neq_def
  c_signed_truthy_def c_unsigned_truthy_def
  c_ucast_def c_scast_def c_scast_checked_with_abort_def

text \<open>
  Shared test support uses the production commands and checked HOL definitions.
  Exceptions are captured before assertions are made, so an assertion failure
  cannot be mistaken for the rejection being tested. Interrupts always propagate.
  Each command test starts from an immutable theory value.
\<close>

ML \<open>
structure C_Parser_Test =
struct
  fun assert label condition =
    if condition then () else error ("C regression test: " ^ label)

  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close

  fun source file text =
    let val start = Position.line_file 1 file
    in Input.source true text
      (Position.range (start, Position.symbol_explode text start))
    end

  fun run thy file command =
    let
      val transitions =
        Outer_Syntax.parse_text thy (K thy) (Position.line_file 1 file) command
      val _ = assert (file ^ ": expected exactly one command")
        (length transitions = 1)
    in
      Toplevel.theory_of
        (fold (Toplevel.command_exception true) transitions
          (Toplevel.make_state (SOME thy)))
    end

  fun translate thy file unit options text =
    run thy file ("c_source " ^ unit ^ " " ^ options ^ " " ^ cartouche text)

  fun rejects label fragments action =
    (case Exn.capture action () of
       Exn.Res _ => error ("C regression test: unexpectedly accepted " ^ label)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let
             val message = Runtime.exn_message exn
             val _ = List.app (fn fragment =>
               assert (label ^ ": expected " ^ quote fragment ^
                 " in diagnostic:\n" ^ message)
                 (String.isSubstring fragment message)) fragments
           in message end)

  fun constant ctxt name =
    Proof_Context.read_const {proper = true, strict = true} ctxt name

  fun absent ctxt name =
    assert ("unexpected constant " ^ quote name) (not (can (constant ctxt) name))

  fun absent_type ctxt name =
    assert ("unexpected type " ^ quote name)
      (not (can (Proof_Context.read_type_name {proper = true, strict = true} ctxt) name))

  fun rhs ctxt name =
    Proof_Context.get_thm ctxt (name ^ "_def")
    |> Thm.prop_of |> Logic.dest_equals |> snd

  fun has_const name =
    Term.exists_subterm (fn Const (candidate, _) => candidate = name | _ => false)

  fun require_consts ctxt name expected forbidden =
    let val term = rhs ctxt name
    in
      List.app (fn c => assert (name ^ ": missing " ^ c) (has_const c term)) expected;
      List.app (fn c => assert (name ^ ": unexpected " ^ c)
        (not (has_const c term))) forbidden
    end

  fun checked_definition ctxt name =
    let
      val term = rhs ctxt name
      val _ = Thm.cterm_of ctxt term
      val _ = assert (name ^ ": escaped lexical variables")
        (null (Term.add_frees term []))
      val _ = assert (name ^ ": unchecked dummy type")
        (not (Term.exists_type (fn ty => ty = dummyT) term))
      val _ = require_consts ctxt name []
        [\<^const_name>\<open>c_unsupported\<close>,
         \<^const_name>\<open>c_while_stub\<close>, \<^const_name>\<open>c_goto_stub\<close>]
    in () end

  fun check_definitions ctxt unit names =
    List.app (fn name => checked_definition ctxt (unit ^ "." ^ name)) names

  fun argument_types ctxt name = binder_types (fastype_of (constant ctxt name))

  (* Generated memory operations may carry phantom TYPE parameters. They are
     explicit in HOL, but are not C parameters or loop-fuel arguments. *)
  fun value_argument_types ctxt name =
    filter (fn Type ("itself", _) => false | _ => true) (argument_types ctxt name)

  (* Supply irrelevant phantom TYPE arguments when executing a generated
     function from HOL. The remaining arguments are the C arguments and fuel. *)
  fun c_application ctxt application =
    (case space_explode " " application of
       name :: arguments =>
         let
           val phantoms =
             take_prefix (fn Type ("itself", _) => true | _ => false)
               (argument_types ctxt name)
         in
           space_implode " " (name :: replicate (length phantoms) "TYPE(unit)" @ arguments)
         end
     | [] => error "C regression test: empty function application")

  fun require_arguments ctxt name expected =
    assert (name ^ ": wrong parameter types")
      (argument_types ctxt name = expected)

  fun prove ctxt facts proposition =
    Goal.prove ctxt [] [] (Syntax.read_prop ctxt proposition)
      (fn {context, ...} =>
        HEADGOAL (simp_tac (context addsimps
          (maps (Proof_Context.get_thms context) facts))))
    |> K ()

  fun evaluates ctxt application result =
    prove ctxt ["shallow_computation_simps", "c_test_eval_simps"]
      ("evaluate (call (" ^ c_application ctxt application ^ ")) () = " ^ result ^ " ()")
end
\<close>

end
