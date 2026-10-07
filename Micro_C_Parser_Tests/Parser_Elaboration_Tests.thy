(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Elaboration_Tests
  imports Frontend_Common.Frontend_Common
begin

ML_val\<open>
local
  structure D = Frontend_Diagnostics
  structure T = Frontend_HOL_Term

  val pos = \<^here>

  fun assert message condition =
    if condition then ()
    else error ("frontend support test: " ^ message)

  fun rejects label fragment thunk =
    ((thunk ();
      error ("frontend support test: accepted " ^ label))
     handle ERROR message =>
       assert
         ("wrong rejection for " ^ label ^ ": " ^ message)
         (String.isSubstring fragment message))

  val diagnostic =
    D.make D.Error pos "invalid declaration" ["expected a C identifier"]
  val rendered = D.render diagnostic
  val _ =
    assert "diagnostic omitted its message"
      (String.isSubstring "invalid declaration" rendered)
  val _ =
    assert "diagnostic omitted its note"
      (String.isSubstring "expected a C identifier" rendered)

  val _ =
    rejects "unsupported construct" "unsupported source construct"
      (fn () => D.unsupported pos "computed goto")
  val _ =
    rejects "protected exception" "checking generated fragment"
      (fn () =>
        D.protect pos "checking generated fragment"
          (fn () => error "inner failure"))

  val binding = T.qualified_binding "Example_Unit" "answer" pos
  val _ =
    assert "qualified binding lost its base name"
      (Binding.name_of binding = "answer")

  val ctxt = \<^context>
  val checked_nat =
    T.check_term ctxt pos "natural literal" (T.mk_nat 42)
  val _ =
    assert "natural literal has the wrong type"
      (fastype_of checked_nat = HOLogic.natT)

  val checked_option =
    T.mk_option HOLogic.natT (SOME (T.mk_nat 1))
    |> T.check_term ctxt pos "optional natural"
  val _ =
    assert "option constructor has the wrong type"
      (fastype_of checked_option =
        Type (\<^type_name>\<open>option\<close>, [HOLogic.natT]))

  val checked_list =
    T.mk_list HOLogic.boolT [T.mk_bool true, T.mk_bool false]
    |> T.check_term ctxt pos "boolean list"
  val _ =
    assert "list constructor has the wrong type"
      (fastype_of checked_list =
        Type (\<^type_name>\<open>list\<close>, [HOLogic.boolT]))

  val abstraction =
    T.abstracts [("x", HOLogic.natT)]
      (Bound 0)
    |> T.check_term ctxt pos "identity abstraction"
  val _ =
    assert "abstraction has the wrong type"
      (fastype_of abstraction = HOLogic.natT --> HOLogic.natT)

  val _ =
    rejects "undeclared constant" "ill-formed HOL term"
      (fn () =>
        T.check_term ctxt pos "missing constant"
          (Const ("Frontend_Common.missing", dummyT)))
in
  val _ = ()
end
\<close>

end
