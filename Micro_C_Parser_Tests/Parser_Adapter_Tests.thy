(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Adapter_Tests
  imports Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

ML_val\<open>
local
  structure A = Micro_C_Isabelle_C_Adapter

  fun assert message condition =
    if condition then ()
    else error ("C adapter test: " ^ message)

  fun source text =
    let
      val start = \<^here>
      val stop = Position.symbol_explode text start
    in
      Input.source true text (Position.range (start, stop))
    end

  fun identifier_name (C_Ast.Ident0 (name, _, _)) =
    C11_Ast_Lib.toString_abr_string name

  fun identifier_node (C_Ast.Ident0 (_, _, node)) = node

  val text =
    "struct pair { int left; int right; };\n" ^
    "int global = 3;\n" ^
    "int sum(int x) { while (x) { x--; } return x; }\n"
  val parsed = A.parse_translation_unit (source text) \<^theory>

  val (external_declarations, unit_node) =
    (case A.ast parsed of
       C_Ast.CTranslUnit0 data => data)

  val _ =
    assert "adapter rejected or discarded external declarations"
      (length external_declarations = 3)

  val (function_name, function_node) =
    (case List.last external_declarations of
       C_Ast.CFDefExt0
         (C_Ast.CFunDef0
           (_, C_Ast.CDeclr0 (C_Ast.Some name, _, _, _, _),
            _, _, node)) =>
         (name, node)
     | _ => error "C adapter test: expected a raw function definition")

  val name_position = A.node_position (identifier_node function_name)
  val function_position = A.node_position function_node
  val unit_position = A.node_position unit_node

  val _ =
    assert "wrong raw function name"
      (identifier_name function_name = "sum")
  val _ =
    assert "identifier position is not a reported range"
      (Position.is_reported_range name_position)
  val _ =
    assert "function position is not a reported range"
      (Position.is_reported_range function_position)
  val _ =
    assert "translation-unit position is not a reported range"
      (Position.is_reported_range unit_position)
  val _ =
    assert "source extraction did not recover the identifier"
      (A.source_text parsed name_position = SOME "sum")
  val _ =
    assert "source extraction accepted an absent position"
      (A.source_text parsed Position.none = NONE)

  val _ =
    (case hd external_declarations of
       C_Ast.CDeclExt0 _ => ()
     | _ => error "C adapter test: declaration AST was normalized away")

  val malformed =
    Exn.capture
      (fn () =>
        A.parse_translation_unit
          (source "int broken( { return 0; }") \<^theory>)
      ()
  val _ =
    (case malformed of
       Exn.Exn (ERROR _) => ()
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ => error "C adapter test: malformed C was accepted")
in
  val _ = ()
end
\<close>

end
