(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Concurrent_B
  imports Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

ML_val\<open>
local
  val text =
    "union value { int integer; char byte; };\n" ^
    "int concurrent_right(union value *p) { return p->integer; }"
  val start = \<^here>
  val source =
    Input.source true text
      (Position.range (start, Position.symbol_explode text start))
  val parsed =
    Micro_C_Isabelle_C_Adapter.parse_translation_unit source \<^theory>
in
  val _ =
    (case Micro_C_Isabelle_C_Adapter.ast parsed of
       C_Ast.CTranslUnit0 ([C_Ast.CDeclExt0 _, C_Ast.CFDefExt0 _], _) => ()
     | _ => error "concurrent parser test B: wrong translation unit")
end
\<close>

end
