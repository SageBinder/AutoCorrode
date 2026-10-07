(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Concurrent_A
  imports Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

ML_val\<open>
local
  val text =
    "int concurrent_left(int x) {" ^
    "  for (int i = 0; i < 3; i++) x += i;" ^
    "  return x;" ^
    "}"
  val start = \<^here>
  val source =
    Input.source true text
      (Position.range (start, Position.symbol_explode text start))
  val parsed =
    Micro_C_Isabelle_C_Adapter.parse_translation_unit source \<^theory>
in
  val _ =
    (case Micro_C_Isabelle_C_Adapter.ast parsed of
       C_Ast.CTranslUnit0 ([C_Ast.CFDefExt0 _], _) => ()
     | _ => error "concurrent parser test A: wrong translation unit")
end
\<close>

end
