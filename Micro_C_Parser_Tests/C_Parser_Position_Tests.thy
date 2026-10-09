(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Position_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Source ranges and provenance\<close>

text \<open>
  Raw upstream AST positions retain offsets and lines, but need not include a
  filename. Provenance is checked through source recovery on each parsed unit
  and through positioned frontend diagnostics, which retain the input identity.
\<close>

ML_val \<open>
local
  structure A = Micro_C_Isabelle_C_Adapter
  fun parse (file, text) =
    (file, text, A.parse_translation_unit (C_Parser_Test.source file text) \<^theory>)
  val inputs =
    [("position-left.c", "// heading\nint probe(int x) {\n return x + 1;\n}\n"),
     ("position-right.c", "/* heading */\nint probe(int x) {\n return x + 2;\n}\n")]
  val parsed = map parse inputs
  fun check (file, text, unit) =
    let
      val (name_info, function_info) =
        (case A.ast unit of
           C_Ast.CTranslUnit0
             ([C_Ast.CFDefExt0
               (C_Ast.CFunDef0
                 (_, C_Ast.CDeclr0 (C_Ast.Some
                   (C_Ast.Ident0 (_, _, ident_info)), _, _, _, _), _, _, info))], _) =>
               (ident_info, info)
         | _ => error ("unexpected position-test AST in " ^ file))
      val name_pos = A.node_position name_info
      val function_pos = A.node_position function_info
      val _ = List.app (fn pos =>
        (C_Parser_Test.assert (file ^ ": missing reported source range")
           (Position.is_reported_range pos);
         C_Parser_Test.assert (file ^ ": wrong source line")
           (Position.line_of pos = SOME 2))) [name_pos, function_pos]
      val _ = C_Parser_Test.assert (file ^ ": incorrect identifier range")
        (A.source_text unit name_pos = SOME "probe")
      val _ = C_Parser_Test.assert (file ^ ": incorrect function range")
        (case A.source_text unit function_pos of
           SOME recovered =>
             Symbol.trim_blanks recovered =
               Symbol.trim_blanks (cat_lines (tl (space_explode "\n" text)))
         | NONE => false)
      val outside = Position.of_properties
        [(Markup.offsetN, "10001"), (Markup.end_offsetN, "10002")]
      val _ = C_Parser_Test.assert (file ^ ": accepted range outside the source")
        (A.source_text unit outside = NONE)
      val _ = C_Parser_Test.assert (file ^ ": accepted absent range")
        (A.source_text unit Position.none = NONE)
      val _ = C_Parser_Test.rejects (file ^ ": diagnostic source identity")
        [file, "undefined variable"]
        (fn () => C_Parser_Test.translate \<^theory> file "PositionRejected" ""
          "// heading\nint rejected(int x) { return missing; }\n")
    in () end
  val _ = List.app check parsed
in
  val _ = ()
end
\<close>

end
