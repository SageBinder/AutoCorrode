theory C_Parser_Smoke
  imports
    Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

section \<open>Isabelle/C Parser Smoke Tests\<close>

text \<open>Verify representative fragments through the sole Isabelle/C adapter boundary.\<close>

ML_val \<open>
local
  structure A = Micro_C_Isabelle_C_Adapter

  fun source text =
    let
      val start = \<^here>
      val stop = Position.symbol_explode text start
    in
      Input.source true text (Position.range (start, stop))
    end

  fun external_declarations text =
    (case A.ast (A.parse_translation_unit (source text) \<^theory>) of
       C_Ast.CTranslUnit0 (declarations, _) => declarations)

  val main =
    external_declarations
      "int main(void) {\n\
      \  return 0;\n\
      \}\n"

  val swap =
    external_declarations
      "void swap(int *a, int *b) {\n\
      \  int t = *a;\n\
      \  *a = *b;\n\
      \  *b = t;\n\
      \}\n"

  val _ =
    if length main = 1 andalso length swap = 1 then ()
    else error "adapter parser smoke test discarded an external declaration"
in
  val _ = ()
end
\<close>

end
