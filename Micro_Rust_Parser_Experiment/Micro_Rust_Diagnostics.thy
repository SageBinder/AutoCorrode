theory Micro_Rust_Diagnostics
  imports Micro_Rust_Parser_Grammar
begin

section\<open> Source diagnostics \<close>

text\<open>
C1-I7/C1-I8 keep parser diagnostics at the source boundary. ML-Yacc still performs the same
conflict-free LALR parse with unchanged mode and recovery behavior; this layer only replaces
selected generated token names with their source spellings.
\<close>

ML\<open>
signature URUST_DIAGNOSTICS =
sig
  val humanize_parse_error: string -> string
end

structure URust_Diagnostics : URUST_DIAGNOSTICS =
struct
  fun replace_all needle replacement text =
    let
      val (prefix, suffix) =
        Substring.position needle (Substring.full text)
    in
      if Substring.isEmpty suffix then text
      else
        Substring.string prefix ^ replacement ^
          replace_all needle replacement
            (Substring.string
              (Substring.triml (size needle) suffix))
    end

  val token_spellings =
    [("TEQEQ", "=="),
     ("TARROW", "=>"),
     ("RPAR", ")"),
     ("EOF", "end of input")]

  fun replace_token (token, spelling) =
    replace_all token spelling

  fun humanize_parse_error message =
    if String.isSubstring "syntax error" message
    then fold replace_token token_spellings message
    else message
end
\<close>

end
