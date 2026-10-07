theory Differential_Failures
  imports Differential_Observations
begin

ML \<open>
local
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close

  fun run command_text =
    let
      val theory = @{theory}
      val state = Toplevel.make_state (SOME theory)
      val transitions =
        Outer_Syntax.parse_text theory (K theory)
          (Position.line_file 1 "differential-failure.c") command_text
    in
      fold (Toplevel.command_exception true) transitions state
    end

  fun contains_any needles text =
    List.exists (fn needle => String.isSubstring needle text) needles

  fun expect key needles command_text =
    (case Exn.result run command_text of
       Exn.Res _ =>
         error ("differential failure was accepted: " ^ key)
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn
           in
             if contains_any needles message then
               writeln ("ACDIFF|failure|" ^ key ^ "|rejected")
             else
               error ("wrong differential diagnostic for " ^ key ^
                 ":\n" ^ message)
           end)
in
  val _ =
    expect "variadic" ["variadic"]
      ("c_source DifferentialVariadic " ^
        cartouche
          "int differential_variadic(int first, ...) { return first; }")
  val _ =
    expect "undeclared" ["undeclared function", "missing_callee"]
      ("c_source DifferentialUndeclared " ^
        cartouche
          "int differential_undeclared(void) { return missing_callee(); }")
  val _ =
    expect "parse" ["syntax error", "parse", "unexpected"]
      ("c_source DifferentialParse " ^
        cartouche "int differential_malformed( { return 0; }")
end
\<close>

end
