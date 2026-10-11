(* The urust: clause of simple_word_enum next to the parser commands, without the chunk theory. *)

theory Parser_Simple_Word_Enum_Clause_Tests
  imports
    Micro_Rust_Parser_Impl.Parser_Impl_Command
    Shallow_Micro_Rust.Simple_Word_Enum_uRust
begin

section\<open> Clause compatibility without the chunk command \<close>

text\<open>
The chunk command \<open>urust\<close> is registered by the opt-in theory \<open>Parser_Impl_Chunk\<close>. A theory
that imports the single-item parser commands but not that theory keeps \<open>urust\<close> as an ordinary
name, so generated \<open>simple_word_enum\<close> declarations with a \<open>urust: "Name"\<close> clause remain one
command and register their source paths.
\<close>

simple_word_enum (8) clause_kind urust: "ClauseKind" =
    CLK_First = 1
  | CLK_Second = 2

ML_val\<open>
  local
    val keywords = Thy_Header.get_keywords' \<^context>
    fun backend name =
      (case Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NLiteral ("ClauseKind::" ^ name) of
         [{hol_term, ...}] => hol_term
       | entries =>
           error ("clause registration audit: " ^ name ^ " has " ^
             string_of_int (length entries) ^ " backends"))
  in
    val _ =
      if Keyword.is_command keywords "urust"
      then error "clause registration audit: urust is a command keyword without the chunk theory"
      else ()
    val _ = @{assert} (backend "CLK_First" aconv @{term CLK_First})
    val _ = @{assert} (backend "CLK_Second" aconv @{term CLK_Second})
  end
\<close>

urust_fn clause_kind_first \<open> fn ClauseKindFirst() { let first = ClauseKind::CLK_First; () } \<close>

end
