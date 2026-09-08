(* Roll-up facade for the custom uRust parser. *)

theory Parser_Impl
  imports Parser_Impl_Command
begin

text\<open>
Parser clients import this roll-up facade. Programmatic clients use the sealed
\<open>URust_Command\<close> interface. Frontend conformance is tested in
\<open>Parser_Test_Expr_Conformance.thy\<close>; function-command conformance and facade
smoke tests are part of the separate \<open>Micro_Rust_Parser_Tests\<close> session.
\<close>

end
