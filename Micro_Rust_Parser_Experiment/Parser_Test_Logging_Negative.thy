theory Parser_Test_Logging_Negative
  imports Parser_Test_Negative_Conformance Parser_Test_Logging
begin

section\<open> Malformed logging-data expressions \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>, True\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True,\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True,, False\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True False\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>1\<rrangle> \<close>
  \<open> unexpected input "1" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>\<llangle>True\<rrangle>\<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>Foo::Bar\<rrangle> \<close>
  \<open> unexpected input ":" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True()\<rrangle> \<close>
  \<open> unexpected input "(" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>True + False\<rrangle> \<close>
  \<open> unexpected input "+" \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>l\<llangle>True\<rrangle>\<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l \<llangle>True\<rrangle> \<close>
  \<open> syntax error \<close>

urust_expr_rejects fidelity
  \<open> \<rrangle> \<close>
  \<open> unexpected input \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>"unterminated \<close>
  \<open> malformed or unterminated string literal \<close>

urust_expr_rejects fidelity
  \<open> l\<llangle>"text", True \<close>
  \<open> unterminated log data \<close>

end
