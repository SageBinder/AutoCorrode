theory Parser_Test_Logging
  imports Parser_Impl Micro_Rust_Std_Lib.StdLib_Logging
begin

text\<open>
This theory intentionally remains separate from \<open>Parser_Test_Conformance\<close>.
The \<open>StdLib_Logging\<close> import supplies the legacy frontend syntax used as the
oracle for \<open>l\<llangle>...\<rrangle>\<close>, and it also registers \<open>fatal!\<close>,
\<open>info!\<close>, and the other logger calls. In particular, registered
\<open>fatal!\<close> takes precedence over the built-in macro in this context.
Keeping the import isolated preserves the main suite's built-in \<open>fatal!\<close>
coverage.
\<close>

section\<open> Logging-data expressions \<close>

urust_expr_with_check log_data_one_string
  \<open> l\<llangle>"one"\<rrangle> \<close>

context
  fixes context_value :: nat
begin

urust_expr_with_check log_data_one_identifier
  \<open> l\<llangle>context_value\<rrangle> \<close>

urust_expr_with_check log_data_mixed
  \<open> l\<llangle>"value = ", context_value, "."\<rrangle> \<close>

urust_expr_with_check log_data_repeated_identifier
  \<open> l\<llangle>context_value, context_value, context_value\<rrangle> \<close>

end

urust_expr_with_check log_data_long
  \<open>
    l\<llangle>
      "a", True, "b", False, "c", True,
      "d", False, "e", True, "f", False
    \<rrangle>
  \<close>

urust_expr_with_check log_data_empty_string
  \<open> l\<llangle>""\<rrangle> \<close>

urust_expr_with_check log_data_multiline
  \<open>
    l\<llangle>
      "first",
      True,
      "second",
      False
    \<rrangle>
  \<close>

subsection\<open> String-token boundaries \<close>

urust_expr_with_check log_data_escaped_quote
  \<open> l\<llangle>"say: \"hello\""\<rrangle> \<close>

urust_expr_with_check log_data_escaped_backslash
  \<open> l\<llangle>"left\\right"\<rrangle> \<close>

urust_expr_with_check log_data_comma_in_string
  \<open> l\<llangle>"left, right"\<rrangle> \<close>

urust_expr_with_check log_data_comment_text
  \<open> l\<llangle>"https://example.invalid//path"\<rrangle> \<close>

urust_expr_with_check log_data_keyword_text
  \<open> l\<llangle>"true false let const return log yield l"\<rrangle> \<close>

subsection\<open> Identifier resolution and lexical scope \<close>

definition logging_collision :: nat
  where \<open> logging_collision = 17 \<close>

definition logging_notation_target :: nat
  where \<open> logging_notation_target = 99 \<close>

micro_rust_notation (literal) logging_notation_target ("logging_collision")

urust_expr_with_check log_data_hol_constant
  \<open> l\<llangle>logging_collision\<rrangle> \<close>

urust_expr_with_check log_data_boolean_constant
  \<open> l\<llangle>True, False\<rrangle> \<close>

urust_expr_with_check log_data_local
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    l\<llangle>"value = ", value\<rrangle>
  \<close>

urust_expr_with_check log_data_nested_shadowing
  \<open>
    let value = \<llangle>5 :: nat\<rrangle>;
    let outer = l\<llangle>value\<rrangle>;
    let value = \<llangle>7 :: nat\<rrangle>;
    (outer, l\<llangle>value\<rrangle>)
  \<close>

urust_expr_with_check log_data_constant_named_binder
  \<open>
    let Some = \<llangle>11 :: nat\<rrangle>;
    l\<llangle>Some, Some\<rrangle>
  \<close>

subsection\<open> Registered logging calls \<close>

urust_expr_with_check registered_fatal_logger
  \<open> fatal!(l\<llangle>"fatal", True\<rrangle>) \<close>

urust_expr_with_check registered_info_logger
  \<open> info!(l\<llangle>"info", True\<rrangle>) \<close>

urust_expr_with_check registered_error_logger
  \<open> error!(l\<llangle>"error", True\<rrangle>) \<close>

urust_expr_with_check registered_debug_logger
  \<open> debug!(l\<llangle>"debug", False\<rrangle>) \<close>

urust_expr_with_check registered_trace_logger
  \<open> trace!(l\<llangle>"trace", True\<rrangle>) \<close>

text\<open>
The first row specifically checks that the adjacent registered \<open>fatal!\<close> call wins over the
built-in message macro in this import context. The main conformance theory intentionally does not
import \<open>StdLib_Logging\<close>, so its built-in \<open>fatal!\<close> coverage remains unchanged.
\<close>

end
