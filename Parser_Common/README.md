# Parser Common

This session owns language-neutral support shared by Isabelle_Lex-Yacc frontends:

- positioned source layouts and raw-offset-to-Isabelle-symbol mapping;
- source ranges, raw-offset and range-addressed slices, and positioned parser errors;
- token and PIDE reporting helpers;
- serialized access to the mutable Isabelle_Lex-Yacc runtime;
- parser drivers for repeated entry-point parsing and strict whole-input parsing;
- scoped native output ownership shared by parser declarations and Isabelle tools.

`Parser_Common.Native_Output_Ownership` is the canonical imported owner. Temporary native-result
scopes suppress only their owned result channels and restore callbacks on every exit; authored
output stays outside those scopes. Publication of persistent tool callbacks coordinates with active
scopes, retaining one owner identity for the native process lifetime. Import this ordinary theory
through the session graph rather than evaluating a second copy of its ML structure.

Language-specific ASTs, grammar policy, binders, antiquotations, elaboration, and lowering remain in
their owning frontend sessions.
