# Parser Common

This session owns language-neutral support shared by Isabelle_Lex-Yacc frontends:

- positioned source layouts and raw-offset-to-Isabelle-symbol mapping;
- source ranges, slices, and positioned parser errors;
- token and PIDE reporting helpers;
- serialized access to the mutable Isabelle_Lex-Yacc runtime;
- parser drivers for repeated entry-point parsing and strict whole-input parsing.

Language-specific ASTs, grammar policy, binders, antiquotations, elaboration, and lowering remain in
their owning frontend sessions.
