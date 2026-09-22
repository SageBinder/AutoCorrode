# µRust parser integration status

This session is the executable specification for the production µRust parser. It keeps shared-source
conformance against the legacy frontend, parser-only improvements, negative fidelity boundaries,
term-shape audits, markup/recovery checks, and combined showcase examples in one registered session.

## Command surface

`urust_expr` and `urust_fn` retain the parenthesized declaration-argument syntax:

```isabelle
urust_expr [OPTIONS] NAME [:: TYPE] [(ARG, ...)] \<open> body \<close>
urust_fn [OPTIONS] NAME :: TYPE [(PARAMETER, ...)] \<open> body \<close>
```

The list is optional, may be empty, and accepts one trailing comma. Declaration arguments are
allocated as typed lexical locals before body elaboration. They therefore shadow existing
unqualified HOL constants and direct-call registrations in value and direct-call positions.
Every multi-segment path instead requires an exact role-appropriate registration: `(literal)` for
values, places, and constructor/struct patterns; `(call)` for calls, struct
expressions, and registered macros, whose key includes the trailing `!`. A registration in another
role does not satisfy the check. Method names remain single-segment and retain registration-first
resolution. `Parser_Command_Tests.thy`
contains the exact `zip` collision: a parameter named `zip` shadows HOL `List.zip`, the conformance
theorem closes by reflexivity, and the generated definition is structurally checked not to contain
`List.zip`.

Named definition-mode declarations accept standard Isabelle attributes through `attrs = [...]`;
the attributes apply only to the generated `_def` theorem. An exact terminal `_` in an `urust_fn`
type is completed to a fresh five-parameter `function_body` before ordinary checked elaboration.

## Markup correction

Struct-expression labels used by the source-order call syntax are erased during lowering and do not
denote HOL terms. `URust_Resolution.report_struct_label` therefore retains their syntax typing
tooltip without reporting them as `Markup.free`. `Parser_Syntax_Tests.thy` checks ordinary registered
struct calls, nested expressions, and grouped control heads.

Every qualifier of an exact registered path has one role-specific tooltip without pretending to be
a HOL Free, constant, type, or constructor. An authenticated constructor's nearest qualifier retains
its datatype navigation and `keyword3` styling; earlier module-like segments remain neutral.
Notation references are deferred until typed dispatch selects a backend. Backend and datatype
entities are reported first, then every declaration reference exactly once with the selected
`micro_rust_notation` declaration last on the terminal and every qualifier, so Ctrl-click reaches
the declaration that supplied the checked term while hover retains the backend information.
Validated constructor patterns use the same ordering; if several entries authenticate the same
constructor, the lowest serial is the deterministic target. Native fallback syntax still links only
to its HOL entity.

Single-segment names, unresolved identifiers, diagnostics, ASTs, and checked terms are unchanged.
The consolidated markup audits cover both selections of overloaded literals and calls, fields,
values and patterns, struct heads, both turbofish lookup routes, complete macro keys including `!`,
lifted functions and lambdas, registration multiplicity and idempotence, constructor families,
delayed failures, recovery, and lexical/fixed controls.

Generic macro heads that fall through registered-call lookup now pair their semantic keyword styling
with one exact identifier-range typing tooltip. This prevents the enclosing uRust language report
from becoming the hover range for built-ins such as `assert!`; the same shared path covers assertion
aliases, message macros, `vec!`, and address macros. The dedicated `matches!` token retains its
existing lexer-owned typing report without duplication.

Terminal dispatch now treats the registered `lift_fun0` through `lift_fun14` backend wrappers as
transparent for constant navigation without changing the stored backend or generated term. Applied
wrappers link to the wrapped term's head constant; `Some`, `Ok`, and `Err` value calls therefore
retain notation navigation and `keyword3` styling while linking to their HOL constructors instead of
`lift_fun1`. Their constructor-pattern occurrences remain ordinary neutral constructor references.
A lifted lambda keeps notation navigation and styling but emits no false wrapper-constant target.
Ordinary registrations, multi-backend multiplicity, qualifier reports, ASTs, and checked terms retain
their previous behavior. `Parser_Name_Resolution_Tests.thy` audits each boundary directly.

## Parser and lowering architecture

The grammar has parallel ordinary and no-struct expression families with explicit tiers:
assignment, range, logical OR, logical AND, comparison, bitwise OR, bitwise XOR, bitwise AND,
shifts, additive, multiplicative, cast, prefix, postfix, and primary. Prefix operators bind before
casts, postfix operations bind before prefixes, assignment is right-associative, and ranges and
comparisons are non-associative.

Blocks, `unsafe`, conditionals, loops, and matches are ordinary primary expressions. Their separate
direct-with-block category is used only to decide whether an outer statement semicolon or non-final
match-arm comma may be omitted. Control heads use the parallel no-struct family recursively; an
explicit delimiter restores unrestricted expression parsing.
After a comma-free direct-with-block arm, the grammar admits only following patterns whose first
token cannot continue the preceding expression. Top-level `&` and `[` patterns therefore require an
explicit comma, while parenthesized forms remain accepted; this boundary is encoded without
generated shift/reduce or reduce/reduce conflicts.

Name and constructor metadata operations remain in `URust_Resolution`. `URust_Patterns` owns one
typed recursive decision compiler for binding, structural selection, guards, source-order fallback,
coverage, and compatibility term shape. The compiler does not maintain parser-private constructor
families or separate guarded/unguarded pattern engines.

Constructor resolution follows one chain:

1. ordinary datatype/codatatype metadata from `Ctr_Sugar`;
2. native `Case_Translation` metadata for an exact registered `NLiteral` backend absent from
   `Ctr_Sugar`;
3. native unqualified lookup only for constants recognized by `Code.is_constr` or
   `Case_Translation`.

Registered literals with native case metadata are constructors. Registered literals without it are
values and need no downstream family registration. Binder-free, guard-free value/wildcard arms may
use switch/equality lowering; authentic constructors, bindings, and other structural patterns use
case lowering at every nesting depth, including registered nullary constructors. Exact registration
remains a resolution and markup route, not a lowering distinction. Bare basename ambiguity reports
every candidate and is never resolved from the expected result type. Bare `simple_word_enum`
variants therefore resolve structurally without requiring a notation alias; unknown identifiers
still fall back to binders.
Qualified constructor and struct-pattern metadata is selected from the exact registered `NLiteral`
backend; parsed source `::` separators are never treated as Isabelle long-name separators.

The shared shallow iterator `zip` combines iterator thunk lists with HOL `List.zip`, truncates to the
shorter input, and calls each left thunk before its paired right thunk exactly once. The registered
method uses ordinary receiver-prepending call resolution and returns the established µRust pair
`(left, right, TNil)`.

## Rust-fidelity boundaries

Retained compatibility extensions include complete µRust bodies in guards and statement bodies in
groups, macros, and struct fields. The underscore-before-integer-suffix spelling also remains
accepted. During production migration the parser additionally accepts apostrophised identifiers,
return-arm semicolons, and narrow legacy
dereference/postfix grouping. Explicitly grouping the complete dereference operand retains Rust
precedence. The parser supports binary, octal, decimal, and hexadecimal integers with internal or
trailing underscores and `u8`, `u16`, `u32`, `u64`, and `usize` suffixes.

The following remain deliberately unsupported: one-element tuples, general postfix invocation, open
ranges, unary numeric negation, `/=`, leading `::`, full Rust generics, universal macro
trailing commas, signed integers, `u128`, and floating/character/scientific literals. Focused
negative rows preserve these boundaries.

## Focused regression theories

- `Parser_Legacy_Frontend_Tests.thy`: legacy inner-syntax and notation-registry tests.
- `Parser_Expr_Conformance_Tests.thy` and `Parser_Fn_Conformance_Tests.thy`: independent
  shared-source parity suites, including direct, method, and chained iterator syntax.
- `Parser_Improvements_Tests.thy`: accepted language improvements, intentional semantic
  corrections, and demonstrated legacy-parser bugs.
- `Parser_Command_Tests.thy`: declaration behavior, named and wildcard parameter slots, options,
  artifacts, timing, markup, and facade audits.
- `Parser_Syntax_Tests.thy`: precedence adjacency, unary/cast/postfix behavior, direct and
  wrapped block-like operands, statement/arm separators, recursive no-struct heads, closures,
  structs, integer lexing, comments, exhaustive array-repeat coverage, generated grammar, markup,
  and recovery.
- `Parser_Pattern_Matching_Tests.thy`: `Ctr_Sugar`, custom enum and simple-word-enum native case
  metadata, bare and qualified exhaustive/partial/guarded/or/nested and singleton simple-word-enum
  matches, the legacy nested-variant catch-all bug, metadata-free value/literal equality and switch
  controls, ordinary and typedef-backed basename ambiguity, binder fallback, deep registered nullary
  structural matching, guards, coverage, source order, single evaluation, term shape, markup, and
  recovery.
- `Parser_Name_Resolution_Tests.thy`: notation dispatch, navigation, qualifier markup, turbofish,
  scoped cast-target aliases, primitive-type path heads, and the shared iterator `zip` registration
  audit.
- `Parser_Rejection_Tests.thy`: parser/frontend rejection parity and iterator arity failures.
- `Parser_Datatype_Tests.thy`: datatype declarations, generated registrations and navigation,
  diagnostics, and command output.
- `Parser_Printer_Tests.thy`: serialized and human-readable expression and datatype printing,
  canonicalization, layout, positions, and malformed-AST diagnostics.
- `Parser_Showcase_Tests.thy`: combined command, grammar, matching, and iterator examples.

Shared declaration-only setup lives in `Parser_Iterator_Fixtures.thy`,
`Parser_Registered_Constructor_Fixtures.thy`, `Parser_Cast_Alias_Fixtures.thy`, and the four
ambiguity fixture theories. Shared ML support and test-only rejection commands live in
`Parser_Test_Utils.thy`. Every tracked `.thy` file in this directory is registered in `ROOT`.
