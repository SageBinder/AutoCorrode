# µRust parser integration status

This session is the executable specification for the production µRust parser. It keeps shared-source
conformance against the legacy frontend, parser-only improvements, negative fidelity boundaries,
term-shape audits, markup/recovery checks, and combined showoff examples in one registered session.

## Command surface

`urust_expr` and `urust_fn` retain the parenthesized declaration-argument syntax, and
`urust_datatype` adds complete Rust-shaped datatype items:

```isabelle
urust_expr [OPTIONS] NAME [:: TYPE] [(ARG, ...)] \<open> body \<close>
urust_fn [OPTIONS] NAME :: TYPE [(PARAMETER, ...)] \<open> body \<close>
urust_datatype [verbosity = 0|1|2] [HOL_NAME] \<open> struct-or-enum \<close>
```

The list is optional, may be empty, and accepts one trailing comma. Declaration arguments are
allocated as typed lexical locals before body elaboration. They therefore shadow existing
unqualified HOL constants and direct-call registrations in value and direct-call positions.
Every multi-segment path instead requires an exact role-appropriate registration: `(literal)` for
values, places, and constructor/struct patterns; `(call)` for calls, struct
expressions, and registered macros, whose key includes the trailing `!`. A registration in another
role does not satisfy the check. Method names remain single-segment and retain registration-first
resolution. `Parser_Tests_Misc.thy`
contains the exact `zip` collision: a parameter named `zip` shadows HOL `List.zip`, the conformance
theorem closes by reflexivity, and the generated definition is structurally checked not to contain
`List.zip`.

Named definition-mode declarations accept standard Isabelle attributes through `attrs = [...]`;
the attributes apply only to the generated `_def` theorem. An exact terminal `_` in an `urust_fn`
type is completed to a fresh five-parameter `function_body` before ordinary checked elaboration.

`urust_datatype` infers an omitted HOL binding with acronym-aware ASCII snake case and does not
accept `_` as a placeholder. Named structs use `datatype_record` plus the programmatic
`micro_rust_record` API; tuple/unit structs and enums use native BNF datatypes. Primitive Rust types
and positioned `τ‹TYPE›` HOL type cartouches are checked before generation; the `τ` prefix receives
literal PIDE markup like the existing `ε` expression-antiquotation prefix. A context-local item
table maps exact Rust paths to the completed HOL constructors and field aliases. Native `Ctr_Sugar`,
`Case_Translation`, and `Code.is_constr` metadata remain authoritative for patterns and arity;
generated constructors are deliberately excluded from unqualified basename fallback.

Implementation ownership is intentionally separated. `Parser_Impl_Datatype.thy` seals datatype
validation, generation, item registration, declaration markup, and verbosity rendering behind the
single `URust_Datatype.define` operation. `Parser_Impl_Command.thy` retains only the common option
machinery, the thin datatype adapter, outer-syntax parser, and command registration.

`Parser_Tests_Datatypes.thy` covers every supported shape, inferred and renamed HOL identities,
acronym/digit conversion, every primitive, nested positioned types, exact 14-field arity, comments,
trailing commas, source-order field aliases, overloaded field spellings, repeated variant basenames,
exact-path resolution, native constructor/case metadata, generated lenses, locale lifetime, markup,
parser recovery, output gates, and cumulative verbosity. Its rejection matrix pins declarations
inside `urust_expr` and `urust_fn`, `_` names, recursive/polymorphic/malformed/unsupported types,
source and generated-name duplicates, incomplete or trailing items, option-schema errors, notation
ownership conflicts, shape/role and arity mismatches, forbidden generic item paths, basename
ambiguity, named-pattern field errors, named-variant construction, and tuple-struct projection.

## Markup corrections and portability

T-41 exposed one pre-existing, datatype-independent markup bug. Struct-expression labels used by
the legacy source-order call syntax were reported as HOL free variables even though lowering erases
the labels completely. The general `URust_Resolution.report_struct_label` hook now retains only its
syntax typing tooltip and emits no `Markup.free`. This applies to ordinary registered struct-call
syntax, nested expressions, and grouped control heads; `Parser_Tests_Misc.thy` contains the portable
regression checks.

That correction is separate from the datatype-specific enhancements. Exact `urust_datatype`
constructor fields are reported as their generated selector constants, generated declaration names
are reported after local-theory completion, primitive `bool` is keyword-marked in datatype type
position, and qualified generated constructor terminals receive constructor styling. A branch that
does not contain `urust_datatype` should take only the generic `report_struct_label` change and the
corresponding `Parser_Tests_Misc.thy` assertions.

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

Terminal dispatch now treats the registered `lift_fun0` through `lift_fun14` backend wrappers as
transparent for constant navigation without changing the stored backend or generated term. Applied
wrappers link to the wrapped term's head constant; `Some`, `Ok`, and `Err` value calls therefore
retain notation navigation and `keyword3` styling while linking to their HOL constructors instead of
`lift_fun1`. Their constructor-pattern occurrences remain ordinary neutral constructor references.
A lifted lambda keeps notation navigation and styling but emits no false wrapper-constant target.
Ordinary registrations, multi-backend multiplicity, qualifier reports, ASTs, and checked terms retain
their previous behavior. `Parser_Tests_Misc.thy` audits each boundary directly.

## Parser and lowering architecture

The grammar has parallel ordinary and no-struct expression families with explicit tiers:
assignment, range, logical OR, logical AND, comparison, bitwise OR, bitwise XOR, bitwise AND,
shifts, additive, multiplicative, cast, prefix, postfix, and primary. Prefix operators bind before
casts, postfix operations bind before prefixes, assignment is right-associative, and ranges and
comparisons are non-associative.

Primitive cast targets may be registered under exact, generic-free paths with
`urust_cast_alias`. The registration is a local declaration, so bundles can capture it and callers
must activate file- or module-local aliases explicitly with `context includes ...`; named locale
contexts use Isabelle's corresponding `opening` syntax. Alias lowering emits exactly the primitive
cast term.

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
3. authentic `Code.is_constr`/`Ctr_Sugar` lookup only for unqualified unregistered names.

Registered literals with native case metadata are constructors. Registered literals without it are
values and need no downstream family registration. Binder-free, guard-free value/wildcard arms may
use switch/equality lowering; authentic constructors, bindings, and other structural patterns use
case lowering at every nesting depth, including registered nullary constructors. Exact registration
remains a resolution and markup route, not a lowering distinction. Bare basename ambiguity reports
every candidate and is never resolved from the expected result type.
Qualified constructor and struct-pattern metadata is selected from the exact registered `NLiteral`
backend; parsed source `::` separators are never treated as Isabelle long-name separators.

The shared shallow iterator `zip` combines iterator thunk lists with HOL `List.zip`, truncates to the
shorter input, and calls each left thunk before its paired right thunk exactly once. The registered
method uses ordinary receiver-prepending call resolution and returns the established µRust pair
`(left, right, TNil)`.

Array repeats are a parser-only post-migration extension. Ordinary `[value; length]` evaluates the
length first and the value exactly once, then returns `List.replicate (unat length) value`.
Repeat-local `[const { value }; length]` evaluates the length first and uses
`list_sequence (List.replicate (unat length) value)`, so its body executes once per element.
Lengths are restricted to integer literals, contextual symbolic paths, parentheses, `+ - * / %`,
and `as usize`. A symbolic path may be a direct Isabelle fixed parameter, an exact registered
literal whose backend can depend on the surrounding proof context, or a genuine unqualified global
constant. Qualified lengths require an exact literal registration.
µRust lexical locals and unresolved names remain rejected. The legacy frontend interprets
`[value; length]` as a one-element array containing a sequence, so array repeats require
conformance-disabled declarations.

Exact registered associated items may use the existing integer primitive tokens as path heads:
`u8`, `u16`, `u32`, `u64`, `usize`, `i32`, and `i64`. Literal-role registration is mandatory for
values, patterns, and repeat lengths; call-role registration is mandatory for calls. The primitive
head does not participate in lexical, HOL-name, unresolved-free, or native-constructor fallback.
Identifier-headed multi-segment paths follow the common exact role-specific registration policy;
unsupported widths such as `u128` remain identifier tokens.

## Rust-fidelity boundaries

Retained compatibility extensions include complete µRust bodies in guards and statement bodies in
groups, macros, and struct fields. The underscore-before-integer-suffix spelling and apostrophised
identifiers also remain accepted during production migration. Dereference follows Rust's uniform
postfix-before-prefix precedence, so `*base[index]` dereferences the indexed value and
`(*base)[index]` explicitly selects the former dereference-before-index meaning. Direct return match
arms require a comma; semicolon-terminated returns remain accepted inside braced arm bodies. The
parser supports binary, octal, decimal, and hexadecimal integers with internal or trailing
underscores and `u8`, `u16`, `u32`, `u64`, and `usize` suffixes. Ordinary source accepts nested Rust
block comments as layout; strings and antiquotations retain the same marker text, while restricted
turbofish and log-data syntax continue to reject it.

The following remain deliberately unsupported: one-element tuples, general postfix invocation, open
ranges, unary numeric negation, `/=`, leading `::`, full Rust generics, universal macro
trailing commas, signed integers, `u128`, and floating/character/scientific literals. Focused
negative rows preserve these boundaries.

## Focused regression theories

- `Parser_Tests_Grammar_Literals.thy`: precedence adjacency, unary/cast/postfix behavior, direct and
  wrapped block-like operands, statement/arm separators, recursive no-struct heads, closures,
  structs, integer lexing, generated grammar, markup, and recovery.
- `Parser_Tests_Cast_Target_Aliases.thy`: bundle and locale scoping, all integral and raw-pointer
  aliases, exact qualified paths, primitive term equivalence, conflicts and idempotence, diagnostics,
  markup, and parser recovery.
- `Parser_Test_Constructor_Matching.thy`: `Ctr_Sugar`, custom enum and simple-word-enum native case
  metadata, metadata-free value/literal equality and switch controls, ambiguity, deep registered
  nullary structural matching, guards, coverage, source order, single evaluation, term shape, markup,
  and recovery.
- `Parser_Test_Iterator_Zip.thy`: empty and unequal inputs, truncation, effect order, single
  evaluation, direct/method/chained resolution, arity preflight, notation registration, and
  separation from pure HOL `List.zip`.
- `Parser_Tests_Array_Repeats.thy`: ordinary and inline-const syntax, restricted length validation,
  evaluation count/order and control propagation, term compactness, frontend divergence,
  markup/navigation, positioned diagnostics, recovery, and regression coverage.
- `Parser_Tests_Primitive_Path_Heads.thy`: all seven primitive heads, exact literal/call role
  selection, comments and token boundaries, expression/pattern/place interactions, AST/range/markup
  audits, fallback rejection, and recovery.
- `Parser_Tests_Improvements.thy`: the executable accepted-improvement inventory, including nested
  block comments, ordinary and inline-const array-repeat behavior, scoped cast-target aliases, and a
  dedicated legacy-matcher-bug section for nested registered nullaries, guarded-or fallthrough,
  shadowed fallback binders, and nested alias capture.
- `Parser_Tests_Negative_Conformance.thy` and `Parser_Tests_Misc.thy`: focused fidelity boundaries,
  outer-opener diagnostics, exact full-span comment markup, literal-state boundaries, and recovery.
- `Parser_Test_Showoff.thy`: combined command, grammar, matching, block-comment, array-repeat,
  scoped cast-alias, primitive-associated-item, and iterator examples.

Every `.thy` file in this directory is registered in `ROOT`.

## Migration-report disposition

| Item | Disposition |
|---|---|
| H-D1 | Fixed with parenthesized lexical declaration arguments; chosen names shadow unqualified HOL/direct-call names. |
| H-D2 | Fixed on `more-features`: postfixes bind before dereference uniformly; the former index meaning requires `(*base)[index]`. |
| H-D3 postfix | Kept. |
| H-D3 cast | Fixed with unary-before-cast precedence. |
| H-D4 | Fixed through exact registered `Case_Translation` recovery. |
| H-D5 | Qualification remains required for ambiguous basenames. |
| H-D6 families | Fixed without downstream or parser-private family registration. |
| H-D6 nested pattern | Fixed by lowering every authenticated constructor structurally, including registered nullaries. |
| H-D7 | Fixed on `more-features`: direct return arms require commas, while braced return statements retain ordinary semicolons. |
| H-D8 | Fixed by centralized integer candidate parsing and validation. |
| H-D9 | Temporarily accepts apostrophised identifiers in ordinary, turbofish, and logging-data contexts. |
| H-D10 | Fixed with exact terminal-`_` `function_body` inference. |
| H-D11 | Fixed by the shared shallow iterator `zip`. |
| H-D12 | Import semantics/public bridge documented; no parser change. |
| P10/P14 | Use argument-taking abbreviations and declaration attributes. |
| P5/P13 | Out of scope; no `ic2` change. |
| Other P-items | Migration tooling/environment issues; no AutoCorrode language feature added. |
