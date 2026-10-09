# µRust parser integration status

This session is the executable specification for the production µRust parser. It keeps positive and
negative syntax coverage, accepted-language improvements, term-shape audits, markup/recovery checks,
and combined showcase examples in one registered session.

## Command surface

Expression declarations retain an optional HOL type and parenthesized declaration arguments.
Function declarations take one complete Rust item:

```isabelle
urust_expr [OPTIONS] NAME [:: TYPE] [(ARG, ...)] ‹ body ›
urust_fn [OPTIONS] [HOL_NAME|_] ‹ fn RustName(PARAMETER: RUST_TYPE, ...) [-> RUST_TYPE] { body } ›
```

The expression argument list is optional, may be empty, and accepts one trailing comma. Arguments are
allocated as typed lexical locals before body elaboration. They therefore shadow existing
unqualified HOL constants and direct-call registrations in value and direct-call positions.
Every multi-segment path instead requires an exact role-appropriate registration: `(literal)` for
values, places, and constructor/struct patterns; `(call)` for calls, struct
expressions, and registered macros, whose key includes the trailing `!`. A registration in another
role does not satisfy the check. Method names remain single-segment and retain registration-first
resolution. `Parser_Command_Tests.thy`
contains the exact `zip` collision: a parameter named `zip` shadows HOL `List.zip`, and the generated
definition is structurally checked not to contain `List.zip`.

Named definition-mode declarations accept standard Isabelle attributes through `attrs = [...]`;
the attributes apply only to the generated `_def` theorem. Rust function parameter and explicit
result types resolve through the same `urust_type` registry as datatype fields. Function
`τ‹HOL type›` escapes support polymorphism, sorts, higher-order types and independent inference
holes; datatype fields remain monomorphic. Omitted results and effect channels infer from the
body, and unused channels generalize.

Named functions register their Rust declaration name by default. Bare, explicit and scoped
`register_notation` controls use `urust_register_notation`, shared with datatypes. Formerly
body-only helpers use `[register_notation = false]` to preserve their registration behavior,
including helpers interpreted repeatedly in locales.

Start with `Parser_Function_Tests.thy` to learn `urust_fn`: it opens with explicit, inferred and
anonymous names, then demonstrates parameter forms, calls, options, HOL escapes, mapped signatures,
inferred effects and locales through ordinary checked declarations. The former Rust-function and
function-type-mapping suites are consolidated here.

`Parser_Function_Regression_Tests.thy` imports those examples and checks their equations, types,
registration, ASTs, diagnostics, parser/printer recovery, locale conflicts and editor navigation.
Its ML harnesses stay in this separate regression theory. `Parser_Command_Tests.thy` retains
shared command/API and expression tests, including comparisons with the imported function artifacts.

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

Array repeats evaluate the length first. Ordinary `[value; length]` evaluates the value once,
including at length zero; `[const { value }; length]` uses
`list_sequence (List.replicate (unat length) value)` and executes the body once per element.
Lengths admit integer literals, parentheses, `+ - * / %`, and `as usize`. Symbolic lengths may
be direct Isabelle fixed parameters, exact literal registrations whose backends depend on the
proof context, or genuine unqualified HOL constants. Qualified paths require exact literal
registration; µRust lexical locals and unresolved names are rejected.

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

Array repeats are a parser-only post-migration extension. Ordinary `[value; length]` evaluates the
length first and the value exactly once, then returns `List.replicate (unat length) value`.
Repeat-local `[const { value }; length]` evaluates the length first and uses
`list_sequence (List.replicate (unat length) value)`, so its body executes once per element.
Lengths are restricted to integer literals, contextual symbolic paths, parentheses, `+ - * / %`,
and `as usize`. A symbolic path may be a direct Isabelle fixed parameter, an exact registered
literal whose backend can depend on the surrounding proof context, or a genuine global constant.
µRust lexical locals and unresolved names remain rejected. The legacy frontend interprets
`[value; length]` as a one-element array containing a sequence, so array repeats require
conformance-disabled declarations.

Scoped cast-target aliases are declared with `urust_cast_alias "SmallId" = "u16"` and may be
captured in bundles. Importing a fixture does not activate its aliases; inclusion activates exact,
qualified, generic-free paths only in that context. Aliases lower to the identical existing primitive
cast term. Identical registrations are idempotent; conflicts report both declaration positions.
Alias chains, general Rust types, and named aliases in repeat lengths remain unsupported.

Exact registered associated items may use the existing integer primitive tokens as path heads:
`u8`, `u16`, `u32`, `u64`, `usize`, `i32`, and `i64`. Literal-role registration is mandatory for
values, patterns, and repeat lengths; call-role registration is mandatory for calls. The primitive
head does not participate in lexical, HOL-name, unresolved-free, or native-constructor fallback.
Identifier-headed paths retain their previous behavior, including unsupported widths such as
`u128`.

## Rust-fidelity boundaries

List matching supports closed lists and a single bare or bound rest at any position:
`[..]`, `[rest @ ..]`, `[first, rest @ ..]`, `[rest @ .., last]`, and
`[first, rest @ .., last]`. Captures preserve order, including when suffix selection reverses the
remaining list internally. Integer literals compose at every structural depth through the existing
value-pattern equality lowering; unguarded numeral/wildcard matches retain switch selection.
Ordinary `let` and `for` accept recursively irrefutable aliases, tuples, and rest-only lists.
Requiring even one list element makes a binding refutable. Direct rest names always bind, even
when they spell a HOL constant or constructor. Duplicate names, multiple rests, and unequal
alternative binder sets reject before arm bodies or guards are lowered.

Direct top-level tuples in `if let` and `let … else` retain their restricted binding policy and
special fallback handling. Constructor-wrapped tuples use case lowering; direct refutable
conditional tuples remain separate work. Existing rejection rows preserve this boundary.

Retained compatibility extensions include complete µRust bodies in guards and statement bodies in
groups, macros, and struct fields. The underscore-before-integer-suffix spelling also remains
accepted. During production migration the parser additionally accepts apostrophised identifiers.
Direct return match arms use commas between arms and an optional final comma. Direct
`return value;,` and `return;` arms are rejected; `{ return value; }` and `{ return; }` retain
ordinary statement semicolons. Complete guard bodies retain return statements.
`Parser_Syntax_Tests.thy` checks all three match forms, guarded and restricted post-block arms,
AST shapes, positioned rejection and recovery, and typed kernel equalities with braced spellings.
Dereference follows Rust's uniform postfix-before-prefix precedence:
`*base[index]` dereferences the indexed value, while `(*base)[index]` explicitly selects
dereference-before-index. `Parser_Precedence_Tests.thy` covers indexed, grouped, call, and field
operands, explicit grouping, and the restricted control-head grammar.
The parser supports binary, octal, decimal, and hexadecimal integers with internal or
trailing underscores and `u8`, `u16`, `u32`, `u64`, and `usize` suffixes. Ordinary source accepts
nested Rust block comments as layout; strings and antiquotations retain marker text, while
restricted turbofish and log-data syntax continue to reject it. Documentation-shaped comments
`/** ... */` and `/*! ... */` are expression layout, without documentation-item semantics.

The following remain deliberately unsupported: one-element tuples, general postfix invocation, open
ranges, unary numeric negation, `/=`, leading `::`, full Rust generics, universal macro
trailing commas, signed integers, `u128`, and floating/character/scientific literals. Focused
negative rows preserve these boundaries.

## Focused regression theories

- `Parser_Expression_Tests.thy`: positive expression syntax, including direct, method and chained
  iterator calls.
- `Parser_Function_Tests.thy`: the declaration-first `urust_fn` reading entry point, consolidating
  complete-item syntax, signatures, mappings, options, lexical binding and locale examples.
- `Parser_Function_Regression_Tests.thy`: the internal audits and negative probes for those
  function examples, including inference, registration, generated artifacts, navigation and recovery.
- `Parser_Improvements_Tests.thy`: accepted language improvements and intentional semantic
  corrections.
- `Parser_Command_Tests.thy`: declaration behavior, named and wildcard parameter slots, options,
  artifacts, markup, and facade audits.
- `Parser_Syntax_Tests.thy`: precedence adjacency, unary/cast/postfix behavior, direct and
  wrapped block-like operands, statement/arm separators, recursive no-struct heads, closures,
  structs, integer lexing, generated grammar, markup, and recovery.
- `Parser_Cast_Target_Aliases_Tests.thy`: bundle and locale scoping, every integral and raw-pointer
  target, exact qualified paths, primitive term equality, repeat integration, conflicts, idempotence,
  positioned diagnostics, navigation markup, and recovery. Its declaration-only fixture is
  `Parser_Cast_Alias_Fixtures.thy`.
- `Parser_Block_Comments_Tests.thy`: nested and adjacent layout, token boundaries, full symbol-aware
  markup, positioned diagnostics, literal and lexer-state boundaries, recovery, repeats, and
  dereference/postfix precedence.
- `Parser_Array_Repeats_Tests.thy`: ordinary and inline-const syntax, restricted length validation,
  evaluation count/order and control propagation, term compactness, markup/navigation, positioned
  diagnostics, recovery, and array/index/borrow/macro regressions.
- `Parser_Pattern_Matching_Tests.thy`: `Ctr_Sugar`, custom enum and simple-word-enum native case
  metadata, bare and qualified exhaustive/partial/guarded/or/nested and singleton simple-word-enum
  matches, metadata-free value/literal equality and switch controls, ordinary and typedef-backed
  basename ambiguity, binder fallback, deep registered nullary
  structural matching, guards, coverage, source order, single evaluation, term shape, markup, and
  recovery.
- `Parser_Primitive_Path_Heads_Tests.thy`: all seven primitive heads, exact literal/call roles,
  comments and token boundaries, expressions, patterns, repeats, cast aliases, positions,
  current notation navigation, fallback rejection, and recovery.
- `Parser_Name_Resolution_Tests.thy`: notation dispatch, navigation, qualifier markup, turbofish,
  and the shared iterator `zip` registration audit.
- `Parser_Slice_Pattern_Syntax_Tests.thy`: positioned bound-rest ASTs, binder markup, malformed
  syntax, binding-site restrictions, and recovery.
- `Parser_Slice_Pattern_Tests.thy`: ordered extraction and fallback equations, bare suffix
  regressions, structural integer matching, irrefutable aliases, scoping, and evaluation effects.
- `Parser_Rejection_Tests.thy`: parser diagnostics and iterator arity failures.
- `Parser_Datatype_Tests.thy`: datatype declarations, generated registrations and navigation,
  scoped/inline field-lens registration control, registry integrity, manual aliases, transactional
  diagnostics, and command output. Declaration-local `renames` coverage checks selector and
  constructor identities, short-name binder hygiene, source aliases and metadata, effective-name
  collisions, quoted-list syntax, positioned recovery, and read-only pretty replay.
- `Parser_Printer_Tests.thy`: serialized and human-readable expression and datatype printing,
  canonicalization, layout, positions, and malformed-AST diagnostics.
- `Parser_Showcase_Tests.thy`: combined command, grammar, matching, array-repeat, and iterator examples.

Shared declaration-only setup lives in `Parser_Iterator_Fixtures.thy`,
`Parser_Registered_Constructor_Fixtures.thy`, `Parser_Cast_Alias_Fixtures.thy`, and the four
ambiguity fixture theories. Shared ML support and test-only rejection commands live in
`Parser_Test_Utils.thy`. Every tracked `.thy` file in this directory is registered in `ROOT`.
