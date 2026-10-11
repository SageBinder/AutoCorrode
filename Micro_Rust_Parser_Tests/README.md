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
urust [OPTIONS] ‹ [ω‹OPTIONS›] ITEM ... ›
```

The plain `urust` command declares a nonempty source-ordered chunk of complete `fn`, `struct` and
`enum` items. It is registered by the opt-in theory `Micro_Rust_Parser_Impl.Parser_Impl_Chunk`;
`Parser_Impl_Command` alone keeps `urust` an ordinary name, so the `simple_word_enum … urust:
"Name"` clause remains usable there (`Parser_Simple_Word_Enum_Clause_Tests.thy`). A theory that
imports the chunk theory cannot use that clause: the command keyword starts a new command span.
An optional `ω‹OPTION, OPTION = VALUE, …›` annotation occupies its own line or lines immediately
before the line on which its item starts; a leading `#[repr(…)]` line belongs to its enum, and an
annotation may not share the opening `urust ‹` line. Its payload uses the bracketed-list entry
syntax with the item's single-item schema plus the HOL binding `name` (`name = _` checks a function
without installing anything; datatypes reject `_`). The outer list accepts only `pp_test`,
`pretty`, `verbosity` and `register_notation`; annotation entries replace outer defaults, which
replace scoped configurations. The whole chunk parses, and every annotation payload, schema and
option combination is validated, before the first declaration; checks that depend on earlier
members (registration conflicts, field and signature types, backend selection for resolved
fields, unresolved names) run when the member is declared. Members use the same prepared-item
operations as `urust_fn` and `urust_datatype`, each in the context the next single-item command
would receive, so earlier items are available to later ones and forward references are not
resolved. Type alias items are rejected as chunk members.

Every declaration command is one report transaction. uRust-owned elaboration markup, the native
markup of embedded HOL sources (re-read for markup at release), regenerated
definition entities of the installed artifacts, warnings and successful output are released only
after the command succeeds; native declaration backends run in invisible contexts (target and
background theory) and their results are restated in the returned context, so printed definitions
carry no local hypothesis and function names keep their constant definition entity. A failing
single-item declaration, or the failing member of a chunk, releases its own queued markup with its
error. A chunk additionally buffers the check-time markup of embedded HOL sources, so a failing
chunk leaves only lexical markup for its earlier members at theory level, in locales and in
nested contexts.
Background code-generator `consts` listings of earlier datatype members are the accepted
exception: they are printed through `show_results` of the background theory, which has no
faithful non-persistent control.

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
holes; datatype fields allow implicit pointer backend parameters, while unrelated HOL free type
variables remain rejected. Omitted returns mean `()`, just like explicit `-> ()`.
Non-unit results require an explicit Rust or `τ‹…›` return type. Effect channels infer from
the signature/body, and unused channels generalize.

Function declarations accept independently optional `[state = ‹HOL type›, abort = ‹HOL type›,
input = ‹HOL type›, output = ‹HOL type›]`. These constrain the actual curried HOL constant's
computation channels; input and output include any prompt wrappers. Named variables and sorts
are shared with all Rust signature escapes, locale variables remain rigid, and `_` holes
remain independent. Rust signatures alone supply parameter and returned-value types.
`Parser_Function_Semantic_Type_Tests` checks every channel combination, full declared schemes,
default unit equivalence, callback sharing, contracts, local folding, holes, synonyms,
pointers, locales, positioned rejection and recovery. The former overall `type` option is rejected.

Explicitly typed `self: T` and `mut self: T` use ordinary signature typing and parameter binding.
`Parser_Function_Receiver_Tests` checks complete declaration schemes and kernel equivalence
with `self_value` versions for primitive/mapped types, a HOL reference escape, fields,
direct/method calls, HOL value/expression escapes, closures and name collisions. Boundary
and recovery probes retain rejection of shorthand/untyped receivers, borrowed patterns,
implicit `Self`, unsupported Rust reference types, duplicate names and incompatible bodies.
No `impl` support or receiver-specific lowering is introduced.

Named functions register their Rust declaration name by default. Bare, explicit and scoped
`register_notation` controls use `urust_register_notation`, shared with datatypes. Examples
and ordinary fixtures keep the enabled default. Use `[register_notation = false]` only for
an actual name or registration conflict, such as different locale interpretations sharing
one Rust path. Tests of disabled registration and option precedence deliberately exercise
the opt-out.

Start with `Parser_Function_Tests.thy` to learn `urust_fn`: it opens with explicit, inferred and
anonymous names, then demonstrates parameter forms, calls, options, HOL escapes, mapped signatures,
inferred effects and locales through ordinary checked declarations. The former Rust-function and
function-type-mapping suites are consolidated here.

`Parser_Function_Regression_Tests.thy` imports those examples and checks their equations, types,
registration, ASTs, diagnostics, parser/printer recovery, locale conflicts and editor navigation.
Its ML harnesses stay in this separate regression theory. `Parser_Command_Tests.thy` retains
shared command/API and expression tests, including comparisons with the imported function artifacts.

`Parser_Function_Semantic_Type_Tests.thy` checks complete annotated type schemes, unused callback
relationships through direct and registered method calls, fixed-channel contracts and local proof
expressions, independent holes and call instances, type synonyms, pointer backends, locales,
declaration artifacts and positioned transactional failures.

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

Rust synonyms are ordinary declarations such as `urust_type_alias ‹ type SmallId = u16; ›`.
They are available immediately and inherited by importing the declaring theory; native context and
locale scoping follows the other declaration commands.
Qualified registration uses an optional quoted path whose terminal matches the
item name. Chains and ordinary generic parameters capture their dependencies and inferred sorts.
The same registry resolves aliases in casts, function signatures, and datatype fields. Primitive
cast aliases lower to the identical existing checked term, retaining signedness and mutability.
Identical registrations are idempotent; conflicts report both declaration positions.

Raw pointers share one implicit address/global pair across a complete signature or datatype field
batch. Bodies constrain signature backend variables; pointer datatypes expose implicit HOL
parameters while retaining zero additional Rust generic arguments. Cast syntax uses the shared
positioned type grammar, splits nested generic closers in type contexts, and preserves expression
shifts. Ambiguous cast comparisons require Rust grouping. Repeat lengths accept only literal
`as usize`; aliases do not bypass that policy. Explicit rejection covers the retired command.

Exact registered associated items may use the existing integer primitive tokens as path heads:
`u8`, `u16`, `u32`, `u64`, `usize`, `i32`, and `i64`. Literal-role registration is mandatory for
values, patterns, and repeat lengths; call-role registration is mandatory for calls. The primitive
head does not participate in lexical, HOL-name, unresolved-free, or native-constructor fallback.

`Parser_Unified_Datatype_Tests.thy` covers generic type/const schemes, fixed arrays, const forwarding,
explicit parameter sorts, unused parameters, and source construction/patterns.
`urust_datatype` selects the custom enum by default and the word backend only with an explicit width
and no payload. Explicit word/custom backend names are quoted Isabelle command keywords.
The suite checks boundary discriminants, incompatible backend requests, inferred constraints,
constructor substitutions, conversion registration, and failure recovery. Automatic `PhantomData`
handling is deferred: unmapped fields receive a diagnostic, and explicit singleton mappings retain
ordinary stored fields and constructor/pattern slots. Tests relying on BNF
artifacts select `backend = hol`.
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
- `Parser_Cast_Target_Aliases_Tests.thy`: import and locale scoping, every integral and raw-pointer
  target, exact qualified paths, primitive term equality, repeat integration, conflicts, idempotence,
  positioned diagnostics, navigation markup, and recovery. Its declaration-only fixture is
  `Parser_Cast_Alias_Fixtures.thy`.
- `Parser_Type_Alias_Registry_Tests.thy`: captured templates, normalized generic sorts,
  independent instantiations, pointer backends, collisions and exact registration ranges.
- `Parser_Type_Alias_Syntax_Tests.thy`: shared type/cast grammar, generic closers, source ranges,
  malformed items, recovery and serialized/human printer roundtrips.
- `Parser_Type_Alias_Tests.thy`: ordinary commands, qualified and chained aliases, generic casts,
  signature consumers, namespace conflicts, declaration/dependency navigation and atomic reports.
- `Parser_Pointer_Type_Tests.thy`: record/tuple/enum pointer fields, nested generated types,
  constructors/selectors/lenses, type-changing native updates, signature constraints,
  independent calls and rigid/merged locale contexts.
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
- `Parser_Matcher_Stability_Tests.thy`: fully typed HOL expectations frozen at `39c334c`, with
  kernel `refl` checks for guarded overlaps, differing captures, aliases, nested constructors,
  generated value/range/slice tests, root-suffix reconstruction and all five match consumers.
  Function, abbreviation, anonymous declaration and repeated programmatic clients retain coverage.
  The compiler emits one term and constructs only the needed generated-test or source-guard
  failure destination; structural coverage, typing witnesses and the direct matrix path remain.
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
- `Parser_Chunk_Tests.thy`: the declaration-first `urust` reading entry point: mixed and
  one-item chunks, every item shape and layout transition, outer defaults and annotation overrides,
  every option kind, earlier declarations in later items, locale interpretation and experiment
  confinement, with single-item controls and kernel equalities.
- `Parser_Chunk_Regression_Tests.thy`: chunk ASTs, envelope slices and serialized roundtrips,
  annotation placement (including attribute and command lines, CR LF) and lexer-state recovery,
  outer/annotation option diagnostics, validation before the first declaration, three-level
  precedence and source-order output, equivalence with single-item artifacts and markup (including
  embedded HOL sources and attributes), atomic last-item failures whose earlier members leave only
  parse-only markup, backend/plugin/`simple_word_enum` annotation effects, calls to anonymous and
  unregistered members, the clause boundary of the chunk theory, escaped-symbol positions,
  independent type environments, read-only pretty replay and a moderately sized chunk.
- `Parser_Simple_Word_Enum_Clause_Tests.thy`: `simple_word_enum … urust:` declarations next to the
  single-item parser commands without the chunk theory.
- `Parser_Datatype_Composition_Tests.thy`: complete generic and const mappings through aliases,
  typed receivers and function channels, default direct/method calls, constructor and field
  renames, native backend artifacts and plugins, locale confinement, and read-only combined replay.
  Complete radix literals and discriminants, additive/suffixed const rejection, malformed numeric
  ASTs, and generated-function turbofish boundaries prevent silent argument truncation.
- `Parser_Printer_Tests.thy`: serialized and human-readable expression and datatype printing,
  canonicalization, layout, positions, and malformed-AST diagnostics.
- `Parser_Showcase_Tests.thy`: combined command, chunk, grammar, matching, array-repeat, and iterator
  examples.

Shared declaration-only setup lives in `Parser_Iterator_Fixtures.thy`,
`Parser_Registered_Constructor_Fixtures.thy`, `Parser_Cast_Alias_Fixtures.thy`, and the four
ambiguity fixture theories. Shared ML support and test-only rejection commands live in
`Parser_Test_Utils.thy`. Every tracked `.thy` file in this directory is registered in `ROOT`.
