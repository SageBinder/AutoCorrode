# µRust parser integration status

This session is the executable specification for the production µRust parser. It keeps shared-source
conformance against the legacy frontend, parser-only improvements, negative fidelity boundaries,
term-shape audits, markup/recovery checks, and combined showoff examples in one registered session.

## Command surface

`urust_expr` and `urust_fn` retain the parenthesized declaration-argument syntax:

```isabelle
urust_expr [OPTIONS] NAME [:: TYPE] [(ARG, ...)] \<open> body \<close>
urust_fn [OPTIONS] NAME :: TYPE [(PARAMETER, ...)] \<open> body \<close>
```

The list is optional, may be empty, and accepts one trailing comma. Declaration arguments are
allocated as typed lexical locals before body elaboration. They therefore shadow existing
unqualified HOL constants and direct-call registrations in value and direct-call positions.
Qualified calls and method names retain registration-first resolution. `Parser_Tests_Misc.thy`
contains the exact `zip` collision: a parameter named `zip` shadows HOL `List.zip`, the conformance
theorem closes by reflexivity, and the generated definition is structurally checked not to contain
`List.zip`.

Named definition-mode declarations accept standard Isabelle attributes through `attrs = [...]`;
the attributes apply only to the generated `_def` theorem. An exact terminal `_` in an `urust_fn`
type is completed to a fresh five-parameter `function_body` before ordinary checked elaboration.

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

Name and constructor metadata operations remain in `URust_Resolution`. `URust_Patterns` owns one
typed recursive decision compiler for binding, structural selection, guards, source-order fallback,
coverage, and compatibility term shape. The compiler does not maintain parser-private constructor
families or separate guarded/unguarded pattern engines.

Constructor resolution follows one chain:

1. ordinary datatype/codatatype metadata from `Ctr_Sugar`;
2. native `Case_Translation` metadata for an exact registered `NLiteral` backend absent from
   `Ctr_Sugar`;
3. authentic `Code.is_constr`/`Ctr_Sugar` lookup only for unregistered names.

Registered literals with native case metadata are constructors. Registered literals without it are
values and need no downstream family registration. Binder-free, guard-free value/wildcard arms may
use switch/equality lowering; authentic constructors, bindings, and other structural patterns use
case lowering. A nested exact registered nullary constructor without payload binding may become an
equality guard while its enclosing authentic constructor remains case-lowered. Bare basename
ambiguity reports every candidate and is never resolved from the expected result type.

The shared shallow iterator `zip` combines iterator thunk lists with HOL `List.zip`, truncates to the
shorter input, and calls each left thunk before its paired right thunk exactly once. The registered
method uses ordinary receiver-prepending call resolution and returns the established µRust pair
`(left, right, TNil)`.

## Rust-fidelity boundaries

Retained compatibility extensions include complete µRust bodies in guards and statement bodies in
groups, macros, and struct fields. The underscore-before-integer-suffix spelling also remains
accepted. The parser supports binary, octal, decimal, and hexadecimal integers with internal or
trailing underscores and `u8`, `u16`, `u32`, `u64`, and `usize` suffixes.

The following remain deliberately unsupported: one-element tuples, general postfix invocation, open
ranges, array repeats, unary numeric negation, `/=`, leading `::`, full Rust generics, universal macro
trailing commas, signed integers, `u128`, floating/character/scientific literals, and apostrophised
Rust identifiers. Focused negative rows preserve these boundaries.

The experimental `Parser_Term_Hook` remains opt-in. Ordinary command and roll-up theories do not
import it; only the two focused hook test theories in this session do.

## Focused regression theories

- `Parser_Tests_Grammar_Literals.thy`: precedence adjacency, unary/cast/postfix behavior, direct and
  wrapped block-like operands, statement/arm separators, recursive no-struct heads, closures,
  structs, integer lexing, generated grammar, markup, and recovery.
- `Parser_Test_Constructor_Matching.thy`: `Ctr_Sugar`, custom enum and simple-word-enum native case
  metadata, metadata-free values, ambiguity, nested registered-nullary normalization, recursive
  structural matching, guards, coverage, source order, single evaluation, term shape, markup, and
  recovery.
- `Parser_Test_Iterator_Zip.thy`: empty and unequal inputs, truncation, effect order, single
  evaluation, direct/method/chained resolution, arity preflight, notation registration, and
  separation from pure HOL `List.zip`.
- `Parser_Test_Showoff.thy`: combined command, grammar, matching, and iterator examples.

Every `.thy` file in this directory is registered in `ROOT`.

## Migration-report disposition

| Item | Disposition |
|---|---|
| H-D1 | Fixed with parenthesized lexical declaration arguments; chosen names shadow unqualified HOL/direct-call names. |
| H-D2 | Kept Rust-correct postfix-before-dereference behavior. |
| H-D3 postfix | Kept. |
| H-D3 cast | Fixed with unary-before-cast precedence. |
| H-D4 | Fixed through exact registered `Case_Translation` recovery. |
| H-D5 | Qualification remains required for ambiguous basenames. |
| H-D6 families | Fixed without downstream or parser-private family registration. |
| H-D6 nested pattern | Fixed through narrow nested-nullary equality normalization inside structural case lowering. |
| H-D7 | Match-arm semicolons remain rejected. |
| H-D8 | Fixed by centralized integer candidate parsing and validation. |
| H-D9 | Apostrophised Rust identifiers remain rejected. |
| H-D10 | Fixed with exact terminal-`_` `function_body` inference. |
| H-D11 | Fixed by the shared shallow iterator `zip`. |
| H-D12 | Import semantics/public bridge documented; no parser change. |
| P10/P14 | Use argument-taking abbreviations and declaration attributes. |
| P5/P13 | Out of scope; no `ic2` change. |
| Other P-items | Migration tooling/environment issues; no AutoCorrode language feature added. |
