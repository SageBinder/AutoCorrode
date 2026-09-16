![CI](https://github.com/awslabs/AutoCorrode/actions/workflows/ci.yml/badge.svg)
![Docs](https://github.com/awslabs/AutoCorrode/actions/workflows/cd.yml/badge.svg)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# AutoCorrode

AutoCorrode provides infrastructure for reasoning about imperative programs in Isabelle/HOL. It supports classical and separation logic and includes configurable and scalable custom automation, written in Standard ML. The core of AutoCorrode is language-agnostic, with a frontend and examples for the Rust-like language µRust.

An experimental (unvalidated) C11 frontend formerly included in this repository is available in a temporary hard-fork at [github.com/DominicPM/AutoCorrode](https://github.com/DominicPM/AutoCorrode).

AutoCorrode gets its name as the little rusty brother of the independent C verification framework [AutoCorres](https://github.com/seL4/l4v/tree/master/tools/autocorres) for Isabelle/HOL.

## Showcase

The [Showcase.thy](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Showcase.html) file provides a small tour of AutoCorrode's basic concepts and features. It defines several (simple) functions in µRust, defines contracts for them, then uses the provided automation to verify that the functions satisfy their contracts.

## I/Q

[I/Q](iq) -- short for Isabelle/Q -- is an experimental Isabelle/jEdit plugin exposing proof editing/exploration capabilities as an MCP server. Its purpose is to enable MCP-capable AI agents such as [Amazon Q](https://aws.amazon.com/q/) to autonomously
or collaboratively conduct interactive theorem proving using Isabelle. See [iq](iq) for more information.

## I/P

[I/P](ip) -- short for Isabelle/Proxy -- runs the Isabelle ML prover on a remote machine while keeping Isabelle/jEdit local. It requires no Isabelle source changes and includes a jEdit plugin for remote status monitoring. See [ip](ip) for more information.

## I/R

[I/R](ir) -- short for Isabelle/REPL -- provides interactive theory exploration outside of jEdit, from the command line or programmatically via TCP and MCP. See [ir](ir) for more information.

## IC2

[IC2](ic2) manages headless, persistent Isabelle sessions from the command line -- similar to `isabelle server` and `isabelle client`, but integrated with [I/R](ir) and [I/Q](iq). A resident session serves repeated `.thy` checks and diagnostic queries, and can bring up I/R against the same session, optionally over MCP, so an agent can drive Isar proofs without a separate Isabelle/jEdit + I/Q. See [ic2](ic2) for more information.

## µRust parser timing

[Micro_Rust_Parser_Timing](Micro_Rust_Parser_Timing) provides
`isabelle urust_timing SESSION`. Timed `urust_expr` and `urust_fn` declarations store structured,
versioned records in the session's final PIDE snapshots; the tool aggregates an already-built session
without rebuilding it or checking source freshness. It reports session and per-theory cumulative
declaration latency, optional hotspots, and complete atomic JSON output.

## Isabelle Assistant

[Isabelle Assistant](isabelle-assistant) is an LLM-powered proof assistant for Isabelle/jEdit, built on [AWS Bedrock](https://aws.amazon.com/bedrock/). It provides autonomous proof search, interactive chat with LaTeX rendering, proof suggestions, code explanation, refactoring, and more — all integrated into the Isabelle/jEdit IDE. When combined with [I/Q](iq), generated proofs are automatically verified against Isabelle before display. See [isabelle-assistant](isabelle-assistant) for more information.

## Browsing the source

An HTML rendering of the AutoCorrode source code is available [here](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/AutoCorrode.html).

## Setup

AutoCorrode requires Isabelle2025-2, which can be downloaded [here](https://isabelle.in.tum.de/website-Isabelle2025-2/). Set `ISABELLE_HOME` to the directory containing the `isabelle` binary.

AutoCorrode also requires the [WordLib](https://www.isa-afp.org/entries/Word_Lib.html) AFP entry. Set `AFP_COMPONENT_BASE` to the directory contaning the `Word_Lib` directory. By default, AutoCorrode expects it to be located in [dependencies/afp](dependencies/afp).

## Usage

You can interactively explore AutoCorrode using `make jedit`, which opens the AutoCorrode source in the Isabelle/jEdit GUI.

To non-interactively check all material in AutoCorrode, run `make build`, which starts a batch-build in Isabelle.

## Citing AutoCorrode

If you want to cite AutoCorrode, consider using the following BibTeX entry:

```
@misc{AutoCorrode,
   author = "Becker, Hanno and Chong, Nathan and Dockins, Robert and Grundy, Jim and Hu, Jason Z. S. and Mulder, Ike and Mulligan, Dominic P. and Mure, Paul and Paulson, Lawrence C. and Slind, Konrad",
   title = "{AutoCorrode} software verification framework for {Isabelle/HOL}",
   year = "2025",
   howpublished = "\url{https://github.com/awslabs/autocorrode}"
}
```

## Sessions

The following gives a brief overview over the Isabelle sessions contained in AutoCorrode.

### [Shallow_Micro_Rust_Base and Shallow_Micro_Rust](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Micro_Rust.Shallow_Micro_Rust.html)

The base session defines the ["µRust monad"](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Micro_Rust_Base.Core_Expression.html#Core_Expression.expression|type), its core semantics, and the shallow embedding required by the parser. The full session adds parser-backed theories, lemmas, and automation. Despite its name and primary purpose as the target of the shallow embedding of µRust into Isabelle/HOL, the monad is quite generic and likely suitable for the modelling of other imperative languages as well. Concretely, the µRust monad is an inductive monad with support for exceptions, functions, and yields/prompts (similar to interaction trees).

The shallow iterator model includes a shared `zip` method. It combines thunk
lists with HOL `List.zip`, truncates to the shorter iterator, and evaluates each
paired element left-to-right before returning the µRust pair `(left, right,
TNil)`.

### [Shallow_Separation_Logic](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Separation_Logic.Shallow_Separation_Logic.html)

This session defines basic notions of separation logic. It also defines [Hoare triples](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Separation_Logic.Triple.html) for the µRust Monad and derives a [weakest precondition calculus](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Separation_Logic.Weakest_Precondition.html). Automatic reasoning within that calculus is the primary purpose of [Crush](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Crush.Crush.html).

### [Separation_Lenses](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Separation_Lenses.Separation_Lenses.html)

Separation lenses facilitate the extension of locale interpretations from smaller to larger separation algebras. They allow for the construction of separation algebras implementing a series of interfaces by constructing individual interface interpretations on minimal separation algebras first, and 'glueing' them together by means of the separation lens formalism. Without separation lenses, a large amount of boilerplate would be required.

Concretely, a separation lens is an [axiomatization](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Separation_Lenses.SLens.html#SLens.is_valid_slens|const) of the projection of product separation algebra onto one of its factors. The axioms are strong enough to enable the [extension](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Separation_Lenses.SLens_Pullback.html) of µRust programs and their separation logic specifications and proofs along separation lenses.

### [Lenses_And_Other_Optics](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Lenses_And_Other_Optics.Lenses_And_Other_Optics.html)

This session defines and elaborates the concepts of [lenses](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Lenses_And_Other_Optics.Lens.html), [prisms](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Lenses_And_Other_Optics.Prism.html) and [foci](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Lenses_And_Other_Optics.Focus.html). Foci are used in AutoCorrode as an axiomatization of the relation between the 'raw' values in a monomorphic store, and the interpretations of those raw values in concrete types.

In a nutshell, a lens is a quotient type (e.g. a record projection), a prism is a subtype (e.g. a branch of an inductive type), and a focus is a subquotient --- the concept emerging from lenses and prisms when requiring compositionality.

Foci are mainly used in AutoCorrode's model of [references](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Shallow_Micro_Rust_Base.Global_Store.html#Global_Store.ref|type): The value behind a raw/untyped reference is a 'raw' value in some fixed monomorphic store, and typing a reference amounts to providing a focus from that raw 'global value type' to the desired 'local' type. This generality allows for representation-agnostic reasoning about references: References can either be implemented as being backed by an abstract heap, where the global value type is the disjoint union of all local value types; or as being backed by a byte-level memory, where the global value type is the type of byte lists, and foci capture pairs of decoding/encoding functions between byte sequences and concrete types. See [Micro_Rust_Examples](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Micro_Rust_Examples.html) for examples.

### [Crush](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Crush.Crush.html)

Crush is a family of highly customizable and scalable tactics for reasoning in separation logic. See [Micro_Rust_Examples/Crush_Examples.thy](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Crush_Examples.html) for an introduction.

### [Autogen](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Autogen.Autogen.html)

Autogen facilitates pure reasoning about functions on records: Users can annotate functions with their footprint -- the set of record fields they depend on -- and have footprint-based commutativity relations derived automatically. See [Autogen/AutoLocality_Test0.thy](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Autogen.AutoLocality_Test0.html) for an example.

### [Byte_Level_Encoding](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Byte_Level_Encoding.Byte_Level_Encoding.html)

This session provides encoding/decoding functions for basic types to/from byte lists, expressed in the formalism of Foci/Optics.

### [Micro_Rust_Examples](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Examples.Micro_Rust_Examples.html)

This session contains documentation and examples illustrating how to use AutoCorrode for reasoning about the Rust-like "µRust" language.

### [Micro_Rust_Interfaces[_Core]](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Interfaces_Core.Micro_Rust_Interfaces_Core.html)

This session define locales for modelling the verification context. For example, [References.thy](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Interfaces_Core.References.html) defines the `Reference` locale which provides axioms for reasoning about references and mutable local variables in µRust. It also defines "transfer locales" which use separation lenses (see Optics, above) to extend interpretations of the interface locales to larger separation algebras.

### Micro_Rust_Parser_Impl and Micro_Rust_Parser_Tests

The implementation session provides the production `urust_expr`, `urust_fn`, and
`urust_datatype` commands:

```isabelle
urust_expr [OPTIONS] NAME [:: TYPE] [(ARG, ...)] \<open> body \<close>
urust_fn [OPTIONS] NAME :: TYPE [(PARAMETER, ...)] \<open> body \<close>
urust_datatype [OPTIONS] [HOL_NAME] \<open> struct-or-enum \<close>
```

`urust_datatype` accepts one complete Rust-shaped struct or enum item. The HOL type name is
optional and otherwise inferred with acronym-aware ASCII snake case (`HTTPServer` becomes
`http_server`). Primitive field types `u8`, `u16`, `u32`, `u64`, `usize`, `i32`, `i64`, `bool`,
and `()` are built in; arbitrary checked HOL types use `τ‹TYPE›`, with `τ` carrying the same literal
markup as the `ε` expression-antiquotation prefix. Named structs generate a `datatype_record`,
field lenses, and exact Rust field aliases. Unit and tuple structs generate
`make_NAME`; enum variants are registered under exact paths such as `Message::Data`. Generated
constructors use those exact Rust identities in values, calls, patterns, and struct expressions;
they are not rediscovered through HOL basenames.

Datatype verbosity is cumulative. Level 0 is quiet, level 1 reports the completed public type,
constructors, selectors, lenses, and installed Rust mappings, and level 2 additionally prints the
normalized generated HOL declaration and public selector/lens definitions. With `pretty = true`,
levels 1 and 2 insert the normalized uRust declaration immediately after the artifact manifest.
Output is emitted only after the whole declaration and item-scope registration succeed.

It also exposes the position-independent `URust_Printer` ML API. Serialized mode preserves explicit
AST groups and is used by the common Boolean `pp_test` declaration option (or scoped
`urust_pp_test`) for a silent parse-print-parse token comparison before lowering or datatype
generation. The sealed API provides parallel token, pretty, and string operations for expression
and datatype ASTs. Human mode removes redundant expression grouping and is available in
verbosity-controlled command output through the common Boolean `pretty` option (or scoped
`urust_pretty`). At verbosity 0, `pretty` has no output to affect and produces a warning.
Conformance theorems retain ordinary HOL rendering because their right-hand side comes from the
legacy frontend. For expression output, the formatted body appears inside a symbolic `µ‹…›`
wrapper that is unrelated to source quotation syntax, and comes from a pure source-mapped document
whose public token projection remains position-free.
Command arguments appear as uRust closure formals on the pretty right-hand side by default;
`application_def` instead displays them as applications on the left-hand side.
The symbolic opening follows the equation marker on the same line; right-hand closure formals and
the body occupy successively indented lines.
In human mode, nonempty code blocks for control flow, matches, closures, bindings, and assignments
always place their code on indented lines, independently of the PIDE margin; opening braces remain
on the construct line and `} else {` remains together. Serialized mode retains compact canonical
blocks where possible. Multiline brace bodies use two-space nesting from the construct's line
indentation rather than aligning beneath the opening brace.
`Parser_Impl_Printer_Output` reparses that canonical generated source only through the new frontend
and transfers every resulting lexical, semantic, entity, typing, and embedded-HOL PIDE report to the
document's matching lexeme span before final line layout. The InfoView therefore inherits parser
markup without the printer reconstructing binder or identifier roles. Datatype replay validates
the synthetic declaration against the already generated item-scope identities and reports generated
HOL entities before final links to the original uRust type, constructor, and field declarations. It
does not regenerate declarations, mutate item scope, or forward probe reports to the live document.
The parser test session enables the
scoped roundtrip check across its command-bearing theories; `Parser_Test_Printer.thy` separately
demonstrates and audits human-readable formatting.

Existing integral and raw-pointer cast targets may also receive context-local source aliases:

```isabelle
bundle module_cast_aliases begin
  urust_cast_alias "WordId" = "u16"
  urust_cast_alias "ConstBytePtr" = "*const u8"
end

context includes module_cast_aliases
begin
  urust_expr example ‹ value as WordId ›
end
```

Defining or importing a bundle does not activate its aliases. Bundle inclusion is the explicit
correspondence to the intended Rust file or module scope; aliases disappear when the confined
context ends. Isabelle named contexts and locales use the native `opening` form, for example
`context some_locale opening module_cast_aliases begin`. Alias paths may be qualified but may not
contain generic arguments, and aliases always resolve directly to one primitive cast target rather
than to another alias.

The parenthesized argument list is optional, accepts a trailing comma, and uses Isabelle liberal
names. Minor keywords such as `for` may be unquoted; major command keywords delimit outer command
spans and therefore need string quoting, for example `("lemma")`. A chosen argument name denotes
that lexical argument in value positions and as an unqualified direct-call head, even if a HOL
constant or call registration has the same spelling. Every multi-segment path requires an exact
role-appropriate `micro_rust_notation`: values and places use `(literal)`, while calls, struct
expressions, and registered macros use `(call)` (with `!` included in a macro key). Method names
remain single-segment and retain their normal registration lookup. `urust_fn` also accepts an exact
terminal `_` in its declared type and
infers a fresh five-parameter `function_body`; internal placeholders and declared argument types
remain checked normally.

Named definition-mode declarations accept `attrs = [ATTRIBUTE, ...]`, including `attrs = []`.
These standard Isabelle attributes apply only to the generated `NAME_def` theorem; anonymous
declarations and `urust_expr [abbrev]` reject them. Argument-taking `urust_expr [abbrev]` declarations
are the supported HOL helper mechanism. At HOL use sites, write `(helper args)` when surrounding
syntax would otherwise group the helper application incorrectly.

Production theories use these commands for complete definitions and named abbreviations, with
conformance checking enabled against the legacy frontend. The test session contains conformance
corpora, regression tests, parser experiments, and legacy shallow-embedding tests. Its
[README](Micro_Rust_Parser_Tests/README.md) records the integrated parser architecture,
Rust-fidelity boundaries, focused regression layout, and migration-report dispositions.

The production expression parser uses explicit Rust-aligned precedence tiers. Prefix operators bind
before casts, supported postfix operations bind before prefixes, and block-like expressions remain
ordinary primary operands. Their separate classification controls only omitted statement semicolons
and non-final match-arm commas. Control heads recursively exclude unparenthesized struct expressions,
while explicit delimiters restore unrestricted parsing. Integer literals support binary, octal,
decimal, and hexadecimal bases, internal or trailing underscores, and the `u8`, `u16`, `u32`,
`u64`, and `usize` suffixes. Ordinary source also accepts nested Rust `/* ... */` comments as
layout, with complete outer-span editor markup and no grammar or AST representation.

Array repeats support ordinary `[value; length]` and repeat-local
`[const { value }; length]`. Lengths admit integer literals, direct Isabelle fixed parameters,
exact registered literal paths, genuine unqualified global constants, parentheses, `+ - * / %`,
and `as usize`; a registered backend may itself depend on the surrounding proof context. Qualified
length paths require exact `(literal)` registration. Unsuffixed and `usize` literals are accepted
directly, while other word widths require the cast. Ordinary operands run exactly once, including at
length zero. Inline-const bodies run once per element and not at all at length zero.

`Parser_Tests_Improvements.thy` provides a consolidated positive baseline for array repeats, nested
block comments, and scoped cast-target aliases. Its separate legacy matcher-bug section demonstrates
nested registered-nullary preservation, guarded-or fallthrough, fallback-binder hygiene, and nested
alias preservation.

The existing integer primitive tokens may head exact registered associated-item paths such as
`u64::MAX`, `u8::MAX as u64`, and `u64::from(x)`. Literal positions, patterns, repeat lengths, and
calls select their own registration roles; primitive-headed paths never fall back to lexical names,
HOL names, unresolved frees, or native constructors. Bare primitive values and primitive-headed
places, struct/macro heads, field labels, and method names remain invalid.

Constructor resolution uses Isabelle's datatype/codatatype metadata first and native case metadata
for exact registered literal backends that are not represented by `Ctr_Sugar`. Registered literals
without native case metadata remain values. Automatic matching selects equality/switch lowering
only for binder-free, guard-free value/wildcard arms; authentic constructors and binding patterns
retain case semantics at every nesting depth, including registered nullary constructors. Resolution
provenance affects exact lookup and markup but never changes constructor lowering. Ambiguous
basenames remain errors, and the parser keeps no private constructor-family registry.
Qualified constructor and struct patterns must have an exact `(literal)` registration; their
constructor metadata is recovered from the registered backend rather than by translating source
`::` separators into Isabelle long names. Unqualified HOL constants, fixed parameters, and native
constructor basenames remain unchanged.

The grammar retains compatibility extensions used by existing µRust sources, including complete
guard bodies and statement bodies in groups, macros, and struct fields. Apostrophised identifiers
also remain accepted during production migration. Dereference otherwise follows Rust's uniform
postfix-before-prefix precedence: `*base[index]` means `*(base[index])`, while the former
dereference-before-index meaning requires `(*base)[index]`. A direct return match arm requires a
comma; a semicolon is accepted as an ordinary return statement only inside braces. Deliberately
deferred Rust surface includes general postfix calls, one-element tuples, open ranges, unary numeric
negation, `/=`, leading `::`, full Rust generics, universal macro trailing commas, and additional
numeric families.

The parser implementation depends only on `Shallow_Micro_Rust_Base` and `Isabelle_Lex-Yacc`.
Full `Shallow_Micro_Rust` adds the parser bridge, while the main `AutoCorrode` session includes both
the implementation and test sessions.

Timed declarations also emit hidden schema-versioned PIDE records. The independent
[Micro_Rust_Parser_Timing](Micro_Rust_Parser_Timing) component reads those records from the final
snapshots in a completed session database and exposes them through `isabelle urust_timing`.

### [Micro_Rust_Parsing_Legacy_Frontend](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Parsing_Legacy_Frontend.Micro_Rust_Parsing_Legacy_Frontend.html)

The legacy inner-syntax frontend remains as the permanent conformance oracle for the production
parser. It defines the custom µRust syntax category and shallow-embedding bracket used by
conformance checks; production µRust declarations and expression sites use the parser commands.

### [Micro_Rust_Runtime](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Runtime.Micro_Rust_Runtime.html)

This session provides concrete interpretations for the locales defined in [Micro_Rust_Interfaces](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Interfaces.Micro_Rust_Interfaces.html) and [Micro_Rust_Interfaces_Core](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Interfaces_Core.Micro_Rust_Interfaces_Core.html), including abstract and byte-level implementations of the  `Reference` locale.

### [Micro_Rust_Std_Lib](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Micro_Rust_Std_Lib.Micro_Rust_Std_Lib.html)

Specifications and proofs for common µRust operations.

### [Data_Structures](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Data_Structures.Data_Structures.html)

This session contains various efficient data structures.

### [Misc](https://awslabs.github.io/AutoCorrode/Unsorted/AutoCorrode/Misc.Misc.html)

A collection of miscellaneous lemmas about lists, arrays, sets, vectors, and words.
