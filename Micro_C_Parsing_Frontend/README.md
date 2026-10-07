# Micro C Parsing Frontend

This directory contains the C11-to-Core translation frontend (`c_source`, `c_file`) and smoke tests.

## Command options

Supported forms:

- `c_source UNIT ‹C translation unit›`
- `c_source UNIT [abi = lp64-le, compiler = default, addr = 'addr, gv = 'gv,
  abort = c_abort, types = all, functions = all] ‹C translation unit›`
- `c_file UNIT "source.c"`
- `c_file UNIT [manifest = "selection.txt"] "source.c"`
- `c_file UNIT [types = [type_a, type_b], functions = [f, g]] "source.c"`

Rules:

- `UNIT` is mandatory and creates the namespace for generated declarations.
- Option keywords are exact tokens: `abi`, `compiler`, `addr`, `gv`, `abort`,
  `types`, `functions`, and `manifest`.
- Each option may appear at most once.
- `abi` defaults to `lp64-le`.
- `compiler` defaults to `default`; `addr`/`gv` default to `'addr`/`'gv`.
- `types` and `functions` accept `all` or a bracketed name list.
- Inline `types`/`functions` selections and `manifest` are mutually exclusive.
- Repeated commands may extend one unit when configurations match and generated
  declarations are disjoint.
- Struct declarations are auto-translated into `datatype_record` declarations when field types are supported.

Supported ABI profiles:

- `lp64-le` (default)
- `ilp32-le`
- `lp64-be`
- `llp64-le`
- `ilp32-be`

## Isabelle/C 2025-2 declaration-specifier limitation

The pinned Isabelle/C parser accepts the tokens for these valid C forms, but
then raises `unknown declaration format` while running its environment/markup
actions:

- `register unsigned int` in a parameter declaration
- `volatile unsigned int *` in a parameter declaration
- `unsigned long long` in a parameter declaration

Consequently, its public parsing operation does not return the completed
translation-unit AST to the adapter. The corresponding smoke cases use
type-equivalent typedef spellings while retaining the storage-class or
qualifier coverage. The frontend has no copied-parser fallback.

Endianness note:

- Translation-level ABI selection drives C type resolution and generated core terms.
- For byte-level memory modeling, machine-model locales must bind the matching byte prisms.
  - Little-endian: `c_*_byte_prism`
  - Big-endian: `c_*_byte_prism_be` (from `Shallow_Micro_C/C_Byte_Encoding.thy`)
- Each translation unit defines ABI metadata constants in its unit namespace:
  - `UNIT.abi_pointer_bits :: nat`
  - `UNIT.abi_long_bits :: nat`
  - `UNIT.abi_char_is_signed :: bool`
  - `UNIT.abi_big_endian :: bool`
- Use `c_endianness_of_bool` (from `Shallow_Micro_C/C_Byte_Encoding.thy`) with
  `c_*_byte_prism_of` selectors to derive prism choices from `UNIT.abi_big_endian`.

## Manifest format

The manifest is plain text with optional section headers:

```text
functions:
  mlk_barrett_reduce
  - mlk_poly_add

types:
  mlk_poly
  int16_t
```

Rules:

- Valid headers are exactly `functions:` and `types:`.
- Sections are optional.
- Entries must appear under a section header.
- Leading/trailing whitespace is ignored.
- Leading `-` on entries is optional and ignored.
- `#` starts a line comment.

## Two-phase extraction pattern

When function definitions require C-derived types to exist first, run extraction in two passes:

1. Type pass: `c_file UNIT [manifest = "<types-manifest>"] "source.c"`
2. Open locale/context with reference assumptions for those types.
3. Function pass: `c_file UNIT [addr = <addr-ty>, gv = <gv-ty>,
   manifest = "<functions-manifest>"] "source.c"`

Note: for a strict type-only pass, include a non-matching `functions:` filter in the
type manifest (for example a sentinel name) so function constants are not generated.

`C_Translation_Smoke_Options.thy` demonstrates this pattern.
