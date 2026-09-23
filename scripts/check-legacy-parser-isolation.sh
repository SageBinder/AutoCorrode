#!/usr/bin/env bash

set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

failed=0

report_failure() {
  printf '%s\n' "$1" >&2
  failed=1
}

is_isolated_test_path() {
  case "$1" in
    ./Micro_Rust_Parsing_Legacy_Frontend/*|\
    ./Micro_Rust_Parser_Tests/*|\
    ./.worktrees/*|\
    ./dependencies/*|\
    ./.git/*)
      return 0
      ;;
    *)
      return 1
      ;;
  esac
}

while IFS= read -r -d '' theory; do
  if is_isolated_test_path "$theory"; then
    continue
  fi

  forbidden_imports="$(
    awk '
      /^[[:space:]]*theory[[:space:]]/ { in_header = 1 }
      in_header && /^[[:space:]]*begin([[:space:]]|$)/ { exit }
      in_header &&
        /Micro_Rust_Parsing_Legacy_Frontend|Micro_Rust_Parser_Conformance_Tests|Micro_Rust_Shallow_Embedding|(^|[^[:alnum:]_])Core_Syntax([^[:alnum:]_]|$)|(^|[^[:alnum:]_])Basic_Case_Expression([^[:alnum:]_]|$)/ {
          print FILENAME ":" FNR ":" $0
        }
    ' "$theory"
  )"
  if [[ -n "$forbidden_imports" ]]; then
    report_failure "Production theory imports the legacy parser frontend:"
    printf '%s\n' "$forbidden_imports" >&2
  fi

  conformance_enables="$(
    grep -nHE 'urust_conformance[[:space:]]*=[[:space:]]*true' "$theory" || true
  )"
  if [[ -n "$conformance_enables" ]]; then
    report_failure "Production theory enables legacy parser conformance:"
    printf '%s\n' "$conformance_enables" >&2
  fi
done < <(find . -type f -name '*.thy' -print0)

while IFS= read -r -d '' root_file; do
  if is_isolated_test_path "$root_file"; then
    continue
  fi

  legacy_session="$(
    grep -nE \
      'Micro_Rust_Parsing_Legacy_Frontend|Micro_Rust_Parser_Conformance_Tests' \
      "$root_file" || true
  )"
  if [[ -n "$legacy_session" ]]; then
    report_failure "Production session depends on the legacy parser frontend:"
    printf '%s\n' "$root_file:$legacy_session" >&2
  fi
done < <(find . -type f -name ROOT -print0)

neutral_registry=Shallow_Micro_Rust_Base/Micro_Rust_Notations.thy
grammar_emission="$(
  grep -nE \
    'emit_bespoke_syntax|is_grammatical_name|_urust_identifier_bespoke_|Local_Theory\.syntax_cmd|Sign\.parse_ast_translation|Mixfix\.mixfix' \
    "$neutral_registry" || true
)"
if [[ -n "$grammar_emission" ]]; then
  report_failure "The syntax-neutral notation registry contains legacy grammar emission:"
  printf '%s\n' "$grammar_emission" >&2
fi

if (( failed != 0 )); then
  exit 1
fi

printf '%s\n' "Legacy parser isolation audit passed."
