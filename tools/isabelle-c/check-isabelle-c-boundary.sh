#!/bin/sh

set -eu

fail()
{
  echo "check-isabelle-c-boundary: $*" >&2
  exit 1
}

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
cd "$repo_root"

expected=Micro_C_Isabelle_C_Adapter/Micro_C_Isabelle_C_Adapter.thy
theory_matches=$(
  find . -type f -name '*.thy' \
    -not -path './.git/*' \
    -not -path './dependencies/*' \
    -exec grep -l -E '"Isabelle_C\.[^"]+"' {} + |
    sed 's|^\./||' |
    sort
)
[ "$theory_matches" = "$expected" ] ||
  fail "Isabelle/C theory imports escaped the adapter boundary:
$theory_matches"

expected_root=Micro_C_Isabelle_C_Adapter/ROOT
root_matches=$(
  find . -type f -name ROOT \
    -not -path './.git/*' \
    -not -path './dependencies/*' \
    -exec grep -l -E '^[[:space:]]+"?Isabelle_C"?[[:space:]]*$' {} + |
    sed 's|^\./||' |
    sort
)
[ "$root_matches" = "$expected_root" ] ||
  fail "Isabelle_C session dependencies escaped the adapter boundary:
$root_matches"

echo "Isabelle/C imports are confined to Micro_C_Isabelle_C_Adapter"
