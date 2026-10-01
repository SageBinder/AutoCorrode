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

for required_session in \
  Micro_C_Isabelle_C_Adapter \
  Micro_C_Parser_Tests \
  Micro_C_Parsing_Frontend \
  Shallow_Micro_C
do
  grep -F -x "$required_session" ROOTS >/dev/null ||
    fail "$required_session is missing from default ROOTS"
  grep -E "^[[:space:]]+\"$required_session\"[[:space:]]*$" ROOT >/dev/null ||
    fail "$required_session is missing from the AutoCorrode umbrella"
done

expected_provider=Micro_C_Isabelle_C_Adapter/adapter.ML
provider_matches=$(
  find . -type f \( -name '*.thy' -o -name '*.ML' \) \
    -not -path './.git/*' \
    -not -path './dependencies/*' \
    -exec grep -l -E 'C_Ast|C11_Ast_Lib|C_Module|get_CTranslUnit' {} + |
    sed 's|^\./||' |
    sort
)
[ "$provider_matches" = "$expected_provider" ] ||
  fail "Isabelle/C parser or AST APIs escaped the adapter implementation:
$provider_matches"

mutable_state_matches=$(
  find Micro_C_Isabelle_C_Adapter Micro_C_Parser_Tests \
    Micro_C_Parsing_Frontend Shallow_Micro_C \
    -type f \( -name '*.thy' -o -name '*.ML' \) \
    -exec grep -l -E 'Unsynchronized\.ref|Synchronized\.(var|value)|Mutex\.' {} + ||
    true
)
[ -z "$mutable_state_matches" ] ||
  fail "C prototype introduced process-global mutable translation state:
$mutable_state_matches"

check_term_count=$(
  grep -R -h -o 'Syntax\.check_term' Micro_C_Parsing_Frontend |
    wc -l |
    tr -d '[:space:]'
)
[ "$check_term_count" = 1 ] ||
  fail "expected exactly one final Syntax.check_term, found $check_term_count"

echo "Isabelle/C APIs and mutable translation state are confined to the adapter boundary"
