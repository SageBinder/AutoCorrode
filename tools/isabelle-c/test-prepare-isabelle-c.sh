#!/bin/sh

set -eu

PATCHED_PARSER_BLOB=49aa9fb8c01c064f6d4de428846e6b7b08821c8a
PARSER_PATH=Isabelle_C/C11-FrontEnd/src/C_Parser_Language.thy

fail()
{
  echo "test-prepare-isabelle-c: $*" >&2
  exit 1
}

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
prepare="$script_dir/prepare-isabelle-c.sh"

[ -n "${AFP_SOURCE_BASE:-}" ] ||
  fail "AFP_SOURCE_BASE must name the thys directory of the pinned AFP checkout"

scratch=$(mktemp -d "${TMPDIR:-/tmp}/autocorrode-isabelle-c-test.XXXXXX")
cleanup()
{
  rm -rf "$scratch"
}
trap cleanup EXIT HUP INT TERM

component_base="$scratch/components"
AFP_SOURCE_BASE="$AFP_SOURCE_BASE" \
  ISABELLE_C_COMPONENT_BASE="$component_base" \
  "$prepare"
first_blob=$(git hash-object "$component_base/$PARSER_PATH")
[ "$first_blob" = "$PATCHED_PARSER_BLOB" ] ||
  fail "first preparation produced unexpected parser blob $first_blob"

AFP_SOURCE_BASE="$AFP_SOURCE_BASE" \
  ISABELLE_C_COMPONENT_BASE="$component_base" \
  "$prepare"
second_blob=$(git hash-object "$component_base/$PARSER_PATH")
[ "$second_blob" = "$first_blob" ] ||
  fail "second preparation changed the patched parser"

unexpected_checkout="$scratch/unexpected-afp"
mkdir -p "$unexpected_checkout/thys"
cp -R "$AFP_SOURCE_BASE/Isabelle_C" "$unexpected_checkout/thys/Isabelle_C"
git -C "$unexpected_checkout" init -q
git -C "$unexpected_checkout" add thys/Isabelle_C
git -C "$unexpected_checkout" \
  -c user.name=AutoCorrode \
  -c user.email=autocorrode@example.invalid \
  commit -q -m "unexpected AFP source"

if AFP_SOURCE_BASE="$unexpected_checkout/thys" \
     ISABELLE_C_COMPONENT_BASE="$scratch/rejected-components" \
     "$prepare" >"$scratch/rejection.out" 2>&1
then
  fail "preparation accepted an unexpected AFP commit"
fi

echo "Isabelle/C preparation is exact, idempotent, and version-guarded"
