#!/bin/sh

set -eu

AFP_COMMIT=42452c8a5661996af380ce4ee01c253a3ec8fa52
SOURCE_PARSER_BLOB=5028fb2790c3321a4e81f457761c3c6085c42c75
PATCHED_PARSER_BLOB=49aa9fb8c01c064f6d4de428846e6b7b08821c8a
PARSER_PATH=C11-FrontEnd/src/C_Parser_Language.thy

fail()
{
  echo "prepare-isabelle-c: $*" >&2
  exit 1
}

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/../.." && pwd)
patch_file="$script_dir/isabelle-c-multi-specifier-parameters.patch"

[ -n "${AFP_SOURCE_BASE:-}" ] ||
  fail "AFP_SOURCE_BASE must name the thys directory of the pinned AFP checkout"

source_component="$AFP_SOURCE_BASE/Isabelle_C"
[ -d "$source_component" ] ||
  fail "missing Isabelle/C source component: $source_component"
source_component=$(CDPATH= cd -- "$source_component" && pwd)

source_git_root=$(git -C "$source_component" rev-parse --show-toplevel 2>/dev/null) ||
  fail "AFP_SOURCE_BASE must belong to a Git checkout at commit $AFP_COMMIT"
source_commit=$(git -C "$source_git_root" rev-parse HEAD)
[ "$source_commit" = "$AFP_COMMIT" ] ||
  fail "unexpected AFP commit $source_commit (expected $AFP_COMMIT)"

source_prefix=$(git -C "$source_component" rev-parse --show-prefix)
[ -z "$(git -C "$source_git_root" status --porcelain --untracked-files=no -- "$source_prefix")" ] ||
  fail "the source Isabelle/C component has tracked modifications"

source_parser="$source_component/$PARSER_PATH"
[ -f "$source_parser" ] ||
  fail "missing pinned parser source: $source_parser"
source_blob=$(git hash-object "$source_parser")
[ "$source_blob" = "$SOURCE_PARSER_BLOB" ] ||
  fail "unexpected parser source blob $source_blob (expected $SOURCE_PARSER_BLOB)"

component_base=${ISABELLE_C_COMPONENT_BASE:-"$repo_root/dependencies/afp"}
mkdir -p "$component_base"
component_base=$(CDPATH= cd -- "$component_base" && pwd)
destination="$component_base/Isabelle_C"
marker="$destination/.autocorrode-source-pin"

if [ -e "$destination" ]; then
  [ -d "$destination" ] ||
    fail "destination exists but is not a directory: $destination"
  [ -f "$marker" ] ||
    fail "existing destination was not prepared by this script: $destination"
  [ "$(sed -n '1p' "$marker")" = "AFP_COMMIT=$AFP_COMMIT" ] ||
    fail "existing destination records a different AFP commit"
  [ "$(sed -n '2p' "$marker")" = "PATCHED_PARSER_BLOB=$PATCHED_PARSER_BLOB" ] ||
    fail "existing destination records a different compatibility patch"
  destination_blob=$(git hash-object "$destination/$PARSER_PATH")
  [ "$destination_blob" = "$PATCHED_PARSER_BLOB" ] ||
    fail "existing patched parser has unexpected blob $destination_blob"
  echo "Isabelle/C already prepared at $destination"
  exit 0
fi

stage_dir=$(mktemp -d "$component_base/.isabelle-c-prepare.XXXXXX")
cleanup()
{
  rm -rf "$stage_dir"
}
trap cleanup EXIT HUP INT TERM

stage_component="$stage_dir/Isabelle_C"
cp -R "$source_component" "$stage_component"
patch -l -d "$stage_component" -p1 < "$patch_file"

patched_blob=$(git hash-object "$stage_component/$PARSER_PATH")
[ "$patched_blob" = "$PATCHED_PARSER_BLOB" ] ||
  fail "compatibility patch produced unexpected parser blob $patched_blob"

{
  printf '%s\n' "AFP_COMMIT=$AFP_COMMIT"
  printf '%s\n' "PATCHED_PARSER_BLOB=$PATCHED_PARSER_BLOB"
} > "$stage_component/.autocorrode-source-pin"

mv "$stage_component" "$destination"
echo "Prepared pinned Isabelle/C at $destination"
