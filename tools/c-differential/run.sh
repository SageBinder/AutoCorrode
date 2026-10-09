#!/usr/bin/env bash
set -euo pipefail

readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
readonly REPO_ROOT="$(git -C "$SCRIPT_DIR" rev-parse --show-toplevel)"

ORACLE_REV="${ORACLE_REV:-f8e08ba}"
ISABELLE_BIN="${ISABELLE_BIN:-${ISABELLE:-}}"
AFP_THYS="${AFP_THYS:-}"
OUTPUT_DIR=""
THREADS="${THREADS:-2}"
JOBS="${JOBS:-1}"
KEEP_WORKTREES=0

usage() {
  cat <<'EOF'
Usage: tools/c-differential/run.sh [options]

Compare the pinned C oracle with the current working tree.

Options:
  --isabelle PATH   Isabelle executable (or set ISABELLE_BIN/ISABELLE)
  --afp PATH        AFP thys directory (or set AFP_THYS)
  --oracle REV      Oracle revision (default: f8e08ba)
  --output DIR      Result directory (default: a fresh /tmp directory)
  --threads N       Isabelle worker threads per session (default: 2)
  --jobs N          Isabelle build jobs (default: 1)
  --keep-worktrees  Retain temporary worktrees for diagnosis
  -h, --help        Show this help
EOF
}

die() {
  printf 'c-differential: %s\n' "$*" >&2
  exit 2
}

while (($#)); do
  case "$1" in
    --isabelle)
      (($# >= 2)) || die "--isabelle requires a path"
      ISABELLE_BIN="$2"
      shift 2
      ;;
    --afp)
      (($# >= 2)) || die "--afp requires a path"
      AFP_THYS="$2"
      shift 2
      ;;
    --oracle)
      (($# >= 2)) || die "--oracle requires a revision"
      ORACLE_REV="$2"
      shift 2
      ;;
    --output)
      (($# >= 2)) || die "--output requires a directory"
      OUTPUT_DIR="$2"
      shift 2
      ;;
    --threads)
      (($# >= 2)) || die "--threads requires a number"
      THREADS="$2"
      shift 2
      ;;
    --jobs)
      (($# >= 2)) || die "--jobs requires a number"
      JOBS="$2"
      shift 2
      ;;
    --keep-worktrees)
      KEEP_WORKTREES=1
      shift
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      die "unknown option: $1"
      ;;
  esac
done

[[ "$THREADS" =~ ^[1-9][0-9]*$ ]] || die "--threads must be a positive integer"
[[ "$JOBS" =~ ^[1-9][0-9]*$ ]] || die "--jobs must be a positive integer"

if [[ -z "$ISABELLE_BIN" ]]; then
  ISABELLE_BIN="$(command -v isabelle || true)"
fi
[[ -n "$ISABELLE_BIN" && -x "$ISABELLE_BIN" ]] ||
  die "set --isabelle to an executable Isabelle launcher"
[[ -n "$AFP_THYS" && -d "$AFP_THYS" ]] ||
  die "set --afp to the AFP thys directory"

for component in Word_Lib Isabelle_Lex-Yacc Isabelle_C; do
  [[ -d "$AFP_THYS/$component" ]] ||
    die "missing AFP component: $AFP_THYS/$component"
done

ORACLE_COMMIT="$(git -C "$REPO_ROOT" rev-parse --verify "${ORACLE_REV}^{commit}")" ||
  die "cannot resolve oracle revision: $ORACLE_REV"
CURRENT_COMMIT="$(git -C "$REPO_ROOT" rev-parse --verify HEAD)"

RUN_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/autocorrode-c-differential.XXXXXX")"
if [[ -z "$OUTPUT_DIR" ]]; then
  OUTPUT_DIR="$(mktemp -d "${TMPDIR:-/tmp}/autocorrode-c-differential-results.XXXXXX")"
else
  mkdir -p "$OUTPUT_DIR"
  OUTPUT_DIR="$(cd "$OUTPUT_DIR" && pwd -P)"
fi

ORACLE_TREE="$RUN_ROOT/oracle"
CURRENT_TREE="$RUN_ROOT/current"
ORACLE_SUITE="$RUN_ROOT/oracle-suite"
CURRENT_SUITE="$RUN_ROOT/current-suite"
WORKTREES_CREATED=0

cleanup() {
  local status=$?
  if ((WORKTREES_CREATED)); then
    if ((KEEP_WORKTREES)); then
      printf 'Temporary worktrees retained at %s\n' "$RUN_ROOT" >&2
    else
      git -C "$REPO_ROOT" worktree remove --force "$ORACLE_TREE" >/dev/null 2>&1 || true
      git -C "$REPO_ROOT" worktree remove --force "$CURRENT_TREE" >/dev/null 2>&1 || true
      rm -rf -- "$RUN_ROOT"
    fi
  else
    rm -rf -- "$RUN_ROOT"
  fi
  exit "$status"
}
trap cleanup EXIT INT TERM

printf 'Creating detached worktrees...\n'
git -C "$REPO_ROOT" worktree add --detach "$ORACLE_TREE" "$ORACLE_COMMIT" >/dev/null
git -C "$REPO_ROOT" worktree add --detach "$CURRENT_TREE" "$CURRENT_COMMIT" >/dev/null
WORKTREES_CREATED=1

printf 'Snapshotting current tracked and untracked implementation files...\n'
git -C "$REPO_ROOT" diff --binary HEAD -- . >"$RUN_ROOT/current.patch"
if [[ -s "$RUN_ROOT/current.patch" ]]; then
  git -C "$CURRENT_TREE" apply "$RUN_ROOT/current.patch"
fi

while IFS= read -r -d '' path; do
  case "$path" in
    tools/c-differential/*|*/output/*)
      continue
      ;;
  esac
  # Only session inputs belong in the test snapshot; unrelated workspace files do not.
  session_root="${path%%/*}"
  [[ -f "$REPO_ROOT/$session_root/ROOT" ]] || continue
  mkdir -p "$CURRENT_TREE/$(dirname "$path")"
  cp -a -- "$REPO_ROOT/$path" "$CURRENT_TREE/$path"
done < <(git -C "$REPO_ROOT" ls-files --others --exclude-standard -z)

mkdir -p "$ORACLE_SUITE" "$CURRENT_SUITE"
cp "$SCRIPT_DIR/templates/ROOT" "$ORACLE_SUITE/ROOT"
cp "$SCRIPT_DIR/templates/ROOT" "$CURRENT_SUITE/ROOT"
cp "$SCRIPT_DIR/templates/oracle/Differential_Observations.thy" \
  "$ORACLE_SUITE/"
cp "$SCRIPT_DIR/templates/oracle/Differential_Failures.thy" \
  "$ORACLE_SUITE/"
cp "$SCRIPT_DIR/templates/current/Differential_Observations.thy" \
  "$CURRENT_SUITE/"
cp "$SCRIPT_DIR/templates/current/Differential_Failures.thy" \
  "$CURRENT_SUITE/"

prune_frontend_smokes() {
  local root_file="$1/Micro_C_Parsing_Frontend/ROOT"
  python3 - "$root_file" <<'PY'
from pathlib import Path
import sys

path = Path(sys.argv[1])
lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
for index, line in enumerate(lines):
    if line.startswith("  theories [document=false]"):
        path.write_text("".join(lines[:index]), encoding="utf-8")
        break
else:
    raise SystemExit(f"no frontend smoke-theory section found in {path}")
PY
}

# The pinned oracle contains smoke fixtures that its own translator rejects
# under the supported Isabelle toolchain. Keep all production theories but
# remove session-owned smoke theories so the focused differential theories can
# run. This changes only the disposable worktree's session selection.
prune_frontend_smokes "$ORACLE_TREE"
prune_frontend_smokes "$CURRENT_TREE"

ISABELLE_DOC_DIR="$(cd "$(dirname "$ISABELLE_BIN")/../src/Doc" && pwd -P)"

session_dirs() {
  local tree=$1
  local suite=$2
  printf '%s\n' \
    -d "$ISABELLE_DOC_DIR" \
    -d "$AFP_THYS/Word_Lib" \
    -d "$AFP_THYS/Isabelle_Lex-Yacc" \
    -d "$AFP_THYS/Isabelle_C" \
    -d "$tree" \
    -d "$suite"
}

run_build() {
  local side=$1
  local tree=$2
  local suite=$3
  local session=$4
  local log=$5
  local side_root="$RUN_ROOT/$side-isabelle"
  local observations="$OUTPUT_DIR/$side-all-observations.txt"
  local -a dirs

  mkdir -p "$side_root/user-home" "$side_root/isabelle-home"
  : >"$observations"
  mapfile -t dirs < <(session_dirs "$tree" "$suite")

  env \
    USER_HOME="$side_root/user-home" \
    ISABELLE_HOME_USER="$side_root/isabelle-home" \
    ACDIFF_OUTPUT="$observations" \
    "$ISABELLE_BIN" build \
      -b -j "$JOBS" -o "threads=$THREADS" -o document=false -v \
      "${dirs[@]}" "$session" >"$log" 2>&1
}

run_positive() {
  local side=$1
  local tree=$2
  local suite=$3
  local log="$OUTPUT_DIR/$side-positive.log"

  printf 'Building %s positive observations...\n' "$side"
  if run_build "$side" "$tree" "$suite" \
      AutoCorrode_C_Differential_Positive "$log"; then
    grep '^ACDIFF|failure|' "$OUTPUT_DIR/$side-all-observations.txt" \
      >"$OUTPUT_DIR/$side-failures.txt" || true
    grep -v '^ACDIFF|failure|' "$OUTPUT_DIR/$side-all-observations.txt" \
      >"$OUTPUT_DIR/$side-observations.txt" || true
    if [[ ! -s "$OUTPUT_DIR/$side-observations.txt" ]]; then
      printf 'No semantic observations captured for %s; see %s\n' \
        "$side" "$log" >&2
      return 1
    fi
    if [[ ! -s "$OUTPUT_DIR/$side-failures.txt" ]]; then
      printf 'No expected-failure observations captured for %s; see %s\n' \
        "$side" "$log" >&2
      return 1
    fi
    return 0
  fi

  printf 'Positive observation build failed for %s; see %s\n' "$side" "$log" >&2
  return 1
}

write_metadata() {
  cat >"$OUTPUT_DIR/metadata.txt" <<EOF
oracle_requested=$ORACLE_REV
oracle_commit=$ORACLE_COMMIT
current_head=$CURRENT_COMMIT
current_tree_dirty=$(if git -C "$REPO_ROOT" diff --quiet HEAD -- . && [[ -z "$(git -C "$REPO_ROOT" ls-files --others --exclude-standard)" ]]; then printf false; else printf true; fi)
isabelle=$("$ISABELLE_BIN" version)
isabelle_bin=$ISABELLE_BIN
afp_thys=$AFP_THYS
threads=$THREADS
jobs=$JOBS
EOF
}

overall=0
oracle_complete=0
current_complete=0
write_metadata

if run_positive oracle "$ORACLE_TREE" "$ORACLE_SUITE"; then
  oracle_complete=1
else
  : >"$OUTPUT_DIR/oracle-observations.txt"
  : >"$OUTPUT_DIR/oracle-failures.txt"
  overall=1
fi
if run_positive current "$CURRENT_TREE" "$CURRENT_SUITE"; then
  current_complete=1
else
  : >"$OUTPUT_DIR/current-observations.txt"
  : >"$OUTPUT_DIR/current-failures.txt"
  overall=1
fi

python3 "$SCRIPT_DIR/compare.py" \
  --oracle "$OUTPUT_DIR/oracle-observations.txt" \
  --current "$OUTPUT_DIR/current-observations.txt" \
  --oracle-failures "$OUTPUT_DIR/oracle-failures.txt" \
  --current-failures "$OUTPUT_DIR/current-failures.txt" \
  --oracle-complete "$oracle_complete" \
  --current-complete "$current_complete" \
  --output "$OUTPUT_DIR/comparison.json" ||
  overall=1

printf '\nResults: %s\n' "$OUTPUT_DIR"
if [[ -f "$OUTPUT_DIR/comparison.json" ]]; then
  python3 - "$OUTPUT_DIR/comparison.json" <<'PY'
import json
import sys

with open(sys.argv[1], encoding="utf-8") as stream:
    result = json.load(stream)
print("Parity:", "PASS" if result["equal"] else "FAIL")
print("Matched observations:", result["matched_observations"])
print("Matched expected failures:", result["matched_failures"])
for difference in result["differences"]:
    print("Difference:", difference)
PY
fi

exit "$overall"
