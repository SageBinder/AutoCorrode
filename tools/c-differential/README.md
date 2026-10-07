# AutoCorrode/C differential parity harness

`run.sh` compares the pinned oracle revision `f8e08ba` with the current
working tree. It creates two detached temporary Git worktrees, snapshots
tracked changes and untracked session inputs into the current-side worktree,
and gives each side a separate Isabelle `USER_HOME` and
`ISABELLE_HOME_USER` (therefore separate heap and database directories).

Typical invocation:

```sh
tools/c-differential/run.sh \
  --isabelle /home/user/Isabelle2025-2/bin/isabelle \
  --afp /path/to/afp/thys
```

The result directory contains complete build logs, normalized observations,
metadata, and `comparison.json`. Use `--output DIR` to retain them at a
specific location. Temporary worktrees are removed even after failure unless
`--keep-worktrees` is supplied.

The disposable worktrees retain every production frontend theory, but the
harness removes the frontend session's built-in smoke-theory list. This is
necessary because the pinned oracle includes fixture spellings that its own
translator rejects on Isabelle2025-2; the focused replacement observations
cover the compared forms without changing implementation source.

The positive session compares:

- executable reductions for signed/unsigned arithmetic and C aborts;
- selected ILP32 and LP64 big-endian ABI metadata;
- signatures of seven freshly translated scalar functions;
- four focused lowering/semantic contracts derived from the C example corpus
  (conditionals, signed overflow, division by zero, and shifts).

The old flat names are normalized to current unit-qualified names, for
example `c_diff_add` to `DiffUnit.diff_add`.

Three commands are transactionally attempted and must fail on both sides with
the expected diagnostic category: a variadic definition, a call to an
undeclared function, and malformed C syntax.

This is deliberately a selected-observable harness, not an equivalence
proof. It does not compare every generated term, every ABI/compiler profile,
memory-state executions, all contracts, diagnostic wording, timing, or
nondeterministic evaluation order. It also cannot detect shared bugs present
in both revisions.
