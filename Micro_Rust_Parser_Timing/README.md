# µRust parser timing component

`Micro_Rust_Parser_Timing` aggregates structured timing records emitted by timed `urust_expr` and
`urust_fn` commands. It reads the final PIDE snapshots in an already-built Isabelle session database;
it does not rebuild the session and does not compare the database with current sources.

## Setup

Register and build the component:

```text
make -C Micro_Rust_Parser_Timing build
```

This defines `ISABELLE_MICRO_RUST_PARSER_TIMING_HOME`, builds
`lib/micro_rust_parser_timing.jar`, and registers the `isabelle urust_timing` tool.

## Usage

First build the target session with parser timing enabled on the declarations to measure:

```isabelle
declare [[urust_timing_info = true]]
```

The independent `urust_timing_verbosity` setting may remain at its default `0` for a silent build;
the structured records are still stored. Set it to `1` for an InfoView summary or `2` for the summary
and phase breakdown. InfoView report titles retain command-keyword markup and show the declaration
name in bold.

Then read its stored results:

```text
isabelle urust_timing [OPTIONS] SESSION

  -T NAME      restrict to a theory; repeatable
  -C NUM       show the NUM slowest declarations by parser time
               (0 shows all declarations)
  -J FILE      atomically write the complete JSON report
  -o OPTION    override Isabelle system/database options
```

The default text report contains session totals and a per-theory table. `-C` adds a hotspot table.
The JSON report always contains every selected declaration, sorted by decreasing parser elapsed
time.

Only declaration elapsed latency is aggregated. CPU and GC measurements are intentionally omitted
because declarations may run concurrently. The cumulative elapsed total includes time waiting for
the parser lock and is not session wall-clock overhead.

Malformed records and unknown record versions are ignored with warnings. A missing database, a failed
session build, an unknown theory filter, or a missing final PIDE snapshot is an error.

## Tests

```text
make -C Micro_Rust_Parser_Timing test
```

The unit suite checks record decoding, aggregation, filtering, deterministic hotspot ordering, JSON,
and malformed/versioned data. The end-to-end suite builds a neutral two-theory fixture with parallel
workers, then checks declaration names, theory filtering, ordering, and atomic JSON output without
timing thresholds.
