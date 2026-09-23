# Checker performance

What the E1 bench measures, how to run it, and a dated snapshot. E1 is the
checker-performance bench: it times the Haskell checker over the frozen
evaluation corpus (the per-unit check cost and one full pass over the
harness records) via `make bench`.

The numbers below are **indicative documentation, not frozen evaluation
numbers**. They describe one machine at one commit; re-run the bench rather
than trusting them. The paper's typeset table is generated separately and is
not tracked in this repository — see [why](#why-no-rendered-table-is-committed).

## Running It

### Native Developer Run

```sh
make bench                                                 # aligned text (default)
make bench FORMAT=markdown                                 # markdown
make bench FORMAT=latex OUT=../paper/tables/performance.tex
```

The table goes to stdout unless `--out` names a file; progress goes to stderr,
so stdout stays pipeable. Every run also writes the raw per-unit record to
`measurements/bench.json`, which is gitignored as regenerable output
(`m5-freeze-checklist.md`).

`make bench` builds the Haskell benchmark executable and Lean driver before it
runs. A direct `lara-bench --prebuilt` invocation suppresses that build only
when an existing Lean driver is present.

### Publication Container

The planned publication measurement will use a pinned Linux/arm64 container on
the local Apple M5 Pro:

```sh
make bench-container
```

The host runner requires a clean commit with successful GitHub Actions CI for
that exact SHA. It builds the image before measurement, then waits until the
macOS one-minute load average remains below `0.5` for 120 continuous seconds.
Any excursion resets the quiet interval. The timed container has no network,
uses a read-only root filesystem, and performs no compilation.

A successful run writes `provenance.json`, `bench.json`, and text, Markdown,
and LaTeX tables under
`measurements/bench-runs/<UTC>-<short-SHA>/`. These regenerable files remain
gitignored. `provenance.json` records exact CI and job times, host and container
resources, the image ID, every quiet-window sample, the timed command, and
SHA-256 digests of the four benchmark outputs.

For a local wiring smoke test that does not claim a publication measurement,
use `BENCH_ARGS="--skip-ci --quiet-seconds 0" make bench-container`. The
bypass is explicit in its provenance.

## What is measured

The bench runs the production checker over the frozen corpus units and the
manifest-discovered harness. Its protocols are deliberately aligned with
`scripts/measure.hs`:

- **Haskell sections are in-process and exclude decode.** The timed work is
  `runCheck` plus forcing the rendered verdict text. One check runs in
  single-digit microseconds — below timer noise — so each section runs the work
  100 times and divides; the reported value is the median of 5 such sections.
- **Phases are timed against forced outputs, with earlier stages pre-forced.**
  parse (decode + forced re-encode), validate (replay preflight + group
  boundary), check (the six-stage `checkUnitWith`), compile (the
  cached-adjacency AF and its closure edges), evaluate (grounded labels +
  per-query four-state statuses). Phases are therefore attributable but **need
  not sum to the end-to-end row**.
- **`parse` is the marginal decode cost** inside the real pipeline: end-to-end
  minus the pre-decoded check + render section.
- **The Lean row is full subprocess wall time** of the reference driver,
  startup and decode included. This is a *different protocol*, reported only to
  justify why the Lean executable stays a test oracle rather than a production
  path. **No cross-driver ratio may be derived from it.**
- **The harness sweep** pre-reads every manifest input, then times one full
  in-memory pass (decode + check + render, or the codec-failure path).
- **The multi-artifact map is measured separately, never in these rows.** A
  `.laramap` run is a different shape of work — reading and parsing several
  `.lara` sources, checking each, then linking and checking again — so its cost
  scales with member count rather than with one unit's size, and folding it
  into this bench's rows would make a kernel number mean something else.
  `make bench-map` measures it under its own protocol and prints its own table;
  see [The multi-artifact map](#the-multi-artifact-map-a-separate-protocol)
  below.

## Current Native Snapshot

Measured at commit `7183c48` on 2026-08-23.

_Setting: 564-record harness; Apple M5 Pro, 64 GB RAM, darwin/aarch64, GHC
9.14.1, Lean 4.32.0; medians over 5 sections of 100 batched runs each._

| | median | worst |
| --- | ---: | ---: |
| Corpus unit, end-to-end (µs) | 523.7 | 580.4 |
| &nbsp;&nbsp;parse (µs) | 319.5 | 366.8 |
| &nbsp;&nbsp;check + render, pre-decoded (µs) | 202.2 | 218.7 |
| &nbsp;&nbsp;validate (µs) | 0.4 | 0.5 |
| &nbsp;&nbsp;check (µs) | 189.9 | 214.2 |
| &nbsp;&nbsp;compile (µs) | 0.5 | 2.0 |
| &nbsp;&nbsp;evaluate (µs) | 1.5 | 2.9 |
| Per-artifact total (27 artifacts, µs) | 1075.8 | 1899.0 |
| Framework size (nodes / edges) | 0 / 0 | 2 / 1 |
| Lean reference driver, subprocess (ms) | 2.9 | 3.3 |
| | | |
| 564-record harness, one full pass (ms) | 187.8 | |

In one line: **checking a corpus unit costs about 200 µs, decoding is the same
order of magnitude rather than several times larger, and one pass over all 564
harness records takes under 200 ms.** Checking is cheap enough to sit inside an
edit loop or a CI step.

The `check + render, pre-decoded` row is the stable control: it sits downstream
of the decode boundary, so no wire-codec change can move it. A run whose
control row deviates markedly from ~203 µs is measuring machine load, not the
checker, and should be discarded rather than quoted (this is what happened
during one of the wire-codec optimizations).

**This snapshot's absolute numbers are stale and should not be cited.**
A review of the harness (no fix planned,
2026-08-24) found that the benchmark harness changed from interpreted
(`cabal exec -- runghc scripts/bench.hs`, the driver that produced this
snapshot) to compiled (`cabal run exe:lara-bench`) with no protocol line
altered, and that the change alone moves every row — a *loaded*-machine
compiled run beat this *quiet*-machine interpreted snapshot on every metric
(end-to-end −22%, parse −31%, check + render pre-decoded −9.4%, check −8%).
Load inflates timings and never deflates them, so the harness is the
explanation, not noise. The `~203 µs` control-row reference above is
therefore itself an interpreted-harness artifact, not a compiled-harness
baseline; that follow-up also found no host available to the project reaches the
container publication runner's quiet-window gate, so no corrected snapshot
has been produced. Treat every number in this section as an upper bound from
a retired harness until a fresh compiled-harness snapshot replaces it.

## The multi-artifact map: a separate protocol

```sh
make bench-map                     # aligned text (default)
make bench-map FORMAT=markdown     # markdown
```

`make bench-map` runs `lara-bench --map`. It measures every
**accepted** `map.laramap` conformance anchor, which are the maps
`scripts/check-map-conformance.sh` discovers under `test/fixtures/map/` and
`examples/agreement-map-multi/`. It writes the raw record to
`measurements/bench-map.json`, which is gitignored. An anchor that does not
accept has no full pass to time, so it is left out, and stderr names it with
the one-line diagnostic and exit code `lara check` would print: 1 when the
checker refuses the map, 2 when the map stops before the checker (a member that
cannot be read, a manifest that no longer parses, a reference that does not
resolve). A renamed member file therefore shows up as what it is, not as one
more refusal. The run fails, with the same diagnostic, if the shipped map is not
among the measured ones. Nothing Lean runs, so there is no
Lean build step, and there is no LaTeX format: the paper typesets the kernel
table, and a map row must never be read as one of its rows.

- **Pre-read, then full passes.** One untimed pass reads the manifest, its
  policy, every member and every member's policy into a fresh source cache
  (`Lara.Map.Load.loadMapWith`). Each timed pass then does everything
  `lara check <map.laramap>` does after argument parsing, over that cache: load
  and recheck every member, qualify, merge, saturate, check the linked unit,
  evaluate, and render the composite verdict. No timed pass reads a file's
  bytes. Each pass still resolves paths, because `canonicalizePath` is the
  cache key; that is the one filesystem call left in the timed work.
- **The indented row** times the pure stage alone (`checkMap` plus rendering)
  over members the warm-up pass has already loaded, so the difference between
  the two rows is the cost of loading and rechecking the members.
- **Same batching as the kernel bench:** medians over 5 sections of 100 batched
  runs each. *Worst* is the slowest section, not the slowest input.
- **Member count, linked nodes and edges are printed beside each figure**,
  because those are the variables a map's cost scales with.

No number from this table may be set beside the kernel table's. The two
protocols time different work, on different inputs.

### Map snapshot

Measured at commit `ad513b5` on 2026-09-11 with
`make bench-map FORMAT=markdown`. The one-minute load average was 0.6 on 128
cores. The CPU and RAM fields were supplied through `LARA_BENCH_HOST_CPU` and
`LARA_BENCH_HOST_RAM_BYTES`, because at that commit the environment probe
read only macOS `sysctl`; the Linux probe (`/proc/cpuinfo`, `/proc/meminfo`)
landed afterwards, so the next snapshot needs no overrides.
Like the kernel snapshot, this is indicative: re-run it rather than cite it.

_Setting: 3 accepted map anchors; AMD EPYC 9354 32-Core Processor, 1507 GB RAM,
linux/x86_64, GHC 9.10.3; every file pre-read by one untimed pass (paths are
still resolved per pass); medians over 5 sections of 100 batched runs each._

| | median | worst |
| --- | ---: | ---: |
| test/fixtures/map/agreement (3 members, 3 nodes / 2 edges, µs) | 1729.2 | 1742.6 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 148.8 | 154.8 |
| test/fixtures/map/merge (2 members, 2 nodes / 2 edges, µs) | 630.0 | 645.0 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 60.8 | 62.5 |
| examples/agreement-map-multi (4 members, 4 nodes / 2 edges, µs) | 2778.2 | 2808.1 |
| &nbsp;&nbsp;link + check + render, members pre-loaded (µs) | 272.9 | 276.8 |

In one line: **the shipped four-member map costs about 2.8 ms per full pass,
and about nine tenths of that is loading and rechecking its members. Linking,
the linked check, evaluation and rendering together take about 0.27 ms.** The
three maps differ in what their members contain as well as in how many there
are (the merge fixture's two members are far smaller than the D3 papers), so
the rows show that cost follows the members' work. They are not a scaling
curve.

## Why no rendered table is committed

A timing table is machine state, not source: it is valid only for the machine
and the commit that produced it. Tracking a rendered table therefore guarantees
that, sooner or later, the copy in the tree disagrees with the code beside it.

That is exactly what happened. `tables/performance.tex` was generated at
`0aa97ef`, before the two later
wire optimizations, and
then sat in the repository reporting a `parse` row that no longer described the
shipped decoder — a byte-identical hand-synced duplicate of the paper
repository's own copy, and the stale one of the two. `measurements/` was
already gitignored under precisely this rule; the rendered table was the
inconsistent exception.

So the bench prints, and each consumer owns its copy:

- the **paper repository** owns the `tables/performance.tex` it typesets, and
  refreshes it with one `make bench FORMAT=latex OUT=…`;
- this document owns a dated, explicitly indicative snapshot for readers who
  want an order of magnitude without building the project.

The snapshot above may drift. That is acceptable *because* it is dated and
labelled, and because nothing typesets it into a submitted claim.
