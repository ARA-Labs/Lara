# Checker timing on the Apple M5 Pro, 2026-11-10

**Date:** 2026-11-10

## TL;DR

At commit `018a2ae`, the Haskell checker took about 200 µs to check one corpus unit and render its verdict, and about 440 µs end to end once decoding is included. Ten repeated runs agreed closely: the per-run median of the control row (check and render on an already decoded unit) varied by 2.3% in the unpinned batch and 1.2% in the later batch pinned to the Docker VM's isolated CPU. Host load moves the numbers: four extra busy processes on the Mac raised the control row by about 6%, more than the spread between ordinary runs. The published table comes from the pinned batch, under a selection rule fixed before the runs, and it describes the checker on a working desktop under the load recorded for each run.

## How long does one check take?

The published table is the table run of the pinned batch, chosen by the rule in [Evaluation](evaluation.md#running-the-bench): the run whose control-row median is the lower median of its batch. Each figure is the median over the 60 corpus units of a per-unit value, and each per-unit value is the median of 5 timed sections of 100 repetitions, divided by 100. "Worst" is the slowest unit.

| Row | Median | Worst |
| --- | ---: | ---: |
| Corpus unit, end to end (µs) | 437.6 | 472.4 |
| Parse, the marginal decode cost (µs) | 238.4 | 248.8 |
| Check and render, pre-decoded: the control row (µs) | 199.8 | 226.5 |
| Validate (µs) | 0.1 | 0.2 |
| Check (µs) | 194.0 | 221.4 |
| Compile (µs) | 0.0 | 0.6 |
| Evaluate (µs) | 0.6 | 1.1 |
| Per-artifact total, 27 artifacts (µs) | 878.7 | 1751.4 |
| Lean reference driver, one subprocess (ms) | 1.1 | 1.3 |
| 660-record harness, one full pass (ms) | 172.2 | |

Decoding and checking cost about the same: of the 437.6 µs end to end, 238.4 µs is parsing the wire format and 199.8 µs is checking and rendering. Almost all of the check is the six-stage acceptance check; compiling the attack graph and evaluating statuses each take under a microsecond, because the median corpus unit has no graph nodes and the largest has two nodes and one edge. The Lean row is a whole process, startup included, so it shows why the Lean executable stays a test oracle; it must not be divided into the Haskell rows.

## Do repeated runs agree?

Three batches ran back to back at the same commit and image. Each run took about 27 seconds. The table lists the across-run median of each run's per-unit median, its range, and the host's one-minute load average sampled every 5 seconds while the runs were timed.

| Batch | Runs | Host load during runs (min / median / max) | Control row median (µs) | Range across runs | End to end (µs) | Lean subprocess (ms) | Harness pass (ms) |
| --- | ---: | --- | ---: | --- | ---: | ---: | ---: |
| Unpinned | 10 | 2.41 / 2.83 / 3.08 | 201.6 | 199.5 to 204.1 (2.3%) | 445.4 | 1.33 | 174.6 |
| Pinned to VM CPU 17 | 10 | 3.00 / 3.52 / 6.71 | 199.7 | 198.5 to 200.9 (1.2%) | 437.9 | 1.11 | 171.1 |
| Unpinned, 4 host busy loops | 5 | 3.03 / 5.28 / 6.71 | 213.2 | 208.0 to 215.3 (3.4%) | 464.6 | 1.33 | 178.1 |

Run-level medians hide some per-unit noise. In the unpinned batch, a typical unit's control row varied by 5.8% across the ten runs and the noisiest unit by 23.5%; in the pinned batch the same figures were 3.9% and 9.1%. A claim about one unit therefore needs the batch median, while a claim about the corpus median is stable to a few percent.

No run failed, so none was excluded. Every run, with its control-row median and the load sampled while it was timed, is listed in [Appendix: Every run](#appendix-every-run).

## Does host load move the numbers?

Four `yes > /dev/null` processes on the Mac pushed the load average from about 3 to about 5, and the control row rose from 201.6 µs to 213.2 µs, 5.8% above the unpinned batch. Every busy run was slower than every unpinned run, so the difference is larger than run-to-run noise.

That result limits what the other batches can claim. Repeated runs agreeing shows that the measurement repeats on this host; it does not show that background work had no effect, because a steady load can slow every run alike. All three batches ran with Spotlight indexing active and desktop apps open, and the load average never fell below 2.41 during a timed run. Two earlier attempts on the same host that day waited an hour each for the runner's default quiet window (load below 0.5 for two minutes) and never reached it; the lowest reading in 1,440 samples was 0.83. These numbers describe the checker under that load. How much faster it would be on an idle machine was not measured.

## Does pinning to the VM's isolated CPU help?

The pinned batch, which ran last, had a narrower spread than the unpinned batch. OrbStack 2.2.5 boots its Linux VM with `isolcpus=17`, which keeps ordinary Linux work off virtual CPU 17, and the runner confirmed that `/sys/devices/system/cpu/isolated` read `17` before pinning. The pinned batch had half the unpinned batch's spread (1.2% against 2.3%) and a slightly lower median (199.7 µs against 201.6 µs), and its Lean subprocess row was lower, 1.11 ms against 1.33 ms. These are observed differences between two batches, not a measured effect of pinning. The batches ran one after the other (unpinned, then busy loops, then pinned), so pinning is confounded with time order and any thermal drift, and the load readings of the first pinned runs (up to 6.71) still carry the one-minute average left by the busy loops, which had already been stopped. Interleaving pinned and unpinned runs would be needed to attribute the difference to pinning.

Pinning isolates the benchmark only from work inside the VM. Virtual CPU 17 is still an ordinary macOS thread, and macOS decides which physical core runs it; the guest cannot reserve a performance core. macOS on Apple Silicon has no CPU affinity to reserve cores from the host side either. The one host-side lever used here was `taskpolicy -b` on `corespotlightd` (PID 1076), which confines that process to the efficiency cores; it slows other work and reserves nothing.

The rule for choosing between batches was fixed before either ran: keep the unpinned batch unless the pinned batch has a narrower control-row range and a median that is not higher. The pinned batch met both conditions, so its table run supplies the published table. The unpinned table run (`20261110T191845Z-018a2ae1e630-r06`, control-row median 201.0 µs) differs by about 1%, well within the claims this report supports.

## How were the runs made?

| Item | Value |
| --- | --- |
| Commit | `018a2ae1e6309351b23f9768f5f1bb2b700a990c`, clean tree, Haskell CI [run 42882314673](https://github.com/ARA-Labs/Lara/actions/runs/42882314673) passed |
| Host | Apple M5 Pro, 64 GB RAM, macOS 27.2 |
| VM | OrbStack 2.2.5, Docker engine 29.8.2, Linux 7.2.12-orbstack, 18 virtual CPUs, about 16 GB |
| Image | `sha256:62a8d63db1220caaa072fbe4f2aacc19ee9f25d12d8d8457948d45e100474754`, GHC 9.14.1, Lean 4.32.0, no network, read-only root |
| Batches | unpinned `20261110T191630Z`, busy `20261110T192100Z`, pinned `20261110T192322Z` |
| Table run | `20261110T192652Z-018a2ae1e630-r09` |
| Quiet window | bypassed (`--quiet-seconds 0`); load sampled during each timed run instead |
| Host conditions | Spotlight indexing active, `corespotlightd` demoted with `taskpolicy -b`, desktop apps open |

The run directories under `measurements/bench-runs/` are gitignored and exist only on the measuring host. Each holds `provenance.json` with the CI run, image ID, batch, pinning check, every load sample and the SHA-256 digests of the outputs, plus `bench.json` and the rendered tables. The per-run values this report relies on are copied into [Appendix: Every run](#appendix-every-run).

## Recommendations

1. Quote the checker as taking about 200 µs per corpus unit for check and render, and about 440 µs including decoding, on this host. Do not quote single figures more precisely than the batch range.
2. Refresh the paper's `tables/performance.tex` from the table run's `performance.tex`, and state the commit, host and the load caveat beside it.
3. Before adopting pinning as the default, interleave pinned and unpinned runs in one session, because the batches here ran in sequence and cannot separate pinning from time order.
4. If a later claim needs precision better than about 5%, measure on a dedicated Linux host with isolated cores, because this Mac cannot remove the load that moved these numbers.

## Appendix: Reproduction

A rerun from a clean checkout of `018a2ae`, with Haskell CI green on that commit, produces new batch ids and new run directories; the ids in this report name the 2026-11-10 runs on the measuring host. The busy batch ran with four `yes > /dev/null` processes started before it and stopped after it.

```sh
taskpolicy -b -p <corespotlightd pid>
BENCH_ARGS="--quiet-seconds 0 --runs 10 --demoted-pid <pid>" make bench-container
BENCH_ARGS="--quiet-seconds 0 --runs 5 --demoted-pid <pid>" make bench-container   # with 4 busy loops
BENCH_ARGS="--quiet-seconds 0 --runs 10 --demoted-pid <pid> --cpuset-cpus 17" make bench-container
taskpolicy -B -p <corespotlightd pid>

python3 scripts/bench_compare.py --batch <batch id from any run's provenance.json>
```

`bench_compare.py` prints every run with its control-row median and in-run load, and the across-run summary used above. The end-to-end, Lean and harness columns in the batch table are medians across runs of the same per-run statistics, read from each run's `bench.json`.

## Appendix: Every run

Control-row median is the median across the 60 corpus units of `kernel_ns` in that run's `bench.json`. Load is the host's one-minute load average sampled every 5 seconds from just before the container started to just after it exited.

| Batch | Run | Control-row median (µs) | Load during run (min / median / max) |
| --- | --- | ---: | --- |
| Unpinned | `20261110T191630Z-018a2ae1e630-r01` | 202.3 | 2.41 / 2.54 / 3.00 |
| Unpinned | `20261110T191657Z-018a2ae1e630-r02` | 204.1 | 2.84 / 2.92 / 3.08 |
| Unpinned | `20261110T191725Z-018a2ae1e630-r03` | 204.0 | 2.72 / 2.84 / 2.94 |
| Unpinned | `20261110T191751Z-018a2ae1e630-r04` | 203.3 | 2.75 / 2.87 / 2.98 |
| Unpinned | `20261110T191818Z-018a2ae1e630-r05` | 203.6 | 2.76 / 2.82 / 2.98 |
| Unpinned | `20261110T191845Z-018a2ae1e630-r06` (table run) | 201.0 | 2.76 / 2.80 / 2.98 |
| Unpinned | `20261110T191912Z-018a2ae1e630-r07` | 200.2 | 2.63 / 2.76 / 2.94 |
| Unpinned | `20261110T191938Z-018a2ae1e630-r08` | 199.5 | 2.63 / 2.82 / 2.94 |
| Unpinned | `20261110T192004Z-018a2ae1e630-r09` | 199.9 | 2.69 / 2.84 / 2.91 |
| Unpinned | `20261110T192030Z-018a2ae1e630-r10` | 200.6 | 2.69 / 2.85 / 2.89 |
| Busy loops | `20261110T192100Z-018a2ae1e630-r01` | 208.0 | 3.03 / 3.83 / 4.30 |
| Busy loops | `20261110T192128Z-018a2ae1e630-r02` (table run) | 213.2 | 4.30 / 4.59 / 4.97 |
| Busy loops | `20261110T192156Z-018a2ae1e630-r03` | 215.3 | 4.97 / 5.28 / 5.78 |
| Busy loops | `20261110T192224Z-018a2ae1e630-r04` | 211.6 | 5.78 / 6.13 / 6.27 |
| Busy loops | `20261110T192252Z-018a2ae1e630-r05` | 214.1 | 6.17 / 6.37 / 6.71 |
| Pinned to VM CPU 17 | `20261110T192322Z-018a2ae1e630-r01` | 200.1 | 5.16 / 5.96 / 6.71 |
| Pinned to VM CPU 17 | `20261110T192349Z-018a2ae1e630-r02` | 199.8 | 3.92 / 4.45 / 5.16 |
| Pinned to VM CPU 17 | `20261110T192415Z-018a2ae1e630-r03` | 199.6 | 3.38 / 3.64 / 3.92 |
| Pinned to VM CPU 17 | `20261110T192441Z-018a2ae1e630-r04` | 200.9 | 3.38 / 3.47 / 3.52 |
| Pinned to VM CPU 17 | `20261110T192507Z-018a2ae1e630-r05` | 199.5 | 3.32 / 3.39 / 3.52 |
| Pinned to VM CPU 17 | `20261110T192533Z-018a2ae1e630-r06` | 200.3 | 3.20 / 3.39 / 3.59 |
| Pinned to VM CPU 17 | `20261110T192559Z-018a2ae1e630-r07` | 200.2 | 3.25 / 3.35 / 3.59 |
| Pinned to VM CPU 17 | `20261110T192626Z-018a2ae1e630-r08` | 199.5 | 3.25 / 3.78 / 4.19 |
| Pinned to VM CPU 17 | `20261110T192652Z-018a2ae1e630-r09` (table run, published) | 199.6 | 3.36 / 3.56 / 3.70 |
| Pinned to VM CPU 17 | `20261110T192718Z-018a2ae1e630-r10` | 198.5 | 3.00 / 3.20 / 3.41 |
