# Checker timing on the Apple M5 Pro, 2026-11-10

**Date:** 2026-11-10

## TL;DR

At commit `018a2ae`, the Haskell checker took about 200 µs to check one corpus unit and render its verdict, and about 440 µs end to end once decoding is included. Ten repeated runs agreed closely: the per-run median of the control row (check and render on an already decoded unit) varied by 2.3% unpinned and 1.2% when the container was pinned to the Docker VM's isolated CPU. Host load moves the numbers: four extra busy processes on the Mac raised the control row by about 6%, more than the spread between ordinary runs. The published table comes from the pinned batch, under a selection rule fixed before the runs, and it supports statements about magnitude (hundreds of microseconds) on a working desktop rather than an idle one.

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

No run failed, so none was excluded.

## Does host load move the numbers?

Four `yes > /dev/null` processes on the Mac pushed the load average from about 3 to about 5, and the control row rose from 201.6 µs to 213.2 µs, 5.8% above the unpinned batch. Every busy run was slower than every unpinned run, so the difference is larger than run-to-run noise.

That result limits what the other batches can claim. Repeated runs agreeing shows that the measurement repeats on this host; it does not show that background work had no effect, because a steady load can slow every run alike. All three batches ran with Spotlight indexing active and desktop apps open, and the load average never fell below 2.41 during a timed run. Two earlier attempts on the same host that day waited an hour each for the runner's default quiet window (load below 0.5 for two minutes) and never reached it; the lowest reading in 1,440 samples was 0.83. The numbers here are what the checker does on a working desktop, and an idle machine might be a few percent faster.

## Does pinning to the VM's isolated CPU help?

Pinning narrowed the spread on this host. OrbStack 2.2.5 boots its Linux VM with `isolcpus=17`, which keeps ordinary Linux work off virtual CPU 17, and the runner confirmed that `/sys/devices/system/cpu/isolated` read `17` before pinning. The pinned batch had half the unpinned batch's spread (1.2% against 2.3%) and a slightly lower median (199.7 µs against 201.6 µs), although its host load was higher. The Lean subprocess row fell most, from 1.33 ms to 1.11 ms. One possible reason is that the subprocess starts on a CPU with no other guest work; that was not tested.

Pinning isolates the benchmark only from work inside the VM. Virtual CPU 17 is still an ordinary macOS thread, and macOS decides which physical core runs it; the guest cannot reserve a performance core. macOS on Apple Silicon has no CPU affinity to reserve cores from the host side either. The one host-side lever used here was `taskpolicy -b` on `corespotlightd` (PID 1076), which confines that process to the efficiency cores; it slows other work and reserves nothing.

The rule for choosing between batches was fixed before either ran: keep the unpinned batch unless the pinned batch has a narrower control-row range and a median that is not higher. The pinned batch met both conditions, so its table run supplies the published table.

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

The run directories under `measurements/bench-runs/` are gitignored. Each holds `provenance.json` with the CI run, image ID, batch, pinning check, every load sample and the SHA-256 digests of the outputs, plus `bench.json` and the rendered tables.

## Recommendations

1. Quote the checker as taking about 200 µs per corpus unit for check and render, and about 440 µs including decoding, on this host. Do not quote single figures more precisely than the batch range.
2. Refresh the paper's `tables/performance.tex` from the table run's `performance.tex`, and state the commit, host and the load caveat beside it.
3. Pin publication batches to the VM's isolated CPU when the runner confirms one exists; on this host it halved the spread.
4. If a later claim needs precision better than about 5%, measure on a dedicated Linux host with isolated cores, because this Mac cannot remove the load that moved these numbers.

## Appendix: Reproduction

Run from a clean checkout of `018a2ae` with Haskell CI green on that commit. The busy batch ran with four `yes > /dev/null` processes started before it and stopped after it.

```sh
taskpolicy -b -p <corespotlightd pid>
BENCH_ARGS="--quiet-seconds 0 --runs 10 --demoted-pid <pid>" make bench-container
BENCH_ARGS="--quiet-seconds 0 --runs 5 --demoted-pid <pid>" make bench-container   # with 4 busy loops
BENCH_ARGS="--quiet-seconds 0 --runs 10 --demoted-pid <pid> --cpuset-cpus 17" make bench-container
taskpolicy -B -p <corespotlightd pid>

python3 scripts/bench_compare.py --batch 20261110T191630Z
python3 scripts/bench_compare.py --batch 20261110T192100Z
python3 scripts/bench_compare.py --batch 20261110T192322Z
```

`bench_compare.py` prints every run with its control-row median and in-run load, and the across-run summary used above. The end-to-end, Lean and harness columns in the batch table are medians across runs of the same per-run statistics, read from each run's `bench.json`.
