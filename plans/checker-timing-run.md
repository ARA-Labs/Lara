# Plan: publication timing run for the Haskell checker

**Status:** not started. Tracked by issue #70. When the report lands, move the protocol into `docs/evaluation.md#checker-performance` and delete this plan.

## Goal

Produce the numbers for the kernel bench table (`make bench-container`) at one pinned commit, record them in `docs/checker-timing.md`, and refresh the paper's `tables/performance.tex` from the same runs. The subject is the Haskell checker. The Lean row (`lara-driver` subprocess wall time) stays only because `lara-bench --prebuilt` requires the driver; it is a separate protocol and no ratio between it and the Haskell rows may be quoted.

## What the numbers may claim

The report states timings observed on the named host, under the host load recorded during each run, and how closely the runs agreed. Agreement between runs shows that the measurement repeats. It does not show that background work had no effect: a steady load, or macOS placing the Docker VM's threads on efficiency cores, can slow every run by the same amount. The LLVM benchmarking guide makes the same point: low noise "is required, but not sufficient. It does not exclude measurement bias."

The paper's timing statements are about magnitude (a check takes a few hundred microseconds; the Lean driver process takes about a millisecond). The report must say whether the observed spread is small next to those statements.

## Why the runner's load gate is dropped

`scripts/bench_container.py` waits until the one-minute load average stays below 0.5 for 120 s. Two one-hour attempts at `9c3f6fa` on 2026-11-10 never reached it: the lowest of 1,440 samples was 0.83, with Spotlight indexing, `gh`, and desktop apps running. The gate also samples load only before `docker run`, so it says nothing about the timed interval. The runs below use `--quiet-seconds 0` (recorded as bypassed in `provenance.json`) and sample load during the timed interval instead.

## Can cores be reserved?

Not on this host. macOS on Apple Silicon has no CPU affinity: the thread-affinity policy is a hint and is unsupported on arm64 ([Stack Overflow](https://stackoverflow.com/questions/77422201/is-it-still-possible-to-set-thread-affinity-in-macos)). The benchmark runs inside Docker's Linux VM, and `--cpuset-cpus` or `taskset` there pins to virtual CPUs, which are ordinary host threads that macOS moves across performance and efficiency cores.

The closest available lever is to push other work off the performance cores. `taskpolicy -b -p <pid>` confines every thread of a process to the efficiency cores ([Eclectic Light, tested on Monterey](https://eclecticlight.co/2022/10/20/making-the-most-of-apple-silicon-power-5-user-control/); behavior on the current macOS is not yet verified here). It is a brake on other processes, not a reservation for ours.

Exclusive cores need a Linux host, where `isolcpus=` or `cset shield -c N -k on` moves every other thread, kernel threads included, off the benchmark cores ([LLVM benchmarking tips](https://llvm.org/docs/Benchmarking.html)). Moving the publication run to such a host changes the reported machine and is a separate decision.

Inside the VM, part of that method is already available. OrbStack 2.2.5 boots its kernel with `isolcpus=17` (`/proc/cmdline` in any container), so the guest scheduler keeps ordinary work off virtual CPU 17, and the guest exposes the cgroup v2 `cpuset` controller, so `docker run --cpuset-cpus=17` places the container there. `lara-bench` uses GHC's non-threaded RTS, so one CPU is enough for the Haskell sections. This isolates the benchmark from other work in the VM only. Virtual CPU 17 is still a macOS thread competing with host processes, which were the load observed on 2026-11-10, and the guest cannot choose which physical core runs it. Pinning could even make results slower or more variable if macOS places that one thread on an efficiency core, so it is measured as its own batch against the unpinned one rather than assumed to help. The kernel command line is OrbStack's and cannot be changed from the guest.

## Tasks

1. **Runner support.** Extend `scripts/bench_container.py` so the protocol is reproducible from the repository rather than from an ad hoc driver:
   - `--runs N`: build the image once, then run the container `N` times sequentially, each into its own `measurements/bench-runs/<UTC>-<sha>/` directory.
   - Sample the host's one-minute load every 5 s from `docker run` start to exit and store the samples in that run's `provenance.json`.
   - `--demote-pids` (or a documented manual step): record which processes were demoted with `taskpolicy -b` before the runs.
   - `--cpuset-cpus CPUS`: pass through to `docker run` and record it in `provenance.json`.
   - Unit coverage in `scripts/test_bench_container.py` for the run loop and the in-run sampler, following the existing fake-clock style.
2. **Comparison.** A script that reads every run directory of one batch and writes, per corpus unit and per row, the median and range across runs of the `check + render, pre-decoded` control row, plus each run's in-run load summary. All runs are kept. A run is excluded only for a reason declared here in advance: nonzero exit or failed output validation.
3. **Published table.** Predeclared choice: the run whose median control-row value across units is the median of the batch supplies `performance.{txt,md,tex}`. The report lists every run.
4. **Optional bias probe.** After the main batch, 5 more runs with 4 single-threaded busy loops on the host. If the control-row medians match the main batch within its range, that is evidence the load we cannot remove does not move these numbers by much; if not, the report says the result depends on load.
5. **Pinned batch.** 10 runs with `--cpuset-cpus 17`, compared with the unpinned main batch on the same comparison. The published table stays with the unpinned batch unless the pinned batch's control-row range is narrower and its median is not higher; that rule is fixed here, before either batch runs.
6. **Protocol docs.** Update `docs/evaluation.md:400-406` to describe the repeat-and-report protocol instead of the 0.5 gate, and `:388` and `:436-440`, which say no timing snapshot is committed, to point at `docs/checker-timing.md`.

## Run procedure

1. Pin a clean commit that contains #68 (the image did not build before it), this branch, and task 1; require green Haskell CI on that exact SHA.
2. Pause Spotlight (`sudo mdutil -a -i off`), quit desktop apps and other agent sessions, and demote remaining noisy processes with `taskpolicy -b -p <pid>`; record the list.
3. `BENCH_ARGS="--quiet-seconds 0 --runs 10" make bench-container`.
4. Optional bias probe (task 4), then the pinned batch (task 5): `BENCH_ARGS="--quiet-seconds 0 --runs 10 --cpuset-cpus 17" make bench-container`.
5. Restore Spotlight (`sudo mdutil -a -i on`) and the demoted processes (`taskpolicy -B -p <pid>`).
6. Run the comparison (task 2) and write `docs/checker-timing.md` with every run, the in-run load, the spread, and the claim limits above.

## Acceptance

- `docs/checker-timing.md` names the commit, host, container image ID, load during every run, and the across-run median and range of the control row; it states the claim limits in "What the numbers may claim".
- `docs/README.md` indexes it; `docs/evaluation.md` no longer describes the 0.5 gate or says no timing snapshot is committed.
- The paper's `tables/performance.tex` is regenerated from the predeclared run, with the commit recorded.
