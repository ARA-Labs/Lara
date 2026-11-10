# Checker timing batches, 2026-11-10

Run record for `docs/checker-timing.md`. Trace nodes: `N425_quiet_window_unreachable`, `N426_bench_repeat_and_report`, `N427_checker_timing_batches`.

- Commit: `018a2ae1e6309351b23f9768f5f1bb2b700a990c` (branch `docs/checker-timing`, PR #69), clean tree; Haskell CI run 42882314673 completed success on that exact SHA.
- Host: Apple M5 Pro, 64 GB RAM, macOS 27.2 (Darwin 27.2.0).
- VM: OrbStack 2.2.5, Docker engine 29.8.2, kernel 7.2.12-orbstack, 18 virtual CPUs; `/sys/devices/system/cpu/isolated` read `17`.
- Image: `sha256:62a8d63db1220caaa072fbe4f2aacc19ee9f25d12d8d8457948d45e100474754` (GHC 9.14.1, Lean 4.32.0).
- Conditions: `--quiet-seconds 0`; Spotlight indexing active; `corespotlightd` (PID 1076) demoted with `taskpolicy -b` for all three batches and restored afterwards; desktop apps open.
- Run directories: `measurements/bench-runs/` on the measuring host (gitignored).

## Failed quiet-window attempts at 9c3f6fa

| Run directory | Status | Load samples | Load min | Load median | Load max |
| --- | --- | ---: | ---: | ---: | ---: |
| `20261110T054940Z-9c3f6fa65f32` | failed: host did not remain below load 0.5 for 120.0s within 3600.0s | 720 | 1.30 | 2.64 | 7.16 |
| `20261110T074841Z-9c3f6fa65f32` | failed: host did not remain below load 0.5 for 120.0s within 3600.0s | 720 | 0.83 | 2.11 | 6.49 |

## `bench_compare.py` output, verbatim

Unpinned, batch `20261110T191630Z`:

```
| Run | Pinned CPUs | Status | Control median (µs) | Load during run (min / median / max) |
| --- | --- | --- | ---: | --- |
| `20261110T191630Z-018a2ae1e630-r01` | - | included | 202.3 | 2.41 / 2.54 / 3.00 |
| `20261110T191657Z-018a2ae1e630-r02` | - | included | 204.1 | 2.84 / 2.92 / 3.08 |
| `20261110T191725Z-018a2ae1e630-r03` | - | included | 204.0 | 2.72 / 2.84 / 2.94 |
| `20261110T191751Z-018a2ae1e630-r04` | - | included | 203.3 | 2.75 / 2.87 / 2.98 |
| `20261110T191818Z-018a2ae1e630-r05` | - | included | 203.6 | 2.76 / 2.82 / 2.98 |
| `20261110T191845Z-018a2ae1e630-r06` (table) | - | included | 201.0 | 2.76 / 2.80 / 2.98 |
| `20261110T191912Z-018a2ae1e630-r07` | - | included | 200.2 | 2.63 / 2.76 / 2.94 |
| `20261110T191938Z-018a2ae1e630-r08` | - | included | 199.5 | 2.63 / 2.82 / 2.94 |
| `20261110T192004Z-018a2ae1e630-r09` | - | included | 199.9 | 2.69 / 2.84 / 2.91 |
| `20261110T192030Z-018a2ae1e630-r10` | - | included | 200.6 | 2.69 / 2.85 / 2.89 |

Across 10 included runs the control-row median is 201.6 µs (range 199.5 to 204.1 µs, 2.3% of the median). Per unit, the range across runs is 5.8% of the unit's median at the median unit and 23.5% at most.
```

Unpinned with four host `yes > /dev/null` loops, batch `20261110T192100Z`:

```
| Run | Pinned CPUs | Status | Control median (µs) | Load during run (min / median / max) |
| --- | --- | --- | ---: | --- |
| `20261110T192100Z-018a2ae1e630-r01` | - | included | 208.0 | 3.03 / 3.83 / 4.30 |
| `20261110T192128Z-018a2ae1e630-r02` (table) | - | included | 213.2 | 4.30 / 4.59 / 4.97 |
| `20261110T192156Z-018a2ae1e630-r03` | - | included | 215.3 | 4.97 / 5.28 / 5.78 |
| `20261110T192224Z-018a2ae1e630-r04` | - | included | 211.6 | 5.78 / 6.13 / 6.27 |
| `20261110T192252Z-018a2ae1e630-r05` | - | included | 214.1 | 6.17 / 6.37 / 6.71 |

Across 5 included runs the control-row median is 213.2 µs (range 208.0 to 215.3 µs, 3.4% of the median). Per unit, the range across runs is 6.6% of the unit's median at the median unit and 12.8% at most.
```

Pinned to VM CPU 17, batch `20261110T192322Z`:

```
| Run | Pinned CPUs | Status | Control median (µs) | Load during run (min / median / max) |
| --- | --- | --- | ---: | --- |
| `20261110T192322Z-018a2ae1e630-r01` | 17 | included | 200.1 | 5.16 / 5.96 / 6.71 |
| `20261110T192349Z-018a2ae1e630-r02` | 17 | included | 199.8 | 3.92 / 4.45 / 5.16 |
| `20261110T192415Z-018a2ae1e630-r03` | 17 | included | 199.6 | 3.38 / 3.64 / 3.92 |
| `20261110T192441Z-018a2ae1e630-r04` | 17 | included | 200.9 | 3.38 / 3.47 / 3.52 |
| `20261110T192507Z-018a2ae1e630-r05` | 17 | included | 199.5 | 3.32 / 3.39 / 3.52 |
| `20261110T192533Z-018a2ae1e630-r06` | 17 | included | 200.3 | 3.20 / 3.39 / 3.59 |
| `20261110T192559Z-018a2ae1e630-r07` | 17 | included | 200.2 | 3.25 / 3.35 / 3.59 |
| `20261110T192626Z-018a2ae1e630-r08` | 17 | included | 199.5 | 3.25 / 3.78 / 4.19 |
| `20261110T192652Z-018a2ae1e630-r09` (table) | 17 | included | 199.6 | 3.36 / 3.56 / 3.70 |
| `20261110T192718Z-018a2ae1e630-r10` | 17 | included | 198.5 | 3.00 / 3.20 / 3.41 |

Across 10 included runs the control-row median is 199.7 µs (range 198.5 to 200.9 µs, 1.2% of the median). Per unit, the range across runs is 3.9% of the unit's median at the median unit and 9.1% at most.
```

## Published table run `20261110T192652Z-018a2ae1e630-r09`, `performance.md` verbatim

```
| | median | worst |
| --- | ---: | ---: |
| Corpus unit, end-to-end (µs) | 437.6 | 472.4 |
| &nbsp;&nbsp;parse (µs) | 238.4 | 248.8 |
| &nbsp;&nbsp;check + render, pre-decoded (µs) | 199.8 | 226.5 |
| &nbsp;&nbsp;validate (µs) | 0.1 | 0.2 |
| &nbsp;&nbsp;check (µs) | 194.0 | 221.4 |
| &nbsp;&nbsp;compile (µs) | 0.0 | 0.6 |
| &nbsp;&nbsp;evaluate (µs) | 0.6 | 1.1 |
| Per-artifact total (27 artifacts, µs) | 878.7 | 1751.4 |
| Framework size (nodes / edges) | 0 / 0 | 2 / 1 |
| Lean reference driver, subprocess (ms) | 1.1 | 1.3 |
| | | |
| 660-record harness, one full pass (ms) | 172.2 |  |
```

## Reading

The batches ran in sequence (unpinned, busy, pinned), so the pinned batch's narrower spread is confounded with time order and with the one-minute load average left by the stopped busy loops. Every busy run was slower than every unpinned run (208.0 µs minimum against 204.1 µs maximum). The selection rule fixed in the plan before the runs (`plans/checker-timing-run.md` as of commit `15c9d45`, removed once executed: keep unpinned unless pinned has a narrower range and a median that is not higher) chose the pinned batch.
