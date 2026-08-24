# Containerized Publication Benchmark Runner

Status: approved in conversation on 2026-08-23 for issue #120.

## Goal

Produce the performance table for issue #120 from a pinned Linux/arm64 container on the local Apple M5 Pro. The run must identify the measured source commit, require successful CI for that exact commit, separate compilation from timing, enforce the issue's quiet-machine protocol on the physical host, and retain enough provenance to audit the result.

The LARA pull request owns the runner, the dated repository snapshot, and the generated measurement record. The paper repository is outside this checkout. The pull request and issue comment therefore carry a ready-to-paste LaTeX table and an exact replacement for the obsolete “Decoding dominates” paragraph.

## Measurement Boundary

The publication number comes from one invocation of the prebuilt benchmark executable inside a Linux/arm64 container. The container image contains the LARA source tree, the compiled Haskell benchmark, the production Haskell executable, and the compiled Lean reference driver. The timed container invocation performs no compilation and has no network access.

The physical machine remains part of the measurement setting. A container pins the software environment but does not isolate the guest from host scheduling, thermal state, or background load. The host runner therefore waits until the macOS one-minute load average remains below `0.5` for 120 continuous seconds. An excursion resets the timer.

This protocol establishes a new Linux/arm64-container setting on an Apple M5 Pro. Its latencies must not be compared directly with the existing native-Darwin `~203 µs` control. The table, documentation, and paper prose must identify the container setting.

## Source and CI Identity

The measured tree must be a clean Git commit. The host runner resolves the full `HEAD` SHA and refuses modified or untracked files.

Before building the image, the runner queries GitHub Actions for workflow `CI` at that exact SHA. It accepts only a completed successful run. The runner records:

- repository and full commit SHA;
- workflow run ID, URL, conclusion, event, creation time, start time, and completion time;
- each job's name, conclusion, runner labels, start time, and completion time;
- the UTC time at which the runner fetched the CI record.

CI duration is provenance, not benchmark input. GitHub-hosted runner timing never substitutes for the local performance measurement.

The measured commit and the final documentation commit are necessarily distinct. The infrastructure commit is pushed and passes CI first. The benchmark runs against that commit. A later documentation-only commit records its numbers. The snapshot states the measured infrastructure SHA, and the final PR check confirms that the documentation commit changes no benchmarked source.

## Container Contract

Add `containers/bench/Dockerfile` and `containers/bench/cabal.project`. The Dockerfile must:

- target `linux/arm64`;
- pin the Haskell base image by immutable digest;
- use GHC 9.14.1;
- install Elan v4.2.3 from the `aarch64-unknown-linux-gnu` release asset and verify SHA-256 `cb69af0803b04157bc30201c29c12fca882bb3ad8b43476b8d2d3064810bc3ac`;
- install the repository-pinned Lean toolchain `leanprover/lean4:v4.32.0`;
- consume a committed Linux/arm64 Cabal freeze file associated with `containers/bench/cabal.project`;
- build `exe:lara`, `exe:lara-bench`, and the Lean driver during image construction;
- copy only runtime inputs and compiled binaries into the final image;
- run as a non-root user;
- expose no network-dependent runtime step.

Add `.dockerignore` rules that exclude `.git`, worktrees, local build output, measurements, caches, and editor state from the image context. The host runner passes the full measured commit as an immutable image build argument. The benchmark records that value rather than trying to inspect `.git` inside the image.

The timed `docker run` uses `--network none`, `--read-only`, a temporary `/tmp`, and one writable bind mount at `/out`. The runner records the image ID, Docker client and server versions, Docker architecture, assigned CPU count and memory, and the exact command.

## Benchmark Executable Contract

Promote `scripts/bench.hs` to the `lara-bench` Cabal executable while retaining direct script use for developers.

Normal behavior stays unchanged:

- `make bench` builds `exe:lara`, `exe:lara-bench`, and the Lean driver before running;
- a direct benchmark invocation without `--prebuilt` runs the existing Lean build preflight;
- the default raw record remains `measurements/bench.json`;
- `--format` and `--out` retain their current behavior.

The container adds two explicit options:

- `--prebuilt`: skip the Lean build command and require the already-built Lean driver. This flag is the only path that suppresses the build preflight.
- `--output-dir DIR`: create `DIR` and write `bench.json`, `performance.txt`, `performance.md`, and `performance.tex` from the same in-memory measurement. It is incompatible with `--out`; `--format` is ignored only when the caller explicitly requests the multi-format output directory.

The benchmark reads five optional environment overrides supplied by the trusted host runner or pinned image:

- `LARA_BENCH_GIT_REV`: full measured commit SHA;
- `LARA_BENCH_HOST_CPU`: physical host CPU model;
- `LARA_BENCH_HOST_RAM_BYTES`: physical host memory in bytes;
- `LARA_BENCH_GHC_VERSION`: GHC version used to build the benchmark;
- `LARA_BENCH_LEAN_VERSION`: Lean version used to build the reference driver.

Without overrides, normal host execution gathers the same values locally. The raw JSON continues to contain the measured rows and gains no GitHub or Docker dependency. CI and container provenance remain in the separate host-generated `provenance.json`.

## Host Runner

Add `scripts/bench_container.py`, using only the Python standard library. Its default command performs the publication protocol. Test-only and developer controls remain explicit flags:

- `--skip-ci` permits a local smoke run and is recorded in provenance;
- `--quiet-seconds N` defaults to `120`;
- `--load-threshold X` defaults to `0.5`;
- `--image TAG` reuses a named image only when the caller also selects the explicit no-build path;
- `--output-root PATH` defaults to `measurements/bench-runs`.

The runner executes these stages in order:

1. Validate Darwin/arm64 host, clean Git tree, Docker availability, and GitHub authentication.
2. Resolve and validate exact-commit CI unless `--skip-ci` is present.
3. Build the pinned `linux/arm64` image and record its ID.
4. Create `measurements/bench-runs/<UTC>-<short-SHA>/` and atomically write initial provenance.
5. Wait for the continuous quiet window, recording every sampled load average and every reset.
6. Capture the pre-run host state and execute the read-only, networkless container once.
7. Capture post-run host state, hash every generated output, mark the provenance record successful, and atomically replace it.

A failed stage leaves the run directory with `status: failed`, the failed stage, diagnostic text, and all provenance collected before failure. It never labels an incomplete or noisy run successful.

The runner must not start or reconfigure Docker Desktop or OrbStack. It reports a stopped daemon with a concrete command for the operator. Starting a desktop runtime is an operator action outside the script's trust boundary.

## Generated Artifacts

A successful run directory contains:

- `provenance.json`: source, exact CI, host, Docker, quiet-window, command, timestamps, status, and output digests;
- `bench.json`: raw benchmark data from `lara-bench`;
- `performance.txt`: aligned terminal table;
- `performance.md`: Markdown table;
- `performance.tex`: LaTeX table.

The directory remains gitignored under the existing `measurements/*` rule. The PR commits only the runner, container definition, dependency lock, tests, Makefile/Cabal wiring, and the refreshed dated snapshot in `docs/performance.md`.

The PR body and #120 comment include:

1. the measured commit and CI run URL;
2. the container image ID and provenance artifact digest;
3. the complete generated LaTeX table;
4. a replacement for the old paper sentence beginning “Decoding dominates.”

The replacement prose states the measured check-plus-render and parse values, avoids a cross-driver ratio, identifies the Linux/arm64 container setting, and says that decoding and checking are the same order only if the measured numbers support that statement.

## Validation and Failure Handling

The host runner rejects:

- a dirty or uncommitted tree;
- no CI run for the exact SHA;
- pending, failed, cancelled, or skipped exact-SHA CI;
- a stopped or non-arm64 Docker engine;
- an unpinned base-image reference;
- missing expected binaries in the image;
- a nonzero Lean reference-driver exit for any measured unit;
- a quiet-window timeout or interruption;
- a container failure;
- a missing output file;
- malformed benchmark JSON;
- an output digest mismatch while finalizing provenance.

The benchmark executable rejects `--prebuilt` when the Lean driver is absent. Normal invocation continues to run the Lean build preflight. `--output-dir` never partially replaces an existing successful run directory: the host runner creates a fresh directory, and benchmark files are written only inside it.

## Tests

Add Python unit tests for observable orchestration contracts:

- exact-SHA successful CI selection;
- rejection of wrong-SHA, pending, failed, and ambiguous CI records;
- quiet-window completion and reset after an excursion;
- deterministic Docker command construction with network, read-only, temporary, architecture, environment, and output-mount constraints;
- provenance failure and success finalization;
- output-file and SHA-256 validation.

Exercise the benchmark CLI behaviorally:

- normal `--help` lists `--prebuilt` and `--output-dir`;
- unknown and incompatible options fail;
- `--prebuilt` rejects a missing Lean driver, and any nonzero Lean driver exit aborts the run;
- a container smoke run emits all five required artifacts from one measurement.

Final verification runs the focused Python tests, the Haskell suite, the container build, the container smoke run with `--skip-ci --quiet-seconds 0`, exact infrastructure-commit CI, the quiet publication run, and final PR-head CI.

## Non-goals

- Do not use GitHub-hosted runner duration as a performance number.
- Do not claim that a container isolates host scheduling or thermal state.
- Do not compare the container control directly with the native-Darwin snapshot.
- Do not commit raw timing artifacts under `measurements/`.
- Do not add a general deployment or container platform for LARA.
- Do not modify checker semantics, wire formats, corpus inputs, mutation suites, replay identity, Lean proofs, or frozen measurements.
