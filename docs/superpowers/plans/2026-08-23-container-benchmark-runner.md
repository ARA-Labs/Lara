# Containerized Publication Benchmark Runner Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce issue #120's publication benchmark from a pinned Linux/arm64 container on the local Apple M5 Pro, with exact-commit CI provenance and a continuously quiet physical host.

**Architecture:** A Python host runner validates source and CI identity, builds a pinned image before timing, enforces the macOS quiet window, and runs a prebuilt benchmark container with no network and one output mount. The existing Haskell benchmark becomes a Cabal executable, retains normal build-preflight behavior, and adds explicit `--prebuilt` and multi-format output modes for the container path. Raw runs remain gitignored; the PR commits the reproducible runner and the dated documentation snapshot.

**Tech Stack:** Python 3 standard library and `unittest`, Haskell/GHC 9.14.1, Cabal, Lean 4.32.0, Elan 4.2.3, Docker/OrbStack on Darwin arm64, GitHub CLI/API, Make.

**Spec:** `docs/superpowers/specs/2026-08-23-container-benchmark-runner-design.md`

## Global Constraints

- The number of record runs in a `linux/arm64` container on the local Apple M5 Pro.
- The macOS one-minute load average must remain below `0.5` for 120 continuous seconds before the timed container starts.
- CI must be completed and successful for the exact measured commit SHA; CI duration is provenance, not a performance measurement.
- Normal `make bench` and direct `scripts/bench.hs` behavior retains the Lean build preflight. Only explicit `--prebuilt` suppresses the build command and requires the existing driver.
- The timed container performs no compilation and has no network access.
- Pin GHC 9.14.1, Lean 4.32.0, Elan 4.2.3, the Elan arm64 asset SHA-256, the Haskell base-image digest, and Linux/arm64 Cabal dependencies.
- Raw timing output remains under gitignored `measurements/bench-runs/`; no timing artifact enters frozen measurements.
- Do not modify checker semantics, wire formats, corpus inputs, mutation suites, replay identity, Lean proofs, or frozen measurements.

---

## Repository and File Map

- `scripts/bench.hs`: add explicit prebuilt and one-measurement/multi-format output contracts; accept trusted host metadata overrides.
- `lara.cabal`: expose `scripts/bench.hs` as `exe:lara-bench` with optimization enabled.
- `scripts/bench_container.py`: exact-SHA CI validation, host quiet gate, image build/run, and provenance finalization.
- `scripts/test_bench_container.py`: deterministic unit tests with fake commands, clocks, and load samples.
- `containers/bench/Dockerfile`: pinned Linux/arm64 build and minimal non-root runtime image.
- `containers/bench/cabal.project`: container-specific project configuration.
- `containers/bench/cabal.project.freeze`: resolved Linux/arm64 dependency lock.
- `.dockerignore`: exclude repository and build state that must not enter the image context.
- `Makefile`: retain `bench`; add `bench-image` and `bench-container` entry points.
- `.github/workflows/ci.yml`: run the Python runner unit tests without requiring Docker.
- `docs/performance.md`: document the container protocol and refresh the dated snapshot after the publication run.
- `docs/superpowers/specs/2026-08-23-container-benchmark-runner-design.md`: approved contract.
- `docs/superpowers/plans/2026-08-23-container-benchmark-runner.md`: execution record.

---

### Task 1: Make the Benchmark Prebuildable and Single-Run Multi-Format

**Files:**
- Modify: `scripts/bench.hs:42-138,303-416,467-535,624-663`
- Modify: `lara.cabal:97-115`

**Interfaces:**
- Consumes: existing benchmark measurement, `renderTable`, and Lean driver path.
- Produces: Cabal component `exe:lara-bench`; options `--prebuilt` and `--output-dir DIR`; environment overrides for the measured Git SHA, physical host CPU/RAM, and pinned GHC/Lean versions.
- Invariant: default invocation still runs the Lean build preflight and writes `measurements/bench.json` plus one selected table.

- [ ] **Step 1: Add failing CLI contract checks**

Before changing the parser, run the current script and record the expected failures:

```bash
cabal exec -- runghc scripts/bench.hs --help
cabal exec -- runghc scripts/bench.hs --output-dir /tmp/lara-bench-contract
```

Expected: help does not list `--prebuilt`, and `--output-dir` exits nonzero as an unknown option.

- [ ] **Step 2: Add the optimized benchmark executable**

Add an `executable lara-bench` stanza with `hs-source-dirs: scripts`, `main-is: bench.hs`, `ghc-options: -O2`, and direct dependencies `base`, `bytestring`, `directory`, `lara`, and `process`. Build it with:

```bash
cabal build exe:lara-bench
```

Expected: PASS with `-Wall`; `cabal list-bin exe:lara-bench` returns an executable path.

- [ ] **Step 3: Extend the option model without changing defaults**

Extend `Options` with:

```haskell
optPrebuilt :: Bool
optOutputDir :: Maybe FilePath
```

Keep `Options FmtText Nothing False Nothing` as the default. Parse `--prebuilt`, `--output-dir=PATH`, and `--output-dir PATH`. Reject an empty output directory and any `--out`/`--output-dir` combination. Update `usage` with both options.

Change the preflight call to:

```haskell
preflightLean (optPrebuilt opts)
```

When `prebuilt` is `False`, retain the current `lake build` call and binary check. When `True`, perform only the binary check and report `bench: Lean driver missing in --prebuilt mode: ...` on failure.

`timeLean` must inspect the driver's `ExitCode`. A nonzero exit aborts with the
unit path and driver stderr; it never contributes a fast timing sample.

- [ ] **Step 4: Emit all formats from one measurement**

Factor output writing so `--output-dir DIR` creates the directory and writes:

```text
bench.json
performance.txt
performance.md
performance.tex
```

All three tables must call `renderTable` over the same `env`, `inputCount`, `units`, and `sweepNs` values. Outside output-directory mode, retain the existing raw path and `--format`/`--out` behavior.

- [ ] **Step 5: Add trusted environment overrides**

Use `lookupEnv` before subprocess probes. `LARA_BENCH_GIT_REV` overrides `git rev-parse HEAD`; `LARA_BENCH_HOST_CPU` overrides the physical CPU label; a decimal `LARA_BENCH_HOST_RAM_BYTES` overrides physical memory. `LARA_BENCH_GHC_VERSION` and `LARA_BENCH_LEAN_VERSION` override compiler probes in the compiler-free runtime image. Reject a present non-decimal RAM override rather than silently recording `null`.

- [ ] **Step 6: Verify the CLI contract**

Run:

```bash
cabal build exe:lara-bench
"$(cabal list-bin exe:lara-bench)" --help
"$(cabal list-bin exe:lara-bench)" --out a --output-dir b
```

Expected: help lists both options; the incompatible-output command exits nonzero with an exact `bench:` diagnostic before any build or measurement.

- [ ] **Step 7: Commit the benchmark CLI change**

```bash
git add scripts/bench.hs lara.cabal
git commit -m "feat(bench): add prebuilt multi-format runner"
```

### Task 2: Implement the Tested Host Provenance Runner

**Files:**
- Create: `scripts/bench_container.py`
- Create: `scripts/test_bench_container.py`

**Interfaces:**
- Consumes: clean Git repository, `gh` JSON, Darwin `os.getloadavg`, `sysctl`, Docker CLI, and the image contract from Task 3.
- Produces: `measurements/bench-runs/<UTC>-<short-SHA>/provenance.json` plus the Docker output mount.
- Key functions: `select_ci_run(runs, sha)`, `wait_for_quiet(load, sleep, monotonic, threshold, seconds)`, `docker_run_command(...)`, `sha256_file(path)`, and `run_publication(args)`.

- [ ] **Step 1: Write CI-selection tests**

Add tests with fixed JSON fixtures proving that `select_ci_run`:

```python
self.assertEqual(select_ci_run([successful], SHA)["databaseId"], 42)
```

and rejects wrong-SHA, pending, failed, skipped, cancelled, and two successful records for the same SHA without an unambiguous newest run.

- [ ] **Step 2: Write quiet-window tests**

Inject fake load samples, clock, and sleep. Prove `[0.4, 0.4, 0.4]` completes the configured window, while `[0.4, 0.6, 0.4, 0.4]` resets the start time at `0.6`. Assert every sample and reset is returned for provenance.

- [ ] **Step 3: Write Docker-command and provenance tests**

Assert the exact command contains:

```text
--platform linux/arm64
--network none
--read-only
--tmpfs /tmp:rw,noexec,nosuid,size=256m
--mount type=bind,src=<absolute-run-dir>,dst=/out
-e LARA_BENCH_GIT_REV=<full-sha>
-e LARA_BENCH_HOST_CPU=<cpu>
-e LARA_BENCH_HOST_RAM_BYTES=<bytes>
-e LARA_BENCH_GHC_VERSION=9.14.1
-e LARA_BENCH_LEAN_VERSION=Lean 4.32.0
```

Test failure finalization, success finalization, required output enumeration, and SHA-256 digests over fixed fixture bytes.

- [ ] **Step 4: Run tests and confirm red behavior**

```bash
python3 -m unittest scripts/test_bench_container.py -v
```

Expected: FAIL because `scripts.bench_container` does not exist.

- [ ] **Step 5: Implement pure orchestration helpers**

Use dataclasses only for immutable records that cross function boundaries. Run external commands with argument arrays, captured UTF-8 output, and contextual `bench-container:` failures. Parse JSON with `json.loads`; never construct provenance through shell interpolation.

Write JSON atomically through a sibling temporary file, `flush`, `os.fsync`, and `os.replace`. Sort object keys and end the file with one newline.

- [ ] **Step 6: Implement the publication state machine**

Implement validation, exact-SHA CI lookup, image build/inspect, run-directory creation, quiet waiting, Docker execution, required-output validation, digest calculation, and success finalization in the order specified by the design. On failure after run-directory creation, atomically persist `status: failed`, `failed_stage`, and `error`, then re-raise for exit 1.

- [ ] **Step 7: Run focused tests**

```bash
python3 -m unittest scripts/test_bench_container.py -v
```

Expected: all tests PASS without Docker, GitHub, sleeps, or network access.

- [ ] **Step 8: Commit the host runner**

```bash
git add scripts/bench_container.py scripts/test_bench_container.py
git commit -m "feat(bench): capture quiet-run provenance"
```

### Task 3: Build the Pinned Linux/arm64 Image

**Files:**
- Create: `containers/bench/Dockerfile`
- Create: `containers/bench/cabal.project`
- Create: `containers/bench/cabal.project.freeze`
- Create: `.dockerignore`

**Interfaces:**
- Consumes: full Git SHA build argument `LARA_GIT_REV`; Task 1's `exe:lara-bench`.
- Produces: non-root runtime image whose entrypoint runs `lara-bench --prebuilt --output-dir /out`.
- Invariant: compilation occurs only in image-build stages; timed runtime has no compiler dependency or network access.

- [ ] **Step 1: Start the local container engine and resolve the immutable base**

Start OrbStack as an operator action, then verify:

```bash
docker version --format '{{.Client.Version}} {{.Server.Version}} {{.Server.Os}}/{{.Server.Arch}}'
docker buildx imagetools inspect haskell:9.14.1-slim-bookworm
```

Select the `linux/arm64` manifest digest and place the exact digest after `haskell:9.14.1-slim-bookworm@sha256:` in the Dockerfile. Do not commit a mutable tag-only `FROM` line.

- [ ] **Step 2: Write the container project and dependency lock**

Create `containers/bench/cabal.project` with the repository package, optimization level 2, and tests disabled. Generate `containers/bench/cabal.project.freeze` inside the selected Linux/arm64 base image so its solver result matches the target platform. Re-run the same freeze command and require an empty diff.

- [ ] **Step 3: Write the multi-stage Dockerfile**

The build stage verifies Elan v4.2.3's arm64 asset against:

```text
cb69af0803b04157bc30201c29c12fca882bb3ad8b43476b8d2d3064810bc3ac
```

It installs `leanprover/lean4:v4.32.0`, builds `exe:lara`, `exe:lara-bench`, and `lean/.lake/build/bin/lara-driver`, and copies runtime corpus/manifests plus binaries into a minimal final stage. The final stage creates an unprivileged `lara` user and uses:

```dockerfile
ENTRYPOINT ["/usr/local/bin/lara-bench", "--prebuilt", "--output-dir", "/out"]
```

- [ ] **Step 4: Exclude mutable host state**

Create `.dockerignore` entries for `.git`, `.worktrees`, `dist-newstyle`, `lean/.lake`, `measurements`, caches, coverage, editor state, and OS metadata. Keep all corpus, fixture, source, and manifest inputs required by the benchmark.

- [ ] **Step 5: Build and inspect the image**

```bash
docker build --platform linux/arm64 \
  --build-arg LARA_GIT_REV="$(git rev-parse HEAD)" \
  -f containers/bench/Dockerfile \
  -t lara-bench:smoke .
docker image inspect lara-bench:smoke
```

Expected: build succeeds; architecture is arm64; no unpinned base warning; entrypoint is the prebuilt output-directory command.

- [ ] **Step 6: Smoke the runtime boundary**

Run with network disabled, a read-only root, temporary `/tmp`, and a fresh output directory. Expected: all four benchmark files are written; no build command runs; the process exits 0.

- [ ] **Step 7: Commit the pinned image**

```bash
git add .dockerignore containers/bench
git commit -m "build(bench): pin the arm64 measurement image"
```

### Task 4: Wire Developer Entry Points and Documentation

**Files:**
- Modify: `Makefile:4-34`
- Modify: `.github/workflows/ci.yml:73-87`
- Modify: `docs/performance.md:1-50,78-108`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: `make bench`, `make bench-image`, `make bench-container`, and a CI unit-test gate.
- Invariant: `make bench` remains the native developer path; container results are identified as a distinct protocol.

- [ ] **Step 1: Wire Make targets**

Change `bench` to build and invoke `exe:lara-bench` while retaining the Lean build. Add:

```make
bench-image:
	docker build --platform linux/arm64 ...

bench-container:
	python3 scripts/bench_container.py
```

Pass optional `BENCH_ARGS` only after the fixed script path; do not assemble JSON or shell snippets in Make.

- [ ] **Step 2: Add the runner unit test to CI**

After existing Python unit tests, run:

```yaml
- name: Container benchmark runner unit tests
  run: python3 -m unittest scripts/test_bench_container.py -v
```

CI does not build or execute Docker and does not publish timing numbers.

- [ ] **Step 3: Document the protocol before measuring**

Update `docs/performance.md` with the native/container distinction, exact-SHA CI requirement, quiet-window rule, output directory, and commands. Leave the numeric snapshot unchanged until Task 6.

- [ ] **Step 4: Run focused and full pre-PR gates**

```bash
python3 -m unittest scripts/test_bench_container.py -v
make test
make presentation-parity
```

Expected: PASS. Confirm no diff under corpus, fixtures, bundles, examples, `measurements/frozen`, or Lean source.

- [ ] **Step 5: Commit the integration**

```bash
git add Makefile .github/workflows/ci.yml docs/performance.md
git commit -m "docs(bench): document the container protocol"
```

### Task 5: Open the PR and Establish Exact-Commit CI Provenance

**Files:**
- No source changes.
- Remote: issue #120 and a new pull request.

**Interfaces:**
- Consumes: infrastructure commit from Tasks 1–4.
- Produces: open PR and successful exact-SHA CI run used by the publication runner.

- [ ] **Step 1: Push the branch and create the PR**

Push `bench/120-container-publication-run`, create a PR against `main`, and explain that the first commit set is infrastructure. Include the native/container protocol distinction and `Refs #120`.

- [ ] **Step 2: Wait for exact infrastructure SHA checks**

Run:

```bash
gh pr checks --watch
gh run list --commit "$(git rev-parse HEAD)" --workflow CI
```

Expected: every required PR check passes for the exact infrastructure SHA.

- [ ] **Step 3: Record the immutable measured SHA**

Save the full infrastructure SHA before changing documentation. The publication runner must report the same SHA and CI run URL in `provenance.json`.

### Task 6: Execute the Quiet Publication Run and Refresh Consumers

**Files:**
- Generated, ignored: `measurements/bench-runs/<UTC>-<SHA>/*`
- Modify: `docs/performance.md:51-83`
- Modify: PR body and issue #120 comment.

**Interfaces:**
- Consumes: exact green infrastructure SHA and the pinned image.
- Produces: successful provenance record, raw benchmark, three table formats, refreshed repository snapshot, and paper-ready replacement text.

- [ ] **Step 1: Execute the default publication protocol**

```bash
make bench-container
```

Expected: the runner builds before waiting, observes 120 continuous seconds below load `0.5`, runs one networkless prebuilt container, and writes a successful run directory.

- [ ] **Step 2: Validate internal agreement**

Check that `bench.json`, `performance.md`, and `performance.tex` report identical values, the setting identifies Apple M5 Pro plus Linux/arm64, the full Git SHA matches the infrastructure commit, the CI URL resolves to its successful exact-SHA run, and every digest in `provenance.json` matches its file.

- [ ] **Step 3: Refresh the dated snapshot**

Replace `docs/performance.md`'s native snapshot table and interpretation with the container run. Preserve the historical explanation of why rendered timing tables are not committed. State explicitly that the old `~203 µs` native control and new container control belong to different settings.

- [ ] **Step 4: Prepare the paper update**

Use the generated `performance.tex` verbatim. Replace:

```text
Decoding dominates. The median corpus unit takes about \qty{1.5}{\milli\second} end to end, and wire parsing consumes roughly seven eighths of that time.
```

with a two-sentence paragraph grounded in the measured parse and pre-decoded check-plus-render values. Mention the pinned Linux/arm64 container on Apple M5 Pro and derive no Haskell/Lean cross-driver ratio.

- [ ] **Step 5: Commit only the repository snapshot**

```bash
git add docs/performance.md
git commit -m "docs(bench): record the container publication run"
```

Confirm the diff from the measured infrastructure commit touches only `docs/performance.md`.

- [ ] **Step 6: Update the PR and issue**

Add the measured SHA, exact CI run, image ID, provenance digest, complete LaTeX table, and paper paragraph to the PR body. Add the same result to #120 and leave the issue open until the PR merges and the paper copy is applied.

### Task 7: Final Verification and Delivery

**Files:**
- Verify all modified files.

**Interfaces:**
- Consumes: final branch and publication artifacts.
- Produces: green final PR head and auditable delivery report.

- [ ] **Step 1: Run focused and repository verification**

```bash
python3 -m unittest scripts/test_bench_container.py -v
make test
make presentation-parity
```

Run the container smoke path against the final image without replacing the publication run. Expected: all gates pass.

- [ ] **Step 2: Push and verify exact final-head CI**

Push the documentation commit and run:

```bash
gh pr checks --watch
gh run list --commit "$(git rev-parse HEAD)" --workflow CI
```

Expected: successful CI for the exact final PR head.

- [ ] **Step 3: Review the final diff boundary**

Confirm no changes under checker source, Lean proofs, corpus, fixtures, bundles, examples, replay artifacts, or frozen measurements. Confirm generated run artifacts remain untracked and ignored.

- [ ] **Step 4: Report delivery**

Report the PR URL, measured infrastructure SHA, exact CI URL, final-head CI URL, image ID, run-directory path, provenance digest, quiet-window evidence, headline timing values, and the paper-ready table/prose location.
