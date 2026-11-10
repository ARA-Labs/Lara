#!/usr/bin/env python3
"""Behavioral and orchestration tests for the publication benchmark runner."""

from __future__ import annotations

import hashlib
import io
import json
import os
import subprocess
import sys
import tempfile
import threading
import unittest
from contextlib import ExitStack, redirect_stderr
from pathlib import Path
from unittest.mock import patch

from scripts.bench_compare import CompareError, compare
from scripts.bench_container import (
    BenchError,
    compact_docker_metadata,
    docker_run_command,
    image_metadata,
    main,
    parse_args,
    parse_cpu_list,
    require_isolated_cpus,
    run_publication,
    run_with_load_samples,
    select_ci_run,
    validate_outputs,
    wait_for_quiet,
)


ROOT = Path(__file__).resolve().parents[1]


class BenchCliContractTests(unittest.TestCase):
    def run_bench(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["cabal", "run", "exe:lara-bench", "--", *args],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )

    def stub_publication_dependencies(self, stack: ExitStack) -> None:
        stack.enter_context(
            patch("scripts.bench_container.run_command", return_value=str(ROOT))
        )
        stack.enter_context(
            patch("scripts.bench_container.platform.system", return_value="Darwin")
        )
        stack.enter_context(
            patch("scripts.bench_container.platform.machine", return_value="arm64")
        )
        stack.enter_context(
            patch("scripts.bench_container.require_clean_tree", return_value=SHA)
        )
        stack.enter_context(
            patch(
                "scripts.bench_container.host_metadata",
                return_value={"cpu": "test CPU", "ram_bytes": 1},
            )
        )
        stack.enter_context(
            patch("scripts.bench_container.docker_metadata", return_value={})
        )
        stack.enter_context(
            patch(
                "scripts.bench_container.image_metadata",
                return_value={"id": IMAGE_ID},
            )
        )

    def test_help_lists_container_contract(self) -> None:
        result = self.run_bench("--help")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("--prebuilt", result.stdout)
        self.assertIn("--output-dir", result.stdout)

    def test_output_modes_are_mutually_exclusive(self) -> None:
        result = self.run_bench("--out", "one", "--output-dir", "two")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot combine --out with --output-dir", result.stderr)

    def test_rejects_failed_lean_driver(self) -> None:
        binary = subprocess.run(
            ["cabal", "list-bin", "exe:lara-bench"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        with tempfile.TemporaryDirectory() as raw_dir:
            work = Path(raw_dir)
            os.symlink(ROOT / "fixtures", work / "fixtures", target_is_directory=True)
            os.symlink(ROOT / "corpus-units", work / "corpus-units", target_is_directory=True)
            lean_driver = work / "lean/.lake/build/bin/lara-driver"
            lean_driver.parent.mkdir(parents=True)
            lean_driver.write_text("#!/bin/sh\nexit 7\n", encoding="utf-8")
            lean_driver.chmod(0o755)
            result = subprocess.run(
                [binary, "--prebuilt", "--output-dir", str(work / "out")],
                cwd=work,
                check=False,
                capture_output=True,
                text=True,
                env={
                    **os.environ,
                    "LARA_BENCH_GIT_REV": SHA,
                    "LARA_BENCH_HOST_CPU": "test CPU",
                    "LARA_BENCH_HOST_RAM_BYTES": "1",
                    "LARA_BENCH_GHC_VERSION": "9.14.1",
                    "LARA_BENCH_LEAN_VERSION": "Lean 4.32.0",
                },
            )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Lean driver failed with exit 7", result.stderr)

    def test_missing_host_tool_uses_cli_error_contract(self) -> None:
        result = subprocess.run(
            [sys.executable, str(ROOT / "scripts/bench_container.py"), "--skip-ci"],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            env={**os.environ, "PATH": ""},
        )
        self.assertEqual(result.returncode, 1)
        self.assertIn("bench-container:", result.stderr)
        self.assertIn("git", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_no_build_requires_smoke_mode(self) -> None:
        with self.assertRaisesRegex(BenchError, "--no-build requires --skip-ci"):
            run_publication(parse_args(["--no-build"]))

    def test_unusable_output_root_uses_cli_error_contract(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            output_root = Path(raw_dir) / "not-a-directory"
            output_root.write_text("blocked", encoding="utf-8")
            stderr = io.StringIO()
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                with redirect_stderr(stderr):
                    try:
                        exit_code = main(
                            [
                                "--skip-ci",
                                "--no-build",
                                "--image",
                                "lara-bench:test",
                                "--output-root",
                                str(output_root),
                            ]
                        )
                    except OSError as error:
                        self.fail(f"filesystem error escaped CLI contract: {error}")
        self.assertEqual(exit_code, 1)
        self.assertIn("bench-container:", stderr.getvalue())
        self.assertIn("benchmark run directory", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())

    def test_initial_provenance_error_uses_cli_error_contract(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            stderr = io.StringIO()
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                write_provenance = stack.enter_context(
                    patch(
                        "scripts.bench_container.write_json_atomic",
                        side_effect=PermissionError("denied"),
                    )
                )
                with redirect_stderr(stderr):
                    try:
                        exit_code = main(
                            [
                                "--skip-ci",
                                "--no-build",
                                "--image",
                                "lara-bench:test",
                                "--output-root",
                                raw_dir,
                            ]
                        )
                    except OSError as error:
                        self.fail(f"filesystem error escaped CLI contract: {error}")
        self.assertEqual(exit_code, 1)
        self.assertEqual(write_provenance.call_count, 1)
        self.assertIn("bench-container:", stderr.getvalue())
        self.assertIn("initialize benchmark provenance", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())

    def test_interrupt_finalizes_quiet_window_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                stack.enter_context(
                    patch(
                        "scripts.bench_container.os.getloadavg",
                        return_value=(0.6, 0.6, 0.6),
                    )
                )
                stack.enter_context(
                    patch(
                        "scripts.bench_container.time.monotonic",
                        side_effect=[0.0, 0.0],
                    )
                )
                stack.enter_context(
                    patch(
                        "scripts.bench_container.time.sleep",
                        side_effect=KeyboardInterrupt,
                    )
                )
                with self.assertRaises(KeyboardInterrupt):
                    run_publication(
                        parse_args(
                            [
                                "--skip-ci",
                                "--no-build",
                                "--image",
                                "lara-bench:test",
                                "--output-root",
                                raw_dir,
                            ]
                        )
                    )
            run_dirs = list(Path(raw_dir).iterdir())
            self.assertEqual(len(run_dirs), 1)
            provenance = json.loads(
                (run_dirs[0] / "provenance.json").read_text(encoding="utf-8")
            )
        self.assertEqual(provenance["status"], "failed")
        self.assertEqual(provenance["failed_stage"], "quiet-window")
        self.assertEqual(provenance["error"], "interrupted")
        self.assertEqual(len(provenance["quiet_window"]["events"]), 1)
        self.assertEqual(provenance["quiet_window"]["events"][0]["load_1m"], 0.6)

    def test_interrupt_uses_cli_exit_semantics(self) -> None:
        stderr = io.StringIO()
        with patch("scripts.bench_container.run_publication", side_effect=KeyboardInterrupt):
            with redirect_stderr(stderr):
                try:
                    exit_code = main([])
                except KeyboardInterrupt:
                    self.fail("KeyboardInterrupt escaped CLI contract")
        self.assertEqual(exit_code, 130)
        self.assertIn("bench-container: interrupted", stderr.getvalue())
        self.assertNotIn("Traceback", stderr.getvalue())

    def test_batch_records_every_run_with_load_during_the_run(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                stack.enter_context(
                    patch("scripts.bench_container.validate_outputs", return_value={})
                )
                stack.enter_context(
                    patch(
                        "scripts.bench_container.os.getloadavg",
                        return_value=(1.25, 1.0, 1.0),
                    )
                )
                run_dirs = run_publication(
                    parse_args(
                        [
                            "--skip-ci",
                            "--no-build",
                            "--image",
                            "lara-bench:test",
                            "--quiet-seconds",
                            "0",
                            "--runs",
                            "3",
                            "--batch-note",
                            "spotlight paused",
                            "--output-root",
                            raw_dir,
                        ]
                    )
                )
            provenances = [
                json.loads((run_dir / "provenance.json").read_text(encoding="utf-8"))
                for run_dir in run_dirs
            ]
        self.assertEqual(len(run_dirs), 3)
        self.assertEqual(len({run_dir.name for run_dir in run_dirs}), 3)
        self.assertEqual([p["batch"]["index"] for p in provenances], [1, 2, 3])
        self.assertEqual(len({p["batch"]["id"] for p in provenances}), 1)
        for provenance in provenances:
            self.assertEqual(provenance["status"], "success")
            self.assertEqual(provenance["batch"]["note"], "spotlight paused")
            self.assertIsNone(provenance["cpuset"])
            samples = provenance["benchmark"]["load_samples"]
            self.assertGreaterEqual(len(samples), 2)
            self.assertTrue(all(sample["load_1m"] == 1.25 for sample in samples))

    def test_failed_run_stops_the_batch_and_keeps_its_load_samples(self) -> None:
        def command(arguments, cwd=None, env=None):  # noqa: ANN001
            if arguments[:2] == ["docker", "run"]:
                raise BenchError("container exited 1")
            return str(ROOT)

        with tempfile.TemporaryDirectory() as raw_dir:
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                stack.enter_context(
                    patch("scripts.bench_container.run_command", side_effect=command)
                )
                with self.assertRaisesRegex(BenchError, "container exited 1"):
                    run_publication(
                        parse_args(
                            [
                                "--skip-ci",
                                "--no-build",
                                "--image",
                                "lara-bench:test",
                                "--quiet-seconds",
                                "0",
                                "--runs",
                                "3",
                                "--output-root",
                                raw_dir,
                            ]
                        )
                    )
            run_dirs = list(Path(raw_dir).iterdir())
            provenance = json.loads(
                (run_dirs[0] / "provenance.json").read_text(encoding="utf-8")
            )
        self.assertEqual(len(run_dirs), 1)
        self.assertEqual(provenance["status"], "failed")
        self.assertEqual(provenance["failed_stage"], "benchmark")
        self.assertGreaterEqual(len(provenance["benchmark"]["load_samples"]), 2)

    def test_refuses_to_pin_a_cpu_the_vm_does_not_isolate(self) -> None:
        def command(arguments, cwd=None, env=None):  # noqa: ANN001
            if arguments[-1] == "/sys/devices/system/cpu/isolated":
                return "17"
            if arguments[-1] == "/proc/cmdline":
                return "isolcpus=17"
            return str(ROOT)

        with tempfile.TemporaryDirectory() as raw_dir:
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                stack.enter_context(
                    patch("scripts.bench_container.run_command", side_effect=command)
                )
                with self.assertRaisesRegex(BenchError, "not isolated"):
                    run_publication(
                        parse_args(
                            [
                                "--skip-ci",
                                "--no-build",
                                "--image",
                                "lara-bench:test",
                                "--cpuset-cpus",
                                "16",
                                "--output-root",
                                raw_dir,
                            ]
                        )
                    )
            self.assertEqual(list(Path(raw_dir).iterdir()), [])

    def test_pinned_run_records_the_guest_isolation_it_checked(self) -> None:
        commands = []

        def command(arguments, cwd=None, env=None):  # noqa: ANN001
            commands.append(list(arguments))
            if arguments[-1] == "/sys/devices/system/cpu/isolated":
                return "17"
            if arguments[-1] == "/proc/cmdline":
                return "quiet isolcpus=17"
            return str(ROOT)

        with tempfile.TemporaryDirectory() as raw_dir:
            with ExitStack() as stack:
                self.stub_publication_dependencies(stack)
                stack.enter_context(
                    patch("scripts.bench_container.run_command", side_effect=command)
                )
                stack.enter_context(
                    patch("scripts.bench_container.validate_outputs", return_value={})
                )
                (run_dir,) = run_publication(
                    parse_args(
                        [
                            "--skip-ci",
                            "--no-build",
                            "--image",
                            "lara-bench:test",
                            "--quiet-seconds",
                            "0",
                            "--cpuset-cpus",
                            "17",
                            "--output-root",
                            raw_dir,
                        ]
                    )
                )
            provenance = json.loads((run_dir / "provenance.json").read_text(encoding="utf-8"))
        self.assertEqual(provenance["cpuset"]["cpus"], [17])
        self.assertEqual(provenance["cpuset"]["guest_isolated"], "17")
        self.assertEqual(provenance["cpuset"]["guest_cmdline"], "quiet isolcpus=17")
        timed = [c for c in commands if c[:2] == ["docker", "run"] and "--entrypoint" not in c]
        self.assertEqual(len(timed), 1)
        self.assertEqual(timed[0][-3:], ["--cpuset-cpus", "17", IMAGE_ID])

    def test_rejects_an_empty_batch(self) -> None:
        with self.assertRaisesRegex(BenchError, "--runs must be at least 1"):
            run_publication(parse_args(["--runs", "0"]))


SHA = "a" * 40
IMAGE_ID = "sha256:" + "1" * 64


def ci_run(
    *,
    sha: str = SHA,
    status: str = "completed",
    conclusion: str = "success",
    database_id: int = 42,
    created_at: str = "2026-08-24T00:00:00Z",
) -> dict[str, object]:
    return {
        "databaseId": database_id,
        "headSha": sha,
        "status": status,
        "conclusion": conclusion,
        "createdAt": created_at,
        "url": f"https://example.test/runs/{database_id}",
    }


class CiSelectionTests(unittest.TestCase):
    def test_selects_completed_success_for_exact_sha(self) -> None:
        self.assertEqual(select_ci_run([ci_run()], SHA)["databaseId"], 42)

    def test_rejects_wrong_sha(self) -> None:
        with self.assertRaisesRegex(BenchError, "exact commit"):
            select_ci_run([ci_run(sha="b" * 40)], SHA)

    def test_rejects_non_successful_exact_sha(self) -> None:
        for status, conclusion in [
            ("queued", ""),
            ("in_progress", ""),
            ("completed", "failure"),
            ("completed", "cancelled"),
            ("completed", "skipped"),
        ]:
            with self.subTest(status=status, conclusion=conclusion):
                with self.assertRaisesRegex(BenchError, "successful"):
                    select_ci_run(
                        [ci_run(status=status, conclusion=conclusion)],
                        SHA,
                    )

    def test_selects_unambiguous_newest_success(self) -> None:
        older = ci_run(database_id=41, created_at="2026-08-23T23:00:00Z")
        newer = ci_run(database_id=42, created_at="2026-08-24T00:00:00Z")
        self.assertEqual(select_ci_run([older, newer], SHA)["databaseId"], 42)

    def test_rejects_tied_successes(self) -> None:
        with self.assertRaisesRegex(BenchError, "ambiguous"):
            select_ci_run(
                [ci_run(database_id=41), ci_run(database_id=42)],
                SHA,
            )


class FakeClock:
    def __init__(self) -> None:
        self.now = 0.0

    def monotonic(self) -> float:
        return self.now

    def sleep(self, seconds: float) -> None:
        self.now += seconds


class QuietWindowTests(unittest.TestCase):
    def test_completes_after_continuous_quiet_window(self) -> None:
        clock = FakeClock()
        loads = iter([0.4, 0.4, 0.4])
        events = wait_for_quiet(
            lambda: next(loads),
            clock.sleep,
            clock.monotonic,
            threshold=0.5,
            quiet_seconds=10,
            sample_interval=5,
        )
        self.assertEqual([event["load_1m"] for event in events], [0.4, 0.4, 0.4])
        self.assertEqual(events[-1]["elapsed_quiet_seconds"], 10)

    def test_excursion_resets_quiet_window(self) -> None:
        clock = FakeClock()
        loads = iter([0.4, 0.6, 0.4, 0.4, 0.4])
        events = wait_for_quiet(
            lambda: next(loads),
            clock.sleep,
            clock.monotonic,
            threshold=0.5,
            quiet_seconds=10,
            sample_interval=5,
        )
        self.assertTrue(events[1]["reset"])
        self.assertEqual(events[-1]["monotonic_seconds"], 20)

    def test_timeout_retains_collected_samples(self) -> None:
        clock = FakeClock()
        with self.assertRaisesRegex(BenchError, "within 10s") as caught:
            wait_for_quiet(
                lambda: 0.6,
                clock.sleep,
                clock.monotonic,
                threshold=0.5,
                quiet_seconds=10,
                sample_interval=5,
                max_wait_seconds=10,
            )
        self.assertTrue(
            hasattr(caught.exception, "events"),
            "quiet-window timeout must carry collected samples",
        )
        events = getattr(caught.exception, "events", [])
        self.assertEqual([event["monotonic_seconds"] for event in events], [0.0, 5.0, 10.0])


class LoadSamplingTests(unittest.TestCase):
    def test_samples_bracket_the_action_and_continue_while_it_runs(self) -> None:
        clock = FakeClock()
        sampled_during = threading.Event()
        calls = []

        def load() -> float:
            calls.append(len(calls))
            if len(calls) >= 3:
                sampled_during.set()
            return float(len(calls))

        samples: list[dict[str, object]] = []
        events: list[str] = []

        def action() -> str:
            events.append(f"start after {len(samples)} samples")
            self.assertTrue(sampled_during.wait(5), "sampler did not run during the action")
            return "done"

        result = run_with_load_samples(
            action, samples, load_average=load, monotonic=clock.monotonic, interval=0.001
        )
        self.assertEqual(result, "done")
        self.assertEqual(events, ["start after 1 samples"])
        self.assertGreaterEqual(len(samples), 3)
        self.assertEqual([sample["load_1m"] for sample in samples], sorted(s["load_1m"] for s in samples))

    def test_failed_action_still_gets_a_closing_sample(self) -> None:
        samples: list[dict[str, object]] = []

        def action() -> None:
            raise BenchError("boom")

        with self.assertRaisesRegex(BenchError, "boom"):
            run_with_load_samples(
                action, samples, load_average=lambda: 2.0, monotonic=lambda: 0.0, interval=60
            )
        self.assertEqual(len(samples), 2)


class CpuIsolationTests(unittest.TestCase):
    def test_parses_linux_cpu_lists(self) -> None:
        self.assertEqual(parse_cpu_list("17"), [17])
        self.assertEqual(parse_cpu_list("2-3,17"), [2, 3, 17])
        self.assertEqual(parse_cpu_list(""), [])
        self.assertEqual(parse_cpu_list("\n"), [])
        for bad in ["a", "3-1", "-1", "1-x"]:
            with self.subTest(bad=bad):
                with self.assertRaisesRegex(BenchError, "invalid CPU list"):
                    parse_cpu_list(bad)

    def test_accepts_only_isolated_cpus(self) -> None:
        self.assertEqual(require_isolated_cpus("17", "17"), [17])
        self.assertEqual(require_isolated_cpus("16-17", "16-17"), [16, 17])
        with self.assertRaisesRegex(BenchError, "not isolated.*16"):
            require_isolated_cpus("16-17", "17")
        with self.assertRaisesRegex(BenchError, "not isolated"):
            require_isolated_cpus("17", "")
        with self.assertRaisesRegex(BenchError, "names no CPU"):
            require_isolated_cpus(",", "17")


class DockerCommandTests(unittest.TestCase):
    def test_runtime_is_networkless_read_only_and_prebuilt(self) -> None:
        command = docker_run_command(
            image_id=IMAGE_ID,
            run_dir=Path("/tmp/bench-run"),
            git_sha=SHA,
            host_cpu="Apple M5 Pro",
            host_ram_bytes=68719476736,
        )
        self.assertEqual(command[:3], ["docker", "run", "--rm"])
        for expected in [
            "linux/arm64",
            "none",
            "/tmp:rw,noexec,nosuid,size=256m",
            f"type=bind,src={Path('/tmp/bench-run').resolve()},dst=/out",
            f"LARA_BENCH_GIT_REV={SHA}",
            "LARA_BENCH_HOST_CPU=Apple M5 Pro",
            "LARA_BENCH_HOST_RAM_BYTES=68719476736",
            IMAGE_ID,
        ]:
            self.assertIn(expected, command)
        self.assertIn("--read-only", command)
        self.assertEqual(command[-1], IMAGE_ID)

    def test_rejects_image_built_from_another_revision(self) -> None:
        inspected = [
            {
                "Architecture": "arm64",
                "Os": "linux",
                "Id": IMAGE_ID,
                "Config": {
                    "Labels": {"org.opencontainers.image.revision": "b" * 40},
                },
            }
        ]
        with patch("scripts.bench_container.command_json", return_value=inspected):
            with self.assertRaisesRegex(BenchError, "does not match checkout"):
                image_metadata(ROOT, "lara-bench:stale", SHA)

    def test_compacts_docker_metadata_to_measurement_fields(self) -> None:
        compact = compact_docker_metadata(
            {
                "Client": {"Version": "29.4.0", "Arch": "arm64", "Plugins": ["private"]},
                "Server": {"Version": "29.4.0", "Arch": "arm64", "Components": ["private"]},
            },
            {
                "Architecture": "aarch64",
                "OSType": "linux",
                "NCPU": 18,
                "MemTotal": 16817168384,
                "OperatingSystem": "OrbStack",
                "Plugins": {"private": True},
            },
        )
        self.assertEqual(compact["engine"]["NCPU"], 18)
        self.assertEqual(compact["client"]["Version"], "29.4.0")
        self.assertNotIn("Plugins", compact["client"])
        self.assertNotIn("Plugins", compact["engine"])


class OutputValidationTests(unittest.TestCase):
    def test_validates_and_hashes_required_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            run_dir = Path(raw_dir)
            (run_dir / "bench.json").write_text(
                json.dumps({"environment": {"git_rev": SHA}, "units": []}),
                encoding="utf-8",
            )
            for name in ["performance.txt", "performance.md", "performance.tex"]:
                (run_dir / name).write_text(name, encoding="utf-8")
            digests = validate_outputs(run_dir, expected_git_rev=SHA)
            self.assertEqual(
                set(digests),
                {"bench.json", "performance.txt", "performance.md", "performance.tex"},
            )
            self.assertTrue(all(len(value) == 64 for value in digests.values()))

    def test_rejects_output_from_another_revision(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            run_dir = Path(raw_dir)
            (run_dir / "bench.json").write_text(
                json.dumps({"environment": {"git_rev": "b" * 40}, "units": []}),
                encoding="utf-8",
            )
            for name in ["performance.txt", "performance.md", "performance.tex"]:
                (run_dir / name).write_text(name, encoding="utf-8")
            with self.assertRaisesRegex(BenchError, "benchmark revision"):
                validate_outputs(run_dir, expected_git_rev=SHA)

    def test_rejects_missing_output(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            with self.assertRaisesRegex(BenchError, "missing benchmark output"):
                validate_outputs(Path(raw_dir), expected_git_rev=SHA)


def write_run(
    root: Path,
    name: str,
    *,
    batch: str = "B",
    status: str = "success",
    kernels: dict[str, int] | None = None,
    rev: str = SHA,
) -> Path:
    run_dir = root / name
    run_dir.mkdir()
    provenance: dict[str, object] = {
        "status": status,
        "error": None if status == "success" else "container exited 1",
        "source": {"git_rev": rev},
        "image": {"id": IMAGE_ID},
        "batch": {"id": batch, "index": 1},
        "cpuset": None,
        "benchmark": {"load_samples": [{"load_1m": 1.0}, {"load_1m": 3.0}]},
    }
    if status == "success":
        units = [{"base": base, "kernel_ns": ns} for base, ns in (kernels or {}).items()]
        (run_dir / "bench.json").write_text(json.dumps({"units": units}), encoding="utf-8")
        provenance["outputs"] = {"bench.json": file_sha256(run_dir / "bench.json")}
    (run_dir / "provenance.json").write_text(json.dumps(provenance), encoding="utf-8")
    return run_dir


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class BatchComparisonTests(unittest.TestCase):
    def test_reports_every_run_and_picks_the_lower_median_run(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            write_run(root, "r1", kernels={"u1": 200_000, "u2": 220_000})
            write_run(root, "r2", kernels={"u1": 210_000, "u2": 230_000})
            write_run(root, "r3", kernels={"u1": 190_000, "u2": 200_000})
            write_run(root, "r4", kernels={"u1": 400_000, "u2": 400_000})
            write_run(root, "r5", status="failed")
            write_run(root, "other", batch="C", kernels={"u1": 1, "u2": 1})
            result = compare(root, "B")
        self.assertEqual([run["run"] for run in result["runs"]], ["r1", "r2", "r3", "r4", "r5"])
        self.assertEqual(result["included_runs"], 4)
        excluded = [run for run in result["runs"] if not run["included"]]
        self.assertEqual([run["run"] for run in excluded], ["r5"])
        self.assertIn("container exited 1", excluded[0]["exclusion"])
        # Run medians 210k, 220k, 195k, 400k; sorted r3, r1, r2, r4; lower median r1.
        self.assertEqual(result["table_run"], "r1")
        self.assertEqual(result["control_median_ns"]["median"], 215_000)
        self.assertEqual(result["control_median_ns"]["min"], 195_000)
        self.assertEqual(result["control_median_ns"]["max"], 400_000)
        u1 = next(unit for unit in result["per_unit"] if unit["base"] == "u1")
        self.assertEqual((u1["min_ns"], u1["max_ns"], u1["median_ns"]), (190_000, 400_000, 205_000))
        self.assertEqual(result["runs"][0]["load_during_run"]["max"], 3.0)

    def test_refuses_outputs_changed_after_the_run(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            run_dir = write_run(root, "r1", kernels={"u1": 1})
            (run_dir / "bench.json").write_text(json.dumps({"units": []}), encoding="utf-8")
            with self.assertRaisesRegex(CompareError, "does not match the digest"):
                compare(root, "B")

    def test_refuses_a_batch_mixing_revisions(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            root = Path(raw_dir)
            write_run(root, "r1", kernels={"u1": 1})
            write_run(root, "r2", kernels={"u1": 1}, rev="b" * 40)
            with self.assertRaisesRegex(CompareError, "mixes revisions"):
                compare(root, "B")

    def test_refuses_an_unknown_batch(self) -> None:
        with tempfile.TemporaryDirectory() as raw_dir:
            with self.assertRaisesRegex(CompareError, "belongs to batch"):
                compare(Path(raw_dir), "B")


if __name__ == "__main__":
    unittest.main()
