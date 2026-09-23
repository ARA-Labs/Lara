#!/usr/bin/env python3
"""Behavioral and orchestration tests for the publication benchmark runner."""

from __future__ import annotations

import io
import json
import os
import subprocess
import sys
import tempfile
import unittest
from contextlib import ExitStack, redirect_stderr
from pathlib import Path
from unittest.mock import patch

from scripts.bench_container import (
    BenchError,
    compact_docker_metadata,
    docker_run_command,
    image_metadata,
    main,
    parse_args,
    run_publication,
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


if __name__ == "__main__":
    unittest.main()
