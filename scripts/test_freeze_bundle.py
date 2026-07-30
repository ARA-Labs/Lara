#!/usr/bin/env python3
"""Focused filesystem tests for transactional replay-bundle installation."""

from __future__ import annotations

import importlib.util
import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT_PATH = Path(__file__).with_name("freeze-bundle.py")
SPEC = importlib.util.spec_from_file_location("freeze_bundle", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
freeze_bundle = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(freeze_bundle)


class InstallFrozenOutputsTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary_directory.cleanup)
        root = Path(self.temporary_directory.name)
        self.stage = root / "stage"
        self.bundle = root / "bundle"
        self.stage.mkdir()
        self.bundle.mkdir()
        self.core_source = self.stage / "emitted.core.sexp"
        self.verdict_source = self.stage / "verdict.txt"
        self.manifest_source = self.stage / "manifest.json"
        self.core_source.write_bytes(b"new core\n")
        self.verdict_source.write_bytes(b"new verdict\n")
        self.manifest_source.write_bytes(b"new manifest\n")
        self.core_destination = self.bundle / "emitted.core.sexp"
        self.verdict_destination = self.bundle / "verdict.txt"
        self.manifest_destination = self.bundle / "manifest.json"
        self.outputs = [
            (self.core_source, self.core_destination),
            (self.verdict_source, self.verdict_destination),
            (self.manifest_source, self.manifest_destination),
        ]

    def test_directory_destination_fails_preflight_without_mutation(self) -> None:
        self.core_destination.write_bytes(b"old core\n")
        self.verdict_destination.mkdir()
        verdict_sentinel = self.verdict_destination / "sentinel"
        verdict_sentinel.write_bytes(b"old directory contents\n")
        self.manifest_destination.write_bytes(b"old manifest\n")
        core_inode = self.core_destination.stat().st_ino
        manifest_inode = self.manifest_destination.stat().st_ino

        with self.assertRaisesRegex(
            freeze_bundle.FreezeError,
            "destination is not a regular non-symlink file",
        ):
            freeze_bundle.install_frozen_outputs(self.stage, self.outputs)

        self.assertEqual(self.core_destination.read_bytes(), b"old core\n")
        self.assertEqual(self.core_destination.stat().st_ino, core_inode)
        self.assertTrue(self.verdict_destination.is_dir())
        self.assertEqual(verdict_sentinel.read_bytes(), b"old directory contents\n")
        self.assertEqual(self.manifest_destination.read_bytes(), b"old manifest\n")
        self.assertEqual(self.manifest_destination.stat().st_ino, manifest_inode)

    def test_verdict_install_failure_restores_old_files_and_removes_new_core(self) -> None:
        self.verdict_destination.write_bytes(b"old verdict\n")
        self.manifest_destination.write_bytes(b"old manifest\n")
        verdict_inode = self.verdict_destination.stat().st_ino
        manifest_inode = self.manifest_destination.stat().st_ino
        original_replace = os.replace

        def fail_verdict(source: Path, destination: Path) -> None:
            if source == self.verdict_source and destination == self.verdict_destination:
                raise OSError("injected verdict install failure")
            original_replace(source, destination)

        with mock.patch.object(freeze_bundle.os, "replace", side_effect=fail_verdict):
            with self.assertRaisesRegex(
                freeze_bundle.FreezeError,
                "injected verdict install failure",
            ):
                freeze_bundle.install_frozen_outputs(self.stage, self.outputs)

        self.assertFalse(self.core_destination.exists())
        self.assertEqual(self.verdict_destination.read_bytes(), b"old verdict\n")
        self.assertEqual(self.verdict_destination.stat().st_ino, verdict_inode)
        self.assertEqual(self.manifest_destination.read_bytes(), b"old manifest\n")
        self.assertEqual(self.manifest_destination.stat().st_ino, manifest_inode)

    def test_manifest_install_failure_restores_old_files_and_removes_new_verdict(self) -> None:
        self.core_destination.write_bytes(b"old core\n")
        self.manifest_destination.write_bytes(b"old manifest\n")
        core_inode = self.core_destination.stat().st_ino
        manifest_inode = self.manifest_destination.stat().st_ino
        original_replace = os.replace

        def fail_manifest(source: Path, destination: Path) -> None:
            if source == self.manifest_source and destination == self.manifest_destination:
                raise OSError("injected manifest install failure")
            original_replace(source, destination)

        with mock.patch.object(freeze_bundle.os, "replace", side_effect=fail_manifest):
            with self.assertRaisesRegex(
                freeze_bundle.FreezeError,
                "injected manifest install failure",
            ):
                freeze_bundle.install_frozen_outputs(self.stage, self.outputs)

        self.assertEqual(self.core_destination.read_bytes(), b"old core\n")
        self.assertEqual(self.core_destination.stat().st_ino, core_inode)
        self.assertFalse(self.verdict_destination.exists())
        self.assertEqual(self.manifest_destination.read_bytes(), b"old manifest\n")
        self.assertEqual(self.manifest_destination.stat().st_ino, manifest_inode)

    def test_rollback_failure_reports_both_errors_and_continues_restoring(self) -> None:
        self.core_destination.write_bytes(b"old core\n")
        self.verdict_destination.write_bytes(b"old verdict\n")
        self.manifest_destination.write_bytes(b"old manifest\n")
        original_replace = os.replace

        def fail_install_and_one_restore(source: Path, destination: Path) -> None:
            if source == self.manifest_source and destination == self.manifest_destination:
                raise OSError("injected manifest install failure")
            if destination == self.verdict_destination and source.name == "1-verdict.txt":
                raise OSError("injected verdict rollback failure")
            original_replace(source, destination)

        with mock.patch.object(
            freeze_bundle.os,
            "replace",
            side_effect=fail_install_and_one_restore,
        ):
            with self.assertRaises(freeze_bundle.FreezeError) as raised:
                freeze_bundle.install_frozen_outputs(self.stage, self.outputs)

        message = str(raised.exception)
        self.assertIn("injected manifest install failure", message)
        self.assertIn("rollback failed", message)
        self.assertIn("injected verdict rollback failure", message)
        self.assertEqual(self.core_destination.read_bytes(), b"old core\n")
        self.assertEqual(self.manifest_destination.read_bytes(), b"old manifest\n")
        self.assertEqual(self.verdict_destination.read_bytes(), b"new verdict\n")


if __name__ == "__main__":
    unittest.main()
