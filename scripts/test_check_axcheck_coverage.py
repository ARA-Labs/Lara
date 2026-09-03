#!/usr/bin/env python3
"""Regression tests for check-axcheck-coverage.py."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "check-axcheck-coverage.py"


class AxCheckCoverageTests(unittest.TestCase):
    def run_checker(self, source: str, axcheck: str) -> subprocess.CompletedProcess[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source_path = root / "Source.lean"
            axcheck_path = root / "AxCheck.lean"
            source_path.write_text(source, encoding="utf-8")
            axcheck_path.write_text(axcheck, encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(CHECKER), str(axcheck_path), str(source_path)],
                text=True,
                capture_output=True,
                check=False,
            )

    def test_reports_attribute_prefixed_and_mutual_theorems(self) -> None:
        result = self.run_checker(
            """\
namespace Lara.Context
@[simp] theorem attributed : True := by trivial
mutual
  theorem first : True := by trivial
  theorem second : True := by trivial
end
private theorem hidden : True := by trivial
end Lara.Context
""",
            """\
#print axioms Lara.Context.first
""",
        )

        self.assertEqual(result.returncode, 1)
        self.assertIn("Lara.Context.attributed", result.stderr)
        self.assertIn("Lara.Context.second", result.stderr)
        self.assertNotIn("Lara.Context.hidden", result.stderr)

    def test_accepts_every_public_theorem_and_ignores_comments(self) -> None:
        result = self.run_checker(
            """\
namespace Lara
/- theorem Blocked : False := by trivial -/
namespace Nested
-- theorem LineComment : False := by trivial
@[simp] theorem attributed : True := by trivial
section Local
lemma ordinary : True := by trivial
private theorem hidden : True := by trivial
private section
theorem sectionHidden : True := by trivial
end
end Local
end Nested
end Lara
""",
            """\
#print axioms Lara.Nested.attributed
#print axioms Lara.Nested.ordinary
""",
        )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("AxCheck coverage passed (2 declarations).", result.stdout)
        self.assertNotIn("Lara.Nested.sectionHidden", result.stderr)


if __name__ == "__main__":
    unittest.main()
