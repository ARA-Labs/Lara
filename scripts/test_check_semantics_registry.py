#!/usr/bin/env python3
"""Exercise the registry gate against real Lean declarations in temporary modules."""
from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean"
CHECK = ROOT / "scripts/check-semantics-registry.py"
PRELUDE = "import Lara.Semantics.Registry\nopen Lara.Semantics\n"


class SemanticsRegistryTests(unittest.TestCase):
    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix="RegistryAuditFixture", dir=LEAN / "Lara"))
        self.root_files: list[Path] = []

    def tearDown(self):
        shutil.rmtree(self.directory)
        for path in self.root_files:
            path.unlink(missing_ok=True)

    def fixture(self, source: str, name: str = "Case", imports: str = "") -> str:
        path = self.directory / f"{name}.lean"
        path.write_text(imports + PRELUDE + source)
        return ".".join(path.relative_to(LEAN).with_suffix("").parts)

    def check(self, *modules: str) -> subprocess.CompletedProcess:
        args = [sys.executable, str(CHECK)]
        for module in modules:
            args.extend(["--module", module])
        return subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=600)

    def rejected(self, source: str, declaration: str):
        result = self.check(self.fixture(source))
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("unregistered", result.stdout.lower())
        self.assertIn(declaration, result.stdout)

    def test_registered_import_and_parameterized_family_pass(self):
        module = self.fixture("def family (_ : Nat) : ExtensionSemantics := groundedSem\n")
        result = self.check(module)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_example_qualified_constructor_names_remain_available(self):
        constructors = ("grounded", "complete", "preferred", "stable", "semiStable")
        source = "\n".join(
            f"#check Lara.Examples.Semantics.SemanticsName.{name}" for name in constructors)
        module = self.fixture(source + "\n", "Compatibility", "import Lara.Examples.Semantics\n")
        result = self.check(module)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_closed_value_alias_is_rejected(self):
        self.rejected("def omittedAlias : ExtensionSemantics := groundedSem\n", "omittedAlias")

    def test_type_abbreviation_does_not_hide_declaration(self):
        self.rejected("abbrev Hidden := ExtensionSemantics\ndef omittedTyped : Hidden := groundedSem\n",
                      "omittedTyped")

    def test_private_definition_is_rejected(self):
        self.rejected("private def omittedPrivate : ExtensionSemantics := groundedSem\n",
                      "omittedPrivate")

    def test_opaque_value_is_rejected(self):
        self.rejected("opaque omittedOpaque : ExtensionSemantics := groundedSem\n", "omittedOpaque")

    def test_opaque_type_does_not_hide_declaration(self):
        # The fixture is deliberately not a proof-library contribution. An axiom
        # supplies an inhabitant of the opaque type so the audit must inspect it.
        self.rejected("opaque Hidden : Type := ExtensionSemantics\naxiom omittedHidden : Hidden\n",
                      "omittedHidden")

    def test_whole_tree_discovers_module_outside_root_imports(self):
        self.fixture("def omittedUnimported : ExtensionSemantics := groundedSem\n", "Unimported")
        result = self.check()
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertIn("unregistered", result.stdout.lower())
        self.assertIn("omittedUnimported", result.stdout)

    def test_root_scripts_with_separate_main_declarations_pass(self):
        modules = []
        for suffix in ("One", "Two"):
            path = LEAN / f"{self.directory.name}{suffix}.lean"
            self.root_files.append(path)
            path.write_text(PRELUDE + 'def main : IO Unit := IO.println "fixture"\n')
            modules.append(path.stem)
        result = self.check(*modules)
        self.assertEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main()
