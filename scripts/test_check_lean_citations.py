#!/usr/bin/env python3
"""Regression tests for check-lean-citations.py."""

from __future__ import annotations

import importlib.util
import tempfile
import unittest
from pathlib import Path
from unittest import mock


SCRIPT_PATH = Path(__file__).with_name("check-lean-citations.py")
SPEC = importlib.util.spec_from_file_location("check_lean_citations", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
check_lean_citations = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(check_lean_citations)

# Line 3 is a theorem, 5 a def, 7 a structure, 8 one of its fields, 9 blank and
# 10 an anonymous instance — one target for every branch the gate has.
WIDGET = """\
/-! The widget layer. -/

theorem widget_ok : True := trivial

def widgetCount : Nat := 0

structure Widget where
  size : Nat

instance : Inhabited Widget := ⟨⟨0⟩⟩
"""

CHECK_WIDGET = """\
/-! The checked widget layer. -/

def checkWidget : Bool := true
"""


class CitationTests(unittest.TestCase):
    def check(self, prose: str, *, second_widget: bool = False, allowlist=None):
        """Run the gate over a throwaway tree holding `prose` as its only document."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "lean" / "Lara").mkdir(parents=True)
            (root / "lean" / "Lara" / "Widget.lean").write_text(WIDGET, encoding="utf-8")
            if second_widget:
                (root / "lean" / "Lara" / "Check").mkdir()
                (root / "lean" / "Lara" / "Check" / "Widget.lean").write_text(
                    CHECK_WIDGET, encoding="utf-8"
                )
            (root / "docs").mkdir()
            (root / "docs" / "note.md").write_text(prose, encoding="utf-8")
            with mock.patch.dict(
                check_lean_citations.ALLOWLIST, allowlist or {}, clear=True
            ):
                return check_lean_citations.check_repo(root)

    def test_resolves_a_prefix_less_citation(self) -> None:
        checked, _, errors = self.check("See `Widget.lean:3` for the statement.\n")
        self.assertEqual(errors, [])
        self.assertEqual(checked, 1)

    def test_resolves_a_partial_path_citation(self) -> None:
        checked, _, errors = self.check(
            "See `Lara/Widget.lean:3` and `Lara/Check/Widget.lean:3`.\n",
            second_widget=True,
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 2)

    def test_ambiguous_suffix_is_an_error(self) -> None:
        checked, _, errors = self.check("See `Widget.lean:3`.\n", second_widget=True)
        self.assertEqual(checked, 0)
        self.assertEqual(len(errors), 1)
        self.assertIn("ambiguous suffix", errors[0])
        self.assertIn("lean/Lara/Check/Widget.lean", errors[0])
        self.assertIn("lean/Lara/Widget.lean", errors[0])

    def test_name_mismatch_is_an_error(self) -> None:
        _, _, errors = self.check("The `widgetCount` (`Widget.lean:3`) total.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("names `widgetCount`", errors[0])
        self.assertIn("declares `widget_ok`", errors[0])

    def test_qualified_prose_name_matches_the_declaration(self) -> None:
        _, _, errors = self.check("`Lara.Widget.widget_ok` (`Widget.lean:3`) holds.\n")
        self.assertEqual(errors, [])

    def test_citation_without_an_adjacent_name_is_accepted(self) -> None:
        _, _, errors = self.check("The statement at `Widget.lean:3` is trivial.\n")
        self.assertEqual(errors, [])

    def test_several_names_sharing_a_citation_suppress_the_name_check(self) -> None:
        _, _, errors = self.check(
            "`widget_ok`/`widgetCount` (`Widget.lean:3` and `:5`) pair up.\n"
            "`widget_ok` and `widgetCount` (`Widget.lean:3`, `:5`) pair up.\n"
        )
        self.assertEqual(errors, [])

    def test_a_line_range_is_resolved_at_its_start(self) -> None:
        checked, _, errors = self.check(
            "Blocks at `Widget.lean:7-8` and `Widget.lean:7–10` hold it.\n"
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 2)

    def test_a_line_range_starting_off_a_declaration_is_an_error(self) -> None:
        _, _, errors = self.check("The field block `Widget.lean:8-9`.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("is not a declaration", errors[0])

    def test_a_backwards_line_range_is_an_error(self) -> None:
        _, _, errors = self.check("The block `Widget.lean:5-3`.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("ends at or before its start", errors[0])

    def test_a_line_range_ending_past_the_file_is_an_error(self) -> None:
        _, _, errors = self.check("The block `Widget.lean:3-400`.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("ends past end of file", errors[0])

    def test_a_range_end_is_checked_even_when_its_start_is_allowlisted(self) -> None:
        _, used, errors = self.check(
            "The `size` field block (`Widget.lean:8-400`).\n",
            allowlist={"lean/Lara/Widget.lean:8": "cites the `size` field"},
        )
        self.assertEqual(used, {"lean/Lara/Widget.lean:8"})
        self.assertEqual(len(errors), 1)
        self.assertIn("ends past end of file", errors[0])

    def test_a_bare_citation_resolves_through_the_name_beside_it(self) -> None:
        checked, _, errors = self.check("The `widget_ok` (:3) statement.\n")
        self.assertEqual(errors, [])
        self.assertEqual(checked, 1)

    def test_a_bare_citation_off_its_declaration_is_an_error(self) -> None:
        _, _, errors = self.check("The `widget_ok` (:5) statement.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("names `widget_ok`", errors[0])
        self.assertIn("lean/Lara/Widget.lean:5 declares `widgetCount`", errors[0])

    def test_a_bare_citation_carries_the_file_of_its_neighbour(self) -> None:
        checked, _, errors = self.check(
            "The pair (`Widget.lean:3` and `:5`) is complete.\n"
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 2)

    def test_a_bare_citation_does_not_carry_across_prose(self) -> None:
        checked, _, errors = self.check(
            "`Widget.lean:3` sits above; `gadgetry` was moved to `:5`.\n"
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 1)

    def test_a_bare_citation_naming_nothing_is_skipped(self) -> None:
        checked, _, errors = self.check("The `Widget.lean` layer, at (:3).\n")
        self.assertEqual(errors, [])
        self.assertEqual(checked, 0)

    def test_a_block_naming_a_file_outright_overrides_the_name(self) -> None:
        checked, _, errors = self.check(
            "`Lara/Check/Widget.lean` collects them; `widget_ok` (:3) is one.\n",
            second_widget=True,
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 0)

    def test_a_table_row_is_a_block_of_its_own(self) -> None:
        checked, _, errors = self.check(
            "| file | note |\n"
            "| --- | --- |\n"
            "| `Lara/Check/Widget.lean` | the checked layer |\n"
            "| `widget_ok` (:3) | the statement |\n",
            second_widget=True,
        )
        self.assertEqual(errors, [])
        self.assertEqual(checked, 1)

    def test_lean_diagnostic_locations_are_not_citations(self) -> None:
        checked, _, errors = self.check('Lean says "Widget.lean:9:14: error".\n')
        self.assertEqual(checked, 0)
        self.assertEqual(errors, [])

    def test_non_declaration_is_an_error_unless_allowlisted(self) -> None:
        _, _, errors = self.check("The `size` field (`Widget.lean:8`).\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("is not a declaration", errors[0])

        _, used, errors = self.check(
            "The `size` field (`Widget.lean:8`).\n",
            allowlist={"lean/Lara/Widget.lean:8": "cites the `size` field"},
        )
        self.assertEqual(errors, [])
        self.assertEqual(used, {"lean/Lara/Widget.lean:8"})

    def test_anonymous_declaration_skips_the_name_check(self) -> None:
        _, _, errors = self.check("The `widgetInhabited` (`Widget.lean:10`).\n")
        self.assertEqual(errors, [])

    def test_citation_past_end_of_file_is_an_error(self) -> None:
        _, _, errors = self.check("See `Widget.lean:400`.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("past end of file", errors[0])

    def test_missing_file_is_an_error(self) -> None:
        _, _, errors = self.check("See `Gadget.lean:3`.\n")
        self.assertEqual(len(errors), 1)
        self.assertIn("cites missing file Gadget.lean", errors[0])

    def test_unused_allowlist_entry_is_an_error(self) -> None:
        _, _, errors = self.check(
            "See `Widget.lean:3`.\n",
            allowlist={"lean/Lara/Widget.lean:5": "never cited"},
        )
        self.assertEqual(len(errors), 1)
        self.assertIn("is unused", errors[0])


class RepositoryTest(unittest.TestCase):
    def test_the_repository_itself_passes(self) -> None:
        root = SCRIPT_PATH.resolve().parent.parent
        checked, _, errors = check_lean_citations.check_repo(root)
        self.assertEqual(errors, [])
        self.assertGreater(checked, 0)


if __name__ == "__main__":
    unittest.main()
