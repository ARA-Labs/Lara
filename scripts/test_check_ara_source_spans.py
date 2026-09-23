import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("check_ara_source_spans.py")


def load_checker():
    if not SCRIPT.is_file():
        raise AssertionError(f"missing production checker: {SCRIPT.name}")
    spec = importlib.util.spec_from_file_location("check_ara_source_spans", SCRIPT)
    if spec is None or spec.loader is None:
        raise AssertionError(f"cannot load production checker: {SCRIPT.name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class SourceSpanTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.repo = Path(self.temp_dir.name)
        (self.repo / "ara" / "logic").mkdir(parents=True)
        (self.repo / "docs").mkdir()

    def tearDown(self):
        self.temp_dir.cleanup()

    def validate(self, source_text, citation_text):
        (self.repo / "docs" / "source.md").write_text(source_text, encoding="utf-8")
        (self.repo / "ara" / "logic" / "claims.md").write_text(
            f"- **Sources**: [{citation_text}]\n", encoding="utf-8"
        )
        return load_checker().validate_tree(self.repo, self.repo / "ara")

    def test_accepts_whitespace_normalized_quote_inside_inclusive_range(self):
        result = self.validate(
            "heading\nalpha   beta\ngamma delta\nfooter\n",
            "claim ← docs/source.md:2-3 «alpha beta gamma delta» [input]",
        )
        self.assertEqual(result.checked, 1)
        self.assertEqual(result.errors, [])

    def test_accepts_en_dash_inclusive_range(self):
        result = self.validate(
            "heading\nalpha beta\ngamma delta\nfooter\n",
            "claim ← docs/source.md:2–3 «alpha beta gamma delta» [input]",
        )
        self.assertEqual(result.checked, 1)
        self.assertEqual(result.errors, [])

    def test_accepts_single_line_citation(self):
        result = self.validate(
            "heading\nsingle quoted statement\nfooter\n",
            "claim ← docs/source.md:2 «single quoted statement» [input]",
        )
        self.assertEqual(result.checked, 1)
        self.assertEqual(result.errors, [])

    def test_ignores_historical_git_source_locations(self):
        result = self.validate(
            "current text\n",
            "claim ← `git abc123:docs/source.md:1` «historical text» [input]",
        )
        self.assertEqual(result.checked, 0)
        self.assertEqual(result.errors, [])

    def test_rejects_stale_quote(self):
        result = self.validate(
            "heading\ncurrent wording\nfooter\n",
            "claim ← docs/source.md:2-2 «old wording» [input]",
        )
        self.assertEqual(result.checked, 1)
        self.assertEqual(len(result.errors), 1)
        self.assertIn("quotation not found in cited range", result.errors[0])

    def test_slash_separated_fragments_must_appear_in_order(self):
        accepted = self.validate(
            "first helper\nimplementation\nsecond helper\nimplementation\nthird helper\n",
            "helpers ← docs/source.md:1-5 «first helper / second helper / third helper» [input]",
        )
        self.assertEqual(accepted.errors, [])

        rejected = self.validate(
            "third helper\nsecond helper\nfirst helper\n",
            "helpers ← docs/source.md:1-3 «first helper / second helper / third helper» [input]",
        )
        self.assertEqual(len(rejected.errors), 1)
        self.assertIn("quotation fragment not found in order", rejected.errors[0])

    def test_rejects_out_of_bounds_range(self):
        result = self.validate(
            "only line\n",
            "claim ← docs/source.md:1-2 «only line» [input]",
        )
        self.assertEqual(len(result.errors), 1)
        self.assertIn("range 1-2 exceeds 1 lines", result.errors[0])


if __name__ == "__main__":
    unittest.main()
