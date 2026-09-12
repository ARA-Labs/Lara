import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("check_ara_session_index.py")


def load_checker():
    if not SCRIPT.is_file():
        raise AssertionError(f"missing production checker: {SCRIPT.name}")
    spec = importlib.util.spec_from_file_location("check_ara_session_index", SCRIPT)
    if spec is None or spec.loader is None:
        raise AssertionError(f"cannot load production checker: {SCRIPT.name}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


INDEX_HEADER = "sessions:\n"


def row(session_id, quoted=False):
    rendered = f"'{session_id}'" if quoted else session_id
    return (
        f"- id: {rendered}\n"
        f"  date: '{session_id[:10]}'\n"
        f"  summary: 'session {session_id}'\n"
        f"  turn_count: 1\n"
        f"  events_count: 1\n"
        f"  claims_touched: []\n"
        f"  open_threads: 0\n"
    )


class SessionIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.sessions = Path(self.temp_dir.name) / "ara" / "trace" / "sessions"
        self.sessions.mkdir(parents=True)

    def tearDown(self):
        self.temp_dir.cleanup()

    def write_session(self, session_id):
        (self.sessions / f"{session_id}.yaml").write_text(
            f"session:\n  id: {session_id}\n", encoding="utf-8"
        )

    def write_index(self, text):
        (self.sessions / "session_index.yaml").write_text(text, encoding="utf-8")

    def validate(self):
        return load_checker().validate_sessions(self.sessions)

    def test_accepts_bijection_between_rows_and_files(self):
        for session_id in ("2026-07-21_001", "2026-07-22_001", "2026-09-09_issue279"):
            self.write_session(session_id)
        self.write_index(
            INDEX_HEADER
            + row("2026-07-21_001")
            + row("2026-07-22_001")
            + "\n"
            + row("2026-09-09_issue279")
        )
        result = self.validate()
        self.assertEqual(result.errors, [])
        self.assertEqual(result.checked, 3)

    def test_accepts_quoted_ids(self):
        self.write_session("2026-07-21_001")
        self.write_index(INDEX_HEADER + row("2026-07-21_001", quoted=True))
        result = self.validate()
        self.assertEqual(result.errors, [])
        self.assertEqual(result.checked, 1)

    def test_reports_session_file_missing_from_index(self):
        self.write_session("2026-07-21_001")
        self.write_session("2026-07-22_001")
        self.write_index(INDEX_HEADER + row("2026-07-21_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("2026-07-22_001", result.errors[0])
        self.assertIn("no row", result.errors[0])

    def test_reports_duplicate_row(self):
        self.write_session("2026-07-21_001")
        self.write_session("2026-07-22_001")
        self.write_index(
            INDEX_HEADER
            + row("2026-07-21_001")
            + row("2026-07-22_001")
            + row("2026-07-21_001")
        )
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("2026-07-21_001", result.errors[0])
        self.assertIn("2 rows", result.errors[0])

    def test_reports_row_without_session_file(self):
        self.write_session("2026-07-21_001")
        self.write_index(INDEX_HEADER + row("2026-07-21_001") + row("2026-07-22_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("2026-07-22_001", result.errors[0])
        self.assertIn("no session file", result.errors[0])

    def test_reports_every_defect_not_just_the_first(self):
        self.write_session("2026-07-21_001")
        self.write_session("2026-07-23_001")
        self.write_index(
            INDEX_HEADER
            + row("2026-07-21_001")
            + row("2026-07-21_001")
            + row("2026-07-22_001")
        )
        result = self.validate()
        self.assertEqual(len(result.errors), 3)

    def test_rejects_index_that_does_not_open_with_sessions_key(self):
        self.write_session("2026-07-21_001")
        self.write_index("entries:\n" + row("2026-07-21_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("sessions:", result.errors[0])

    def test_rejects_unrecognized_top_level_line(self):
        self.write_session("2026-07-21_001")
        self.write_index(INDEX_HEADER + row("2026-07-21_001") + "- date: '2026-07-22'\n")
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("line 9", result.errors[0])

    def test_rejects_empty_directory(self):
        self.write_index(INDEX_HEADER)
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("no session files", result.errors[0])

    def test_missing_index_is_an_error(self):
        self.write_session("2026-07-21_001")
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("session_index.yaml", result.errors[0])

    def test_main_exits_two_on_failure_and_zero_on_success(self):
        checker = load_checker()
        self.write_session("2026-07-21_001")
        self.write_index(INDEX_HEADER)
        self.assertEqual(checker.main(["--sessions-dir", str(self.sessions)]), 2)
        self.write_index(INDEX_HEADER + row("2026-07-21_001"))
        self.assertEqual(checker.main(["--sessions-dir", str(self.sessions)]), 0)


if __name__ == "__main__":
    unittest.main()
