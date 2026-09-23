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


def row(session_id, quoted=False, *, date=None, turn_count=1, events=1, claims=(), open_threads=0):
    rendered = f"'{session_id}'" if quoted else session_id
    claims_text = "[" + ", ".join(claims) + "]"
    return (
        f"- id: {rendered}\n"
        f"  date: '{date or session_id[:10]}'\n"
        f"  summary: 'session {session_id}'\n"
        f"  turn_count: {turn_count}\n"
        f"  events_count: {events}\n"
        f"  claims_touched: {claims_text}\n"
        f"  open_threads: {open_threads}\n"
    )


def event(turn, event_id):
    return (
        f"  - turn: {turn}\n"
        f"    type: observation\n"
        f"    id: \"{event_id}\"\n"
        f"    provenance: ai-suggested\n"
        f"    summary: \"event {event_id}\"\n"
    )


def events_block(key, turn, ids):
    if not ids:
        return f"{key}: []\n"
    return f"{key}:\n" + "".join(event(turn, event_id) for event_id in ids)


def claims_block(key, claims, bare=False):
    if not claims:
        return f"{key}: []\n"
    if bare:
        return f"{key}: [" + ", ".join(claims) + "]\n"
    return f"{key}:\n" + "".join(
        f"  - id: {claim}\n    action: crystallized\n    turn: 1\n" for claim in claims
    )


def threads_block(key, count):
    if count == 0:
        return f"{key}: []\n"
    return f"{key}:\n" + "".join(f"  - \"thread {n}\"\n" for n in range(count))


def session_text(
    session_id,
    *,
    turn_count=1,
    events=1,
    claims=(),
    open_threads=0,
    legacy=False,
    bare_claims=False,
    file_id=None,
):
    file_id = file_id or session_id
    if legacy:
        header = (
            "session:\n"
            f"  id: \"{file_id}\"\n"
            f"  timestamp: \"{session_id[:10]}T10:00\"\n"
            f"  summary: \"session {session_id}\"\n"
        )
    else:
        header = (
            "session:\n"
            f"  id: \"{file_id}\"\n"
            f"  date: \"{session_id[:10]}\"\n"
            f"  turn_count: {turn_count}\n"
            f"  summary: \"session {session_id}\"\n"
        )
    return (
        header
        + "\n"
        + events_block("events_logged", 1, [f"N{n}" for n in range(events)])
        + "\n"
        + claims_block("claims_touched", claims, bare=bare_claims)
        + "\n"
        + threads_block("open_threads", open_threads)
    )


class SessionIndexTests(unittest.TestCase):
    def setUp(self):
        self.temp_dir = tempfile.TemporaryDirectory()
        self.sessions = Path(self.temp_dir.name) / "ara" / "trace" / "sessions"
        self.sessions.mkdir(parents=True)

    def tearDown(self):
        self.temp_dir.cleanup()

    def write_session(self, session_id, text=None, **fields):
        (self.sessions / f"{session_id}.yaml").write_text(
            text if text is not None else session_text(session_id, **fields),
            encoding="utf-8",
        )

    def write_index(self, text):
        (self.sessions / "session_index.yaml").write_text(text, encoding="utf-8")

    def validate(self):
        return load_checker().validate_sessions(self.sessions)

    # -- totality and uniqueness --------------------------------------------

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

    # -- field agreement ----------------------------------------------------

    def test_accepts_row_that_agrees_with_its_file(self):
        self.write_session(
            "2026-08-01_001", turn_count=3, events=4, claims=("C01", "H02"), open_threads=2
        )
        self.write_index(
            INDEX_HEADER
            + row("2026-08-01_001", turn_count=3, events=4, claims=("H02", "C01"), open_threads=2)
        )
        result = self.validate()
        self.assertEqual(result.errors, [])

    def test_reports_turn_count_disagreement(self):
        self.write_session("2026-08-01_001", turn_count=2)
        self.write_index(INDEX_HEADER + row("2026-08-01_001", turn_count=1))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("turn_count", result.errors[0])
        self.assertIn("1", result.errors[0])
        self.assertIn("2", result.errors[0])

    def test_reports_events_count_disagreement(self):
        self.write_session("2026-08-01_001", events=7)
        self.write_index(INDEX_HEADER + row("2026-08-01_001", events=5))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("events_count", result.errors[0])

    def test_reports_claims_touched_disagreement(self):
        self.write_session("2026-08-01_001", claims=("C01",))
        self.write_index(INDEX_HEADER + row("2026-08-01_001", claims=("C02",)))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("claims_touched", result.errors[0])
        self.assertIn("C01", result.errors[0])
        self.assertIn("C02", result.errors[0])

    def test_reports_open_threads_disagreement(self):
        self.write_session("2026-08-01_001", open_threads=3)
        self.write_index(INDEX_HEADER + row("2026-08-01_001", open_threads=1))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("open_threads", result.errors[0])

    def test_reports_date_disagreement(self):
        self.write_session("2026-08-01_001")
        self.write_index(INDEX_HEADER + row("2026-08-01_001", date="2026-08-02"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("date", result.errors[0])

    def test_reports_every_disagreeing_field_of_a_row(self):
        self.write_session("2026-08-01_001", turn_count=2, events=3, open_threads=1)
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 3)

    def test_counts_continuation_and_nested_turn_blocks(self):
        # Multi-turn sessions append `events_logged_turn2`-style continuation
        # blocks or nested `turn_<n>:` mappings. Events and claims accumulate
        # across every block; open_threads is the LAST block's snapshot.
        text = (
            session_text("2026-08-01_001", turn_count=3, events=2, claims=("C01",), open_threads=4)
            + "\n"
            + events_block("events_logged_turn2", 2, ["N10", "N11", "N12"])
            + claims_block("claims_touched_turn2", ("C02",))
            + threads_block("open_threads_turn2", 6)
            + "\n"
            + "turn_3:\n"
            + "  events_logged:\n"
            + "    - turn: 3\n      type: observation\n      id: \"N20\"\n"
            + "  claims_touched:\n    - id: C01\n      action: revised\n      turn: 3\n"
            + "  open_threads:\n    - \"only thread\"\n"
        )
        self.write_session("2026-08-01_001", text)
        self.write_index(
            INDEX_HEADER
            + row("2026-08-01_001", turn_count=3, events=6, claims=("C01", "C02"), open_threads=1)
        )
        result = self.validate()
        self.assertEqual(result.errors, [])

    def test_accepts_bare_string_claim_ids(self):
        self.write_session("2026-08-01_001", claims=("C21", "H08"), bare_claims=True)
        self.write_index(INDEX_HEADER + row("2026-08-01_001", claims=("C21", "H08")))
        result = self.validate()
        self.assertEqual(result.errors, [])

    def test_accepts_legacy_timestamp_shape_without_turn_count(self):
        # The July 2026 files carry `session.timestamp` and no `turn_count`;
        # their row's turn_count is the only record and goes unchecked, but
        # the date must still agree with the timestamp's day.
        self.write_session("2026-07-24_003", legacy=True, events=2)
        self.write_index(INDEX_HEADER + row("2026-07-24_003", turn_count=8, events=2))
        result = self.validate()
        self.assertEqual(result.errors, [])
        self.write_index(INDEX_HEADER + row("2026-07-24_003", turn_count=8, events=2, date="2026-07-25"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("date", result.errors[0])

    def test_rejects_dated_file_without_turn_count(self):
        text = session_text("2026-08-01_001").replace("  turn_count: 1\n", "")
        self.write_session("2026-08-01_001", text)
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("turn_count", result.errors[0])

    def test_rejects_duplicate_top_level_key(self):
        text = session_text("2026-08-01_001") + "\nevents_logged: []\n"
        self.write_session("2026-08-01_001", text)
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("duplicate", result.errors[0])
        self.assertIn("events_logged", result.errors[0])

    def test_rejects_session_id_that_differs_from_file_name(self):
        self.write_session("2026-08-01_001", file_id="2026-08-01_002")
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("2026-08-01_002", result.errors[0])

    def test_rejects_claim_entry_without_id(self):
        text = session_text("2026-08-01_001").replace(
            "claims_touched: []\n", "claims_touched:\n  - action: revised\n    turn: 1\n"
        )
        self.write_session("2026-08-01_001", text)
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("claims_touched", result.errors[0])

    def test_rejects_unparseable_session_file(self):
        self.write_session("2026-08-01_001", "session: [unclosed\n")
        self.write_index(INDEX_HEADER + row("2026-08-01_001"))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("2026-08-01_001.yaml", result.errors[0])

    def test_rejects_row_missing_a_counted_field(self):
        self.write_session("2026-08-01_001")
        self.write_index(INDEX_HEADER + row("2026-08-01_001").replace("  open_threads: 0\n", ""))
        result = self.validate()
        self.assertEqual(len(result.errors), 1)
        self.assertIn("open_threads", result.errors[0])


if __name__ == "__main__":
    unittest.main()
