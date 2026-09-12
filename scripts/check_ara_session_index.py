#!/usr/bin/env python3
"""Assert that ara/trace/sessions/session_index.yaml agrees with the session
files it enumerates (#337, #338).

The index is the only enumeration of the trace, so its failure modes are
silent to every consumer that reads it: a session file with no row is
invisible, an id with two rows is read stale (the first match wins), and a
row whose counts disagree with its file misreports the session. This gate
holds the index to a bijection with the session files beside it and to
agreement with each file on every counted field:

- every ``2*.yaml`` under the sessions directory has exactly one ``- id:`` row;
- no id appears in more than one row;
- no row names a session file that does not exist;
- each row's ``date``, ``turn_count``, ``events_count``, ``claims_touched``
  and ``open_threads`` equal the projection of its session file.

The session file is authoritative and the row is its projection; the
projection rules (which file spellings are accepted, how multi-turn
continuation blocks count) are recorded in
``docs/ara-session-record-decision.md``. In short: events and claims
accumulate across ``events_logged`` / ``claims_touched``, their
``*_<suffix>`` continuation blocks, and nested ``turn_<n>:`` mappings;
``open_threads`` is the size of the LAST such block, the threads open at
session end; a claim entry is a mapping with an ``id`` or a bare id string;
``session.turn_count`` is compared when the file records it, and the legacy
July 2026 shape (``session.timestamp``, no ``turn_count``) is accepted with
that one field unchecked.

The index rows are enumerated with the line grammar of #337 (rows begin at
column 0 with ``- id:``; any other column-0 content is rejected rather than
guessed at), and both the index and the session files are then read with
PyYAML under a loader that refuses duplicate mapping keys, because a duplicate
top-level key is exactly the kind of drift a permissive reader hides. PyYAML
is the gate's one dependency beyond the standard library. Any defect names
itself and the gate exits 2.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import yaml


INDEX_NAME = "session_index.yaml"
SESSION_GLOB = "2*.yaml"
HEADER = "sessions:"
ROW = re.compile(r"^- id:\s*(?P<quote>['\"]?)(?P<id>[^'\"\s#]+)(?P=quote)\s*(?:#.*)?$")
CONTINUATION = re.compile(r"^\s+\S")

EVENTS_KEY = "events_logged"
CLAIMS_KEY = "claims_touched"
THREADS_KEY = "open_threads"
TURN_BLOCK = re.compile(r"^turn_\d+$")
ROW_FIELDS = ("date", "turn_count", "events_count", "claims_touched", "open_threads")


class StrictLoader(yaml.SafeLoader):
    """SafeLoader that refuses duplicate keys instead of keeping the last one."""

    def construct_mapping(self, node, deep=False):
        seen: set = set()
        for key_node, _ in node.value:
            key = self.construct_object(key_node, deep=deep)
            if key in seen:
                raise yaml.constructor.ConstructorError(
                    "while constructing a mapping",
                    node.start_mark,
                    f"found duplicate key {key!r}",
                    key_node.start_mark,
                )
            seen.add(key)
        return super().construct_mapping(node, deep=deep)


@dataclass(frozen=True)
class ValidationResult:
    checked: int
    errors: list[str]


@dataclass(frozen=True)
class SessionProjection:
    """What a session file says its index row must say."""

    date: str
    turn_count: int | None  # None: legacy shape, the row's value is unchecked
    events_count: int
    claims_touched: frozenset[str]
    open_threads: int


def read_index_ids(index: Path) -> tuple[list[str], list[str]]:
    """Return the ids listed in the index, in order, and any grammar errors."""
    ids: list[str] = []
    errors: list[str] = []
    lines = index.read_text(encoding="utf-8").splitlines()
    location = index.name

    header_seen = False
    for number, line in enumerate(lines, start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if not header_seen:
            if line.rstrip() == HEADER:
                header_seen = True
                continue
            errors.append(f"{location}:{number}: index must open with `{HEADER}`")
            return ids, errors
        match = ROW.match(line)
        if match:
            ids.append(match.group("id"))
            continue
        if CONTINUATION.match(line):
            continue
        errors.append(
            f"{location}: line {number} is neither a `- id:` row nor an indented "
            f"field: {line.strip()!r}"
        )
    if not header_seen:
        errors.append(f"{location}: index must open with `{HEADER}`")
    return ids, errors


def load_yaml(path: Path) -> tuple[object, str | None]:
    """Parse one YAML file; return (document, error)."""
    try:
        return yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader), None
    except yaml.YAMLError as exc:
        detail = " ".join(str(exc).split())
        return None, f"{path.name}: cannot parse: {detail}"


def read_index_rows(index: Path) -> tuple[dict[str, dict], list[str]]:
    """Return the index rows keyed by id, and any errors."""
    document, error = load_yaml(index)
    if error:
        return {}, [error]
    if not isinstance(document, dict) or "sessions" not in document:
        return {}, [f"{index.name}: `{HEADER}` must hold a list of rows"]
    listed = document["sessions"] if document["sessions"] is not None else []
    if not isinstance(listed, list):
        return {}, [f"{index.name}: `{HEADER}` must hold a list of rows"]
    rows: dict[str, dict] = {}
    errors: list[str] = []
    for row in listed:
        if not isinstance(row, dict) or "id" not in row:
            errors.append(f"{index.name}: row without an id: {row!r}")
            continue
        session_id = str(row["id"])
        missing = [field for field in ROW_FIELDS if field not in row]
        if missing:
            errors.append(f"{index.name} row {session_id} lacks {', '.join(missing)}")
            continue
        rows.setdefault(session_id, row)  # duplicates are reported by the line grammar
    return rows, errors


def blocks(document: dict, key: str) -> list[tuple[str, object]]:
    """Every block of `key` in file order, as (label, value).

    A block is the plain key, a `<key>_<suffix>` continuation at top level, or
    `<key>` inside a nested `turn_<n>:` mapping.
    """
    found: list[tuple[str, object]] = []
    for name, value in document.items():
        if name == key or name.startswith(key + "_"):
            found.append((name, value))
        elif TURN_BLOCK.match(name) and isinstance(value, dict) and key in value:
            found.append((f"{name}.{key}", value[key]))
    return found


def list_blocks(document: dict, key: str, location: str) -> tuple[list[tuple[str, list]], list[str]]:
    """The blocks of `key` as lists (an empty block may be spelled `null`)."""
    result: list[tuple[str, list]] = []
    errors: list[str] = []
    for label, value in blocks(document, key):
        if value is None:
            value = []
        if not isinstance(value, list):
            errors.append(f"{location}: `{label}` must be a list")
            continue
        result.append((label, value))
    return result, errors


def claim_id(entry: object) -> str | None:
    if isinstance(entry, str):
        return entry
    if isinstance(entry, dict) and isinstance(entry.get("id"), str):
        return entry["id"]
    return None


def project_session(path: Path) -> tuple[SessionProjection | None, list[str]]:
    """Read one session file and compute what its index row must say."""
    location = path.name
    document, error = load_yaml(path)
    if error:
        return None, [error]
    if not isinstance(document, dict) or not isinstance(document.get("session"), dict):
        return None, [f"{location}: must open with a `session:` mapping"]
    session = document["session"]
    errors: list[str] = []

    if str(session.get("id")) != path.stem:
        errors.append(f"{location}: session.id is {session.get('id')!r}, not {path.stem!r}")

    if "date" in session:
        date = str(session["date"])
    elif isinstance(session.get("timestamp"), str):
        date = session["timestamp"][:10]
    else:
        errors.append(f"{location}: session has neither `date` nor `timestamp`")
        date = ""

    if "turn_count" in session:
        turn_count = session["turn_count"]
        if not isinstance(turn_count, int):
            errors.append(f"{location}: session.turn_count must be an integer")
    elif "date" in session:
        errors.append(f"{location}: session.turn_count is missing")
        turn_count = None
    else:
        turn_count = None  # legacy timestamp shape: unchecked

    event_blocks, block_errors = list_blocks(document, EVENTS_KEY, location)
    errors.extend(block_errors)
    events_count = sum(len(entries) for _, entries in event_blocks)

    claims: set[str] = set()
    claim_blocks, block_errors = list_blocks(document, CLAIMS_KEY, location)
    errors.extend(block_errors)
    for label, entries in claim_blocks:
        for entry in entries:
            identifier = claim_id(entry)
            if identifier is None:
                errors.append(f"{location}: `{label}` entry without an id: {entry!r}")
            else:
                claims.add(identifier)

    thread_blocks, block_errors = list_blocks(document, THREADS_KEY, location)
    errors.extend(block_errors)
    open_threads = len(thread_blocks[-1][1]) if thread_blocks else 0

    if errors:
        return None, errors
    return (
        SessionProjection(date, turn_count, events_count, frozenset(claims), open_threads),
        [],
    )


def compare_row(session_id: str, row: dict, projection: SessionProjection) -> list[str]:
    """Every field on which the row and the file disagree."""
    errors: list[str] = []

    def disagree(field: str, row_value: object, file_value: object) -> None:
        errors.append(
            f"{session_id}: {field} is {row_value!r} in {INDEX_NAME} "
            f"but {file_value!r} in {session_id}.yaml"
        )

    if str(row["date"]) != projection.date:
        disagree("date", str(row["date"]), projection.date)
    if projection.turn_count is not None and row["turn_count"] != projection.turn_count:
        disagree("turn_count", row["turn_count"], projection.turn_count)
    if row["events_count"] != projection.events_count:
        disagree("events_count", row["events_count"], projection.events_count)
    row_claims = row["claims_touched"] or []
    if not isinstance(row_claims, list):
        errors.append(f"{session_id}: claims_touched in {INDEX_NAME} must be a list")
    elif sorted(str(claim) for claim in row_claims) != sorted(projection.claims_touched):
        disagree("claims_touched", sorted(str(c) for c in row_claims), sorted(projection.claims_touched))
    if row["open_threads"] != projection.open_threads:
        disagree("open_threads", row["open_threads"], projection.open_threads)
    return errors


def validate_sessions(sessions_dir: Path) -> ValidationResult:
    errors: list[str] = []
    index = sessions_dir / INDEX_NAME
    if not index.is_file():
        return ValidationResult(0, [f"missing index: {index}"])

    session_paths = sorted(sessions_dir.glob(SESSION_GLOB))
    session_ids = [path.stem for path in session_paths]
    if not session_ids:
        return ValidationResult(0, [f"no session files ({SESSION_GLOB}) under {sessions_dir}"])

    ids, errors = read_index_ids(index)
    if errors:
        return ValidationResult(0, errors)

    counts: dict[str, int] = {}
    for session_id in ids:
        counts[session_id] = counts.get(session_id, 0) + 1

    for session_id in session_ids:
        rows = counts.get(session_id, 0)
        if rows == 0:
            errors.append(f"{session_id}.yaml has no row in {INDEX_NAME}")
        elif rows > 1:
            errors.append(f"{session_id} has {rows} rows in {INDEX_NAME}")
    present = set(session_ids)
    for session_id in sorted(counts):
        if session_id not in present:
            errors.append(f"{INDEX_NAME} row {session_id} has no session file")

    rows, row_errors = read_index_rows(index)
    errors.extend(row_errors)
    for path in session_paths:
        row = rows.get(path.stem)
        if row is None or counts.get(path.stem, 0) != 1:
            continue
        projection, file_errors = project_session(path)
        if projection is None:
            errors.extend(file_errors)
            continue
        errors.extend(compare_row(path.stem, row, projection))

    return ValidationResult(checked=len(session_ids), errors=errors)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sessions-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent / "ara" / "trace" / "sessions",
    )
    args = parser.parse_args(argv)

    sessions_dir = args.sessions_dir.resolve()
    if not sessions_dir.is_dir():
        print(f"ARA session index: FAIL: missing sessions dir: {sessions_dir}", file=sys.stderr)
        return 2

    result = validate_sessions(sessions_dir)
    if result.errors:
        for error in result.errors:
            print(f"ARA session index: FAIL: {error}", file=sys.stderr)
        return 2

    print(
        f"ARA session index: PASS ({result.checked} sessions, one row each, "
        f"every row agreeing with its file)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
