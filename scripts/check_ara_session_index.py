#!/usr/bin/env python3
"""Assert that ara/trace/sessions/session_index.yaml is total and unique (#337).

The index is the only enumeration of the trace, so two failure modes are
silent to every consumer that reads it: a session file with no row (invisible),
and an id with two rows (the first match wins and may be stale). This gate
holds the index to a bijection with the session files beside it:

- every ``2*.yaml`` under the sessions directory has exactly one ``- id:`` row;
- no id appears in more than one row;
- no row names a session file that does not exist.

The index is a flat YAML list whose rows begin at column 0 with ``- id:``. The
gate reads exactly that grammar with the standard library, and rejects any
other column-0 content rather than guessing at it, so a reshaped index fails
loudly instead of being half-read. A stray or duplicate names itself and the
gate exits 2.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


INDEX_NAME = "session_index.yaml"
SESSION_GLOB = "2*.yaml"
HEADER = "sessions:"
ROW = re.compile(r"^- id:\s*(?P<quote>['\"]?)(?P<id>[^'\"\s#]+)(?P=quote)\s*(?:#.*)?$")
CONTINUATION = re.compile(r"^\s+\S")


@dataclass(frozen=True)
class ValidationResult:
    checked: int
    errors: list[str]


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


def validate_sessions(sessions_dir: Path) -> ValidationResult:
    errors: list[str] = []
    index = sessions_dir / INDEX_NAME
    if not index.is_file():
        return ValidationResult(0, [f"missing index: {index}"])

    session_ids = sorted(path.stem for path in sessions_dir.glob(SESSION_GLOB))
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

    print(f"ARA session index: PASS ({result.checked} sessions, one row each)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
