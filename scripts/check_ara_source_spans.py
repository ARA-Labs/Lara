#!/usr/bin/env python3
"""Validate repository-local located quotations in ARA Sources entries."""

from __future__ import annotations

import argparse
import re
import sys
import unicodedata
from dataclasses import dataclass
from pathlib import Path


LOCATED_QUOTE = re.compile(
    r"←\s+`?(?P<path>[A-Za-z0-9_./-]+\.[A-Za-z0-9_-]+):"
    r"(?P<start>[0-9]+)(?:[-–](?P<end>[0-9]+))?`?\s+"
    r"«(?P<quote>[^»]+)»"
)


@dataclass(frozen=True)
class ValidationResult:
    checked: int
    errors: list[str]


def normalize(text: str) -> str:
    collapsed = " ".join(unicodedata.normalize("NFC", text).split())
    return re.sub(r"\s+([,;])", r"\1", collapsed)


def resolve_source(repo_root: Path, relative: str) -> Path | None:
    candidate = (repo_root / relative).resolve()
    try:
        candidate.relative_to(repo_root.resolve())
    except ValueError:
        return None
    return candidate


def validate_tree(repo_root: Path, artifact_root: Path) -> ValidationResult:
    errors: list[str] = []
    checked = 0

    for artifact in sorted(artifact_root.rglob("*.md")):
        text = artifact.read_text(encoding="utf-8")
        artifact_name = artifact.relative_to(repo_root)
        for match in LOCATED_QUOTE.finditer(text):
            checked += 1
            citation_line = text.count("\n", 0, match.start()) + 1
            location = f"{artifact_name}:{citation_line}"
            relative = match.group("path")
            start = int(match.group("start"))
            end = int(match.group("end") or match.group("start"))
            source = resolve_source(repo_root, relative)

            if source is None:
                errors.append(f"{location}: source path escapes repository: {relative}")
                continue
            if not source.is_file():
                errors.append(f"{location}: source file does not exist: {relative}")
                continue
            if start < 1 or end < start:
                errors.append(f"{location}: invalid range {start}-{end}: {relative}")
                continue

            source_lines = source.read_text(encoding="utf-8").splitlines()
            if end > len(source_lines):
                errors.append(
                    f"{location}: {relative} range {start}-{end} exceeds "
                    f"{len(source_lines)} lines"
                )
                continue

            cited_text = normalize("\n".join(source_lines[start - 1 : end]))
            quote = normalize(match.group("quote"))
            fragments = [normalize(fragment) for fragment in quote.split(" / ")]
            cursor = 0
            missing = None
            for fragment in fragments:
                found = cited_text.find(fragment, cursor)
                if found < 0:
                    missing = fragment
                    break
                cursor = found + len(fragment)

            if missing is not None:
                if len(fragments) == 1:
                    reason = "quotation not found in cited range"
                else:
                    reason = "quotation fragment not found in order"
                errors.append(
                    f"{location}: {reason}: {relative}:{start}-{end}: {missing!r}"
                )

    return ValidationResult(checked=checked, errors=errors)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parent.parent
    )
    parser.add_argument("--artifact-root", type=Path)
    args = parser.parse_args(argv)

    repo_root = args.repo_root.resolve()
    artifact_root = (
        args.artifact_root.resolve() if args.artifact_root else repo_root / "ara"
    )
    if not artifact_root.is_dir():
        print(f"ARA source spans: FAIL: missing artifact root: {artifact_root}", file=sys.stderr)
        return 1

    result = validate_tree(repo_root, artifact_root)
    if result.checked == 0:
        print("ARA source spans: FAIL: no ranged quotations found", file=sys.stderr)
        return 1
    if result.errors:
        for error in result.errors:
            print(f"ARA source spans: FAIL: {error}", file=sys.stderr)
        return 1

    print(f"ARA source spans: PASS ({result.checked} quotations)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
