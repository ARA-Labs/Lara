#!/usr/bin/env python3
"""Validate `lean/**/*.lean:NNN` cross-references in docstrings, docs and scripts.

A `path:line` citation in prose is a silent-rot reference: nothing compiles it, so
it survives any edit that shifts lines and goes on pointing at whatever now sits
there. This gate resolves every such citation and fails when one no longer lands
on a declaration.

`ara/` is deliberately NOT searched; see the comment on SEARCH_ROOTS below for
the two reasons, and `scripts/check_ara_source_spans.py` for the gate that does
cover it.

**Two known blind spots (#282).** The citation must be written with the `lean/`
prefix or this gate never sees it, and a citation that lands on the *wrong*
declaration still passes because only declaration-hood is checked, not the name
the surrounding prose gives.

Deliberate citations of a non-declaration line — a proof step, a structure field,
a module header — are legitimate and are declared in ALLOWLIST below, each with a
reason. Anything else must resolve to a `def`/`theorem`/`abbrev`/`inductive`/
`structure`/`instance`/`class`.

Usage:
    scripts/check-lean-citations.py [--repo-root PATH]
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

# A trailing "-" means a line RANGE (`Admission.lean:764-765`); the range's end is
# prose, not a second citation, so only the start is resolved and ranges are skipped
# entirely rather than half-rewritten by a careless consumer of this pattern.
PATH_AND_LINE = re.compile(r"\b(lean/[A-Za-z0-9_./-]*\.lean):(\d+)(?![\d-])")
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|theorem|lemma|abbrev|inductive|structure|instance|class|opaque|axiom)\b"
)

# Citations that deliberately point at something other than a declaration.
# Keyed by "path:line" as written; the value is why it is exempt.
ALLOWLIST: dict[str, str] = {
    "lean/Lara/Erase.lean:267": "cites the one-rewrite proof step itself, which is the point being made",
    "lean/Lara/Context/Link.lean:631": "cites the `attack_complete` structure field, not the structure",
    "lean/Lara/Observation.lean:545": "cites the prose paragraph on List.nodup_range, not a declaration",
    "lean/Lara/Consistency.lean:42": "pre-existing: cites a proof step inside statusC_justified_iff",
    "lean/Lara/Consistency.lean:165": "pre-existing: cites a continuation line of a theorem statement",
    "lean/Lara/Unit.lean:35": "pre-existing: cites a blank separator line",
    "lean/Lara/Policy.lean:448": "pre-existing: cites a docstring opening, not the declaration below it",
    "lean/Lara/Admission.lean:764": "pre-existing: cites a proof step",
    "lean/Lara/Driver.lean:1": "cites the module header block",
    "lean/Lara/Support.lean:60": "cites the module header's Forall₂ design bullet, not a declaration",
    "lean/Lara/Context/Observation.lean:97": "cites the `open` line itself, which is what the comparison is about",
    "lean/Lara/Context/Equivalence.lean:43": "cites the `open` line itself, which is what the comparison is about",
}

SEARCH_ROOTS = ("lean", "docs", "scripts", "README.md", "CLAUDE.md")
SKIP_DIRS = {".lake", ".git", "dist-newstyle", "node_modules", ".claude"}

# `ara/` is deliberately outside this gate, for two different reasons.
# `ara/trace/`, `ara/staging/` and `ara/evidence/` are append-only journey records:
# their citations describe the tree AS IT WAS when the entry was written, so
# re-pointing them at today's lines would falsify the record. `ara/logic/` is
# mutable, but its citations are `Sources` quotations that deliberately point at a
# CONTENT line and carry the matched text verbatim — `scripts/check_ara_source_spans.py`
# validates those by comparing the quote, which is strictly stronger than resolving
# a line to a declaration. The two gates are disjoint on purpose.
TEXT_SUFFIXES = {".lean", ".md", ".yaml", ".yml", ".py", ".sh", ".hs", ".txt"}


def iter_files(repo_root: Path):
    for root in SEARCH_ROOTS:
        base = repo_root / root
        if base.is_file():
            yield base
            continue
        if not base.is_dir():
            continue
        for path in base.rglob("*"):
            if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
                continue
            if any(part in SKIP_DIRS for part in path.relative_to(repo_root).parts):
                continue
            yield path


def declaration_lines(path: Path) -> set[int]:
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return set()
    return {i for i, line in enumerate(text.split("\n"), 1) if DECL.match(line)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parent.parent
    )
    args = parser.parse_args(argv)
    repo_root = args.repo_root.resolve()

    decl_cache: dict[str, set[int]] = {}
    line_count: dict[str, int] = {}
    errors: list[str] = []
    checked = 0
    used_allowlist: set[str] = set()

    for source in iter_files(repo_root):
        try:
            text = source.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if "lean/" not in text:
            continue
        rel_source = source.relative_to(repo_root)
        for lineno, line in enumerate(text.split("\n"), 1):
            for match in PATH_AND_LINE.finditer(line):
                target, num = match.group(1), int(match.group(2))
                key = f"{target}:{num}"
                target_path = repo_root / target
                if not target_path.is_file():
                    errors.append(f"{rel_source}:{lineno} cites missing file {target}")
                    continue
                if target not in decl_cache:
                    decl_cache[target] = declaration_lines(target_path)
                    line_count[target] = len(
                        target_path.read_text(encoding="utf-8").split("\n")
                    )
                checked += 1
                if key in ALLOWLIST:
                    used_allowlist.add(key)
                    continue
                if num > line_count[target]:
                    errors.append(
                        f"{rel_source}:{lineno} cites {key}, past end of file "
                        f"({line_count[target]} lines)"
                    )
                elif num not in decl_cache[target]:
                    errors.append(
                        f"{rel_source}:{lineno} cites {key}, which is not a declaration "
                        f"(add to ALLOWLIST in {Path(__file__).name} if deliberate)"
                    )

    stale = sorted(set(ALLOWLIST) - used_allowlist)
    for key in stale:
        errors.append(f"ALLOWLIST entry {key} is unused; remove it")

    if checked == 0:
        print("Lean citations: FAIL: no citations found", file=sys.stderr)
        return 1
    if errors:
        for error in errors:
            print(f"Lean citations: FAIL: {error}", file=sys.stderr)
        return 1

    print(
        f"Lean citations: PASS ({checked} citations, "
        f"{len(used_allowlist)} allowlisted)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
