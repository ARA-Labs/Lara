#!/usr/bin/env python3
"""Validate `*.lean:NNN` cross-references in docstrings, docs and scripts.

A `path:line` citation in prose is a silent-rot reference: nothing compiles it, so
it survives any edit that shifts lines and goes on pointing at whatever now sits
there. This gate resolves every such citation and fails when one no longer lands
on a declaration, or lands on a declaration other than the one the prose names.

A citation may be written with any suffix of the file's path — `Observation.lean`,
`Context/Observation.lean` and `lean/Lara/Context/Observation.lean` all resolve to
the same file. A suffix matching more than one file in the `lean/` tree is an
error: the fix is to lengthen the citation in the prose until it is unique, not to
guess which file was meant.

When the prose names a declaration beside the citation — the common shape
`` `foo_bar` (`path:NNN`) `` — the declaration at `NNN` must be `foo_bar`, so that
a citation which drifted onto its neighbour is caught and not just one that drifted
off declarations entirely. Where no single name is attached to the citation, or the
declaration is anonymous, only declaration-hood is checked.

`ara/` is deliberately NOT searched; see the comment on SEARCH_ROOTS below for
the two reasons, and `scripts/check_ara_source_spans.py` for the gate that does
cover it.

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
from collections import defaultdict
from pathlib import Path

# A trailing dash means a line RANGE (`Admission.lean:764-765`, or the en-dash
# spelling `Grounded.lean:601–606`); the range's end is prose, not a second
# citation, so ranges are skipped entirely rather than half-rewritten by a
# careless consumer of this pattern. A trailing `:column` is a Lean *diagnostic*
# (`AxCheck.lean:3:14`, quoted in `scripts/test-check-axioms.sh` fixtures), not a
# citation, and is skipped for the same reason: nobody maintains it as a pointer.
# The lookbehind keeps a partial path from matching inside a longer one.
PATH_AND_LINE = re.compile(
    r"(?<![A-Za-z0-9_./-])([A-Za-z0-9_./-]*\.lean):(\d+)(?![\d–—-])(?!:\d)"
)
DECL_PREFIX = (
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*"
    r"(?:def|theorem|lemma|abbrev|inductive|structure|instance|class|opaque|axiom)\b"
)
DECL = re.compile(DECL_PREFIX)
# The declared name, when the declaration has one written on the same line. An
# anonymous `instance : Foo := ...` has none, and then no name check is possible.
DECL_NAME = re.compile(DECL_PREFIX + r"\s+(?P<name>[^\s:({\[]+)")

# The prose name attached to a citation, in the overwhelmingly common shape
# `` `foo_bar` (`path:NNN`) ``. CITATION_LEAD is everything allowed between the
# closing backtick of the name and the citation itself; it is deliberately short,
# because a long gap means the name and the citation are not one phrase.
CITATION_LEAD = re.compile(r"[\s,;]{0,2}[(\[]?\s?(?:see\s|at\s|in\s|per\s)?`?$")
BACKTICKED_NAME = re.compile(r"`(?P<name>[^\W\d][\w.'!?]*)`$")
NAME_JOINER = re.compile(r"(?:[\s/,;]|\band\b|\bor\b)+$")
# `` `a` and `b` (`path:592`, `:595`) `` gives two names for two lines, so no one
# name is attached to this one citation. Both spellings of that shape — a second
# name before, a second line after — suppress the name check rather than guessing.
MULTI_LINE_REFERENCE = re.compile(r"^`?\s*(?:,|;|/|and\b|or\b)\s*`?:\d+")

# Citations that deliberately point at something other than a declaration.
# Keyed by the RESOLVED "lean/path:line"; the value is why it is exempt.
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
    "lean/Lara/Admission.lean:16": "cites the module header's validated-versus-verified sentence, which is the claim being made",
    "lean/Lara/Grounded.lean:288": "cites the `Classical.byContradiction` use site held up as the house idiom",
    "lean/Lara/Context/Surface.lean:53": "cites the `coveredB_relabel` proof step, which is the step being exercised",
    "lean/Lara/Check/Unit.lean:132": "cites `checkUnit`'s `ground : List Atom` parameter, not the function",
    "lean/Lara/Check/Unit.lean:151": "cites the `sigma := unit.sigma` retention line quoted verbatim beside it",
    "lean/Lara/Check/Unit.lean:234": "cites `checkUnit_complete`'s `Nodup` premise, not the theorem",
    "lean/Lara/Unit.lean:193": "cites the `attack_complete` structure field, not the structure",
    "lean/Lara/Unit.lean:198": "cites the `nodes_terms` structure field, not the structure",
    "lean/Lara/Unit.lean:204": "cites the `args_well_sorted` structure field, not the structure",
    "lean/Lara/Compile.lean:407": "cites `ConflictAttackable`'s `.leaf` arm, which is the arm being quoted",
    "lean/Lara/Compile.lean:478": "cites the `CheckedProgram.nodup` structure field, not the structure",
    "lean/Lara/Compile.lean:480": "cites the `CheckedProgram.complete` structure field, not the structure",
    "lean/Lara/Compile.lean:606": "quotes issue #68's stale reference verbatim, as the reference being corrected",
    "lean/Lara/Realizability.lean:167": "cites the `compiled_iso` structure field, not the structure",
    "lean/Lara/Attack.lean:85": "cites the `ContraryMatch` docstring's quantified-variable sentence",
    "lean/Lara/Attack.lean:549": "cites `HasAttack.rebut`'s `r.mode = .defeasible` hypothesis, not the inductive",
}

SEARCH_ROOTS = ("lean", "docs", "scripts", "README.md", "CLAUDE.md")
SKIP_DIRS = {".lake", ".git", "dist-newstyle", "node_modules", ".claude"}
# This gate's own test writes synthetic `Widget.lean:NNN` citations into a
# throwaway tree. They are fixtures for the resolver, not references into
# `lean/`, so scanning the test would report every fixture as a missing file.
SKIP_FILES = {"scripts/test_check_lean_citations.py"}

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
        for path in sorted(base.rglob("*")):
            if not path.is_file() or path.suffix not in TEXT_SUFFIXES:
                continue
            relative = path.relative_to(repo_root)
            if any(part in SKIP_DIRS for part in relative.parts):
                continue
            if relative.as_posix() in SKIP_FILES:
                continue
            yield path


def build_lean_index(repo_root: Path) -> dict[str, list[str]]:
    """Map every path suffix of every `lean/**/*.lean` file to the files it names.

    A citation is looked up as written, so `Observation.lean` and
    `Context/Observation.lean` are both keys; a key with two values is the
    ambiguity the caller must report rather than resolve.
    """
    index: dict[str, list[str]] = defaultdict(list)
    base = repo_root / "lean"
    if not base.is_dir():
        return index
    for path in sorted(base.rglob("*.lean")):
        relative = path.relative_to(repo_root)
        if any(part in SKIP_DIRS for part in relative.parts):
            continue
        parts = relative.parts
        for start in range(len(parts)):
            index["/".join(parts[start:])].append(relative.as_posix())
    return index


def declaration_name(line: str) -> str | None:
    match = DECL_NAME.match(line)
    return match.group("name") if match else None


def prose_name_for(prefix: str, suffix: str) -> str | None:
    """The declaration name the prose attaches to a citation, when there is one.

    `prefix` is the text before the citation on its line and `suffix` the text
    after. Returns None whenever the attachment is not unambiguous — no adjacent
    name, several names sharing the citation, or several lines sharing the names.
    """
    if MULTI_LINE_REFERENCE.match(suffix):
        return None
    lead = CITATION_LEAD.search(prefix)
    if lead is None:
        return None
    head = prefix[: lead.start()]
    name = BACKTICKED_NAME.search(head)
    if name is None:
        return None
    before = head[: name.start()]
    joiner = NAME_JOINER.search(before)
    if joiner is not None and BACKTICKED_NAME.search(before[: joiner.start()]):
        return None
    return name.group("name")


def names_agree(prose: str, declared: str) -> bool:
    """Whether a prose name and a declared name can denote the same declaration.

    Prose qualifies freely — `Consistency.contrary_args_not_both_grounded` for a
    `theorem contrary_args_not_both_grounded` inside `namespace Consistency` — so
    the shorter dotted name must be a suffix of the longer one.
    """
    prose_parts = prose.split(".")
    declared_parts = declared.split(".")
    shared = min(len(prose_parts), len(declared_parts))
    return prose_parts[-shared:] == declared_parts[-shared:]


def check_repo(repo_root: Path) -> tuple[int, set[str], list[str]]:
    index = build_lean_index(repo_root)
    contents: dict[str, list[str]] = {}
    errors: list[str] = []
    checked = 0
    used_allowlist: set[str] = set()

    for source in iter_files(repo_root):
        try:
            text = source.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        if ".lean:" not in text:
            continue
        rel_source = source.relative_to(repo_root)
        for lineno, line in enumerate(text.split("\n"), 1):
            for match in PATH_AND_LINE.finditer(line):
                cited, num = match.group(1), int(match.group(2))
                where = f"{rel_source}:{lineno}"
                candidates = index.get(cited, [])
                if not candidates:
                    errors.append(f"{where} cites missing file {cited}")
                    continue
                if len(candidates) > 1:
                    errors.append(
                        f"{where} cites {cited}:{num}, an ambiguous suffix matching "
                        f"{' and '.join(candidates)}; lengthen the path in the prose"
                    )
                    continue
                target = candidates[0]
                if target not in contents:
                    contents[target] = (
                        (repo_root / target).read_text(encoding="utf-8").split("\n")
                    )
                lines = contents[target]
                key = f"{target}:{num}"
                checked += 1
                if key in ALLOWLIST:
                    used_allowlist.add(key)
                    continue
                if num > len(lines):
                    errors.append(
                        f"{where} cites {key}, past end of file ({len(lines)} lines)"
                    )
                    continue
                if not DECL.match(lines[num - 1]):
                    errors.append(
                        f"{where} cites {key}, which is not a declaration "
                        f"(add to ALLOWLIST in {Path(__file__).name} if deliberate)"
                    )
                    continue
                prose = prose_name_for(line[: match.start()], line[match.end() :])
                declared = declaration_name(lines[num - 1])
                if prose is None or declared is None:
                    continue
                if not names_agree(prose, declared):
                    errors.append(
                        f"{where} names `{prose}` but {key} declares `{declared}`"
                    )

    for key in sorted(set(ALLOWLIST) - used_allowlist):
        errors.append(f"ALLOWLIST entry {key} is unused; remove it")

    return checked, used_allowlist, errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root", type=Path, default=Path(__file__).resolve().parent.parent
    )
    args = parser.parse_args(argv)

    checked, used_allowlist, errors = check_repo(args.repo_root.resolve())

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
