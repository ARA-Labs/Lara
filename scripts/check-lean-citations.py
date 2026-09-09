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

A citation may also be written with no file at all — the bare `` `foo` (:256) ``
shape `docs/paper-lean-name-map.md` uses inside a table row — or as a line RANGE,
`Compile.lean:120-123`. Both are resolved rather than skipped.

A file-less citation takes its file from the declaration the prose names beside
it, unless the block it sits in names a `*.lean` file outright, which wins; and
failing both, from a fully-spelled citation standing beside it in the same
enumeration. Where none of the three determines one file the citation is skipped,
because a mis-attributed citation is worse than an unchecked one — see
`bare_target`.

A range is resolved at its START line, exactly as a single line is. Its end is
checked only for being a later line of the same file and is never rewritten: how
long the cited block ought to be is a judgment the prose makes and this gate does
not.

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

# A citation is `path:line`, `path:start-end` (the en-dash spelling
# `Grounded.lean:629–634` is equally common), or the bare `:line` / `:start-end`
# that names no file and is resolved by BARE_FILE_CARRY below. A trailing
# `:column` is a Lean *diagnostic* (`AxCheck.lean:3:14`, quoted in
# `scripts/test-check-axioms.sh` fixtures), not a citation, and is skipped: nobody
# maintains it as a pointer. The lookbehind keeps a partial path from matching
# inside a longer one, and keeps the `:14` of a diagnostic from being read as a
# bare citation.
CITATION = re.compile(
    r"(?<![A-Za-z0-9_./:-])(?:(?P<path>[A-Za-z0-9_./-]*\.lean))?"
    r":(?P<start>\d+)(?:[–—-](?P<end>\d+))?(?![\d–—-])(?!:\d)"
)
# A `*.lean` path named with no line at all — `` `lean/AxCheck.lean` already
# #print axioms-gates every headline row: `srcStatus_iff_checked` (:381) `` — is
# not a citation but a statement of what the surrounding block is about, and
# BLOCK subjects are what stops a file-less citation being resolved against the
# declaration's home file when the block plainly means a different file.
BARE_FILE_MENTION = re.compile(r"(?<![A-Za-z0-9_./:-])([A-Za-z0-9_./-]*\.lean)(?!:\d)")
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

# The text a bare `:NNN` may be separated from the fully-spelled citation whose
# file it borrows: `` (`RA.lean:251`, `:256`) `` and
# `` (`Insp.lean:595`; `inspReplay_iff` :344) `` carry, and anything with a
# bracket, a pipe, a dash or a second clause of prose in it does not. The carry is
# only the fallback, used where the prose names no declaration this gate can
# locate, so it is deliberately narrow: one enumeration, at most one intervening
# name. Backticks are stripped before matching, being pure decoration here.
BARE_FILE_CARRY = re.compile(
    r"^[\s,;/]*(?:(?:and|or)\s+)?(?:[A-Za-z_][\w.']*\s*)?(?:(?:and|or)\s+)?[\s,;/]*$"
)

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
    "lean/Lara/Attack.lean:550": "cites `HasAttack.rebut`'s `r.mode = .defeasible` hypothesis, not the inductive",
    # Range starts. A range is resolved at its first line only, so what is
    # exempted here is that line: the block's opening, not its extent.
    "lean/Lara/Compile.lean:43": "cites the module header's identical-terms-identical-edges paragraph, which is the claim being made",
    "lean/Lara/Compile.lean:632": "cites `edgeB_iff`'s `DisNodup` discharge steps, quoted as the pattern to follow",
    "lean/Lara/Compile.lean:668": "cites the `mutual` block opening `SrcIn`/`SrcOut`, which is what makes the judgment mutual",
    "lean/Lara/Examples.lean:368": "cites the `ord@1` registry-behaviour comment, which says in words what the citation quotes",
    "lean/Lara/Grounded.lean:7": "cites the module header's scope paragraph",
    "lean/Lara/Grounded.lean:629": "cites the `status_preservation` docstring, not the theorem below it",
    "lean/Lara/Policy.lean:236": "cites the conservative instance-overlap section comment, not a declaration",
    "lean/Lara/Update.lean:281": "cites the sufficient-condition-preservation section comment, which names the Γ-weakening lemmas",
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


def build_declaration_index(repo_root: Path) -> dict[str, list[tuple[str, str]]]:
    """Map every declared name in `lean/` to the (name, file) pairs declaring it.

    Keyed by the name's last dotted component so a lookup can accept the prose's
    freer qualification, exactly as `names_agree` does. A bare `` `foo` (:256) ``
    citation names no file, so this index is how the file is recovered: `foo` is
    looked up, and the citation resolves only when every hit is in one file.
    """
    index: dict[str, list[tuple[str, str]]] = defaultdict(list)
    base = repo_root / "lean"
    if not base.is_dir():
        return index
    for path in sorted(base.rglob("*.lean")):
        relative = path.relative_to(repo_root)
        if any(part in SKIP_DIRS for part in relative.parts):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        for line in text.split("\n"):
            name = declaration_name(line)
            if name is not None:
                index[name.split(".")[-1]].append((name, relative.as_posix()))
    return index


def file_declaring(
    decl_index: dict[str, list[tuple[str, str]]], prose: str
) -> str | None:
    """The one `lean/` file declaring `prose`, or None when that is not unique."""
    hits = {
        relative
        for declared, relative in decl_index.get(prose.split(".")[-1], [])
        if names_agree(prose, declared)
    }
    return hits.pop() if len(hits) == 1 else None


def block_subjects(text: str, index: dict[str, list[str]]) -> list[set[str]]:
    """Per line of `text`, the `lean/` files its block names without a line number.

    A block is a run of non-blank lines, except that a markdown table row is a
    block of its own: a table's columns each speak about a different file, so what
    one row is about says nothing about the next. Only file names that resolve
    unambiguously count; an unresolvable one names nothing.
    """
    lines = text.split("\n")
    subjects: list[set[str]] = [set() for _ in lines]
    start = 0
    while start < len(lines):
        if not lines[start].strip():
            start += 1
            continue
        stop = start + 1
        if not lines[start].lstrip().startswith("|"):
            while stop < len(lines) and lines[stop].strip():
                if lines[stop].lstrip().startswith("|"):
                    break
                stop += 1
        named: set[str] = set()
        for line in lines[start:stop]:
            for match in BARE_FILE_MENTION.finditer(line):
                candidates = index.get(match.group(1), [])
                if len(candidates) == 1:
                    named.add(candidates[0])
        for offset in range(start, stop):
            subjects[offset] = named
        start = stop
    return subjects


def check_repo(repo_root: Path) -> tuple[int, set[str], list[str]]:
    index = build_lean_index(repo_root)
    decl_index = build_declaration_index(repo_root)
    contents: dict[str, list[str]] = {}
    errors: list[str] = []
    checked = 0
    used_allowlist: set[str] = set()

    def file_lines(target: str) -> list[str]:
        if target not in contents:
            contents[target] = (
                (repo_root / target).read_text(encoding="utf-8").split("\n")
            )
        return contents[target]

    def bare_target(
        prose: str | None,
        subjects: set[str],
        carry: tuple[str, int] | None,
        gap: str,
    ) -> str | None:
        """The file a file-less `:NNN` citation refers to, or None to skip it.

        The prose name comes first because it is exact: `` `raReplay_iff` (:256) ``
        says which declaration is meant, and one declaration lives in one file.
        `subjects` overrides it, because a block that names a file outright —
        `` `lean/AxCheck.lean` ... `srcStatus_iff_checked` (:381) `` — is citing
        THAT file's line 381, not the line where the named theorem is proved. The
        carry is the last resort, for the shapes that attach no name at all —
        `` (`Linking.lean:43` and `:47`) `` — and is narrow on purpose.

        None of the three applying means the file is genuinely undetermined, and
        an undetermined citation is skipped rather than guessed at.
        """
        if prose is not None:
            named = file_declaring(decl_index, prose)
            if named is not None and (not subjects or named in subjects):
                return named
        if carry is not None and len(gap) <= 60:
            if BARE_FILE_CARRY.match(gap.replace("`", "")):
                return carry[0]
        return None

    for source in iter_files(repo_root):
        try:
            text = source.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        rel_source = source.relative_to(repo_root)
        subjects = block_subjects(text, index)
        for lineno, line in enumerate(text.split("\n"), 1):
            # The file a bare citation may borrow, and the offset the citation
            # that supplied it ended at. Reset per line: the carry is an
            # enumeration-local reading, and an enumeration does not wrap.
            carry: tuple[str, int] | None = None
            for match in CITATION.finditer(line):
                where = f"{rel_source}:{lineno}"
                num = int(match.group("start"))
                last = match.group("end")
                prose = prose_name_for(line[: match.start()], line[match.end() :])
                cited = match.group("path")
                if cited is None:
                    gap = line[carry[1] : match.start()] if carry else ""
                    target = bare_target(prose, subjects[lineno - 1], carry, gap)
                    if target is None:
                        continue
                else:
                    candidates = index.get(cited, [])
                    if not candidates:
                        errors.append(f"{where} cites missing file {cited}")
                        carry = None
                        continue
                    if len(candidates) > 1:
                        errors.append(
                            f"{where} cites {cited}:{num}, an ambiguous suffix matching "
                            f"{' and '.join(candidates)}; lengthen the path in the prose"
                        )
                        carry = None
                        continue
                    target = candidates[0]
                carry = (target, match.end())

                lines_of = file_lines(target)
                key = f"{target}:{num}"
                span = key if last is None else f"{key}-{last}"
                checked += 1
                if num > len(lines_of):
                    errors.append(
                        f"{where} cites {span}, past end of file "
                        f"({len(lines_of)} lines)"
                    )
                    continue
                # Marked before the range checks below, which are about the end
                # and so do not stop the start from being a deliberate exemption.
                exempt = key in ALLOWLIST
                if exempt:
                    used_allowlist.add(key)
                # A range's end is prose — the gate does not claim to know how
                # long the cited block ought to be — so it is checked only for
                # being a later line of the same file, never rewritten.
                if last is not None:
                    if int(last) <= num:
                        errors.append(
                            f"{where} cites {span}, whose range ends at or before "
                            f"its start"
                        )
                        continue
                    if int(last) > len(lines_of):
                        errors.append(
                            f"{where} cites {span}, whose range ends past end of "
                            f"file ({len(lines_of)} lines)"
                        )
                        continue
                if exempt:
                    continue
                if not DECL.match(lines_of[num - 1]):
                    errors.append(
                        f"{where} cites {key}, which is not a declaration "
                        f"(add to ALLOWLIST in {Path(__file__).name} if deliberate)"
                    )
                    continue
                declared = declaration_name(lines_of[num - 1])
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
