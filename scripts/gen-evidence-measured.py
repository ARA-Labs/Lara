#!/usr/bin/env python3
"""Materialize the additive certified-evidence measured-input corpus.

Usage:
    scripts/gen-evidence-measured.py            # write fixtures/evidence/measured/
    scripts/gen-evidence-measured.py --check    # prove the committed bytes regenerate

The corpus is declared here and derived deterministically from the committed
``fixtures/evidence/quarantined`` package: each rejected input is that package
with exactly one targeted edit (and, where the edit moves bytes a manifest
entry covers, a re-pinned manifest).  Nothing outside ``fixtures/evidence/
measured/`` is written, and no original package or historical record is
touched.  ``--check`` is the standing gate: a tree that no longer regenerates
its own corpus fails it, exactly as ``gen-mutants.hs --check`` guards the
mutation suite.

The accepted inputs are *not* generated: they are the real committed packages,
measured in place by ``scripts/evidence-measure.py``.
"""

from __future__ import annotations

import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import evidence_measured as em  # noqa: E402

OUT_ROOT = Path("fixtures/evidence/measured")
BASE = em.REPO_ROOT / "fixtures/evidence/quarantined"

#: Accepted inputs: real committed packages, measured in place.
ACCEPTED_ROWS = [
    {
        "case": "package-a",
        "root": "examples/certified-evidence/package-a",
        "policy": "-",
        "expect": "accepted",
        "leaf": "-",
        "reason": "-",
        "checked": "forward-1631,forward-1632",
        "declared": "-",
        "assurance": "evidence-checked",
    },
    {
        "case": "package-b",
        "root": "examples/certified-evidence/package-b",
        "policy": "-",
        "expect": "accepted",
        "leaf": "-",
        "reason": "-",
        "checked": "train-0,train-1,train-2,loss-0,loss-1,loss-2,loss-3,loss-4",
        "declared": "-",
        "assurance": "evidence-checked",
    },
    {
        # Identical verifier policy bytes: the core and dependency identities must
        # not move, only the evidence identity (policy origin).
        "case": "package-a-verifier-policy",
        "root": "examples/certified-evidence/package-a",
        "policy": "examples/certified-evidence/package-a/certified-componet.policy.lara",
        "expect": "accepted",
        "leaf": "-",
        "reason": "-",
        "checked": "forward-1631,forward-1632",
        "declared": "-",
        "assurance": "evidence-checked",
    },
    {
        # The committed synthetic quarantine fixture: the certified leaf is
        # checked through its request, the observed leaf stays declared.
        "case": "quarantined-mixed",
        "root": "fixtures/evidence/quarantined",
        "policy": "-",
        "expect": "accepted",
        "leaf": "-",
        "reason": "-",
        "checked": "drop",
        "declared": "keep",
        "assurance": "mixed",
    },
]

#: Rejected inputs: one edit each, applied to a copy of ``fixtures/evidence/quarantined``.
REJECTED_ROWS = [
    {
        "case": "reject-admission",
        "root": "fixtures/evidence/measured/reject-admission",
        "policy": "-",
        "expect": "policy",
        "leaf": "drop",
        "reason": "-",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "policy admission table maps (certified, checker(csv-row, 1)) to reject",
    },
    {
        "case": "reject-binding",
        "root": "fixtures/evidence/measured/reject-binding",
        "policy": "-",
        "expect": "binding",
        "leaf": "drop",
        "reason": "object does not resolve an existing leaf reference",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "the certified leaf's refs no longer name the requested object's path",
    },
    {
        "case": "reject-capture",
        "root": "fixtures/evidence/measured/reject-capture",
        "policy": "-",
        "expect": "capture",
        "leaf": "drop",
        "reason": "object SHA256 mismatch",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "the requested object's bytes move without re-pinning the manifest",
    },
    {
        "case": "reject-extraction",
        "root": "fixtures/evidence/measured/reject-extraction",
        "policy": "-",
        "expect": "extraction",
        "leaf": "drop",
        "reason": "extracted proposition mismatch",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "the selected original value moves and the manifest is re-pinned",
    },
    {
        "case": "reject-selection",
        "root": "fixtures/evidence/measured/reject-selection",
        "policy": "-",
        "expect": "extraction",
        "leaf": "drop",
        "reason": "missing CSV key row",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "the CSV request names a key value the original table does not contain",
    },
    {
        "case": "invalid-global-digest",
        "root": "fixtures/evidence/measured/invalid-global-digest",
        "policy": "-",
        "expect": "invalid",
        "leaf": "-",
        "reason": "object SHA256 mismatch",
        "checked": "-",
        "declared": "-",
        "assurance": "-",
        "hint": "a global manifest object digest is wrong: package invalidity, exit 2",
    },
]


def replace_once(path: Path, before: str, after: str) -> None:
    text = path.read_text(encoding="utf-8")
    if text.count(before) != 1:
        raise ValueError(f"mutation target {before!r} is not unique in {path}")
    path.write_text(text.replace(before, after, 1), encoding="utf-8")


def repin(root: Path, *ids: str) -> None:
    """Re-pin the length and digest of named manifest objects from their bytes."""
    manifest_path = root / em.EVIDENCE_MANIFEST
    value = em.parse(manifest_path.read_bytes())
    wanted = set(ids)
    seen = set()
    for entry in em.field(value, "objects"):
        if entry[1] in wanted:
            raw = (root / entry[2]).read_bytes()
            entry[3] = str(len(raw))
            entry[4] = em.sha256_label(raw)
            seen.add(entry[1])
    missing = wanted - seen
    if missing:
        raise ValueError(f"manifest names no object {sorted(missing)}")
    manifest_path.write_bytes(em.canonical(value))


def set_manifest_digest(root: Path, ident: str, digest: str) -> None:
    manifest_path = root / em.EVIDENCE_MANIFEST
    value = em.parse(manifest_path.read_bytes())
    for entry in em.field(value, "objects"):
        if entry[1] == ident:
            entry[4] = digest
            manifest_path.write_bytes(em.canonical(value))
            return
    raise ValueError(f"manifest names no object {ident!r}")


def build_case(case: str, destination: Path) -> None:
    """Copy the base package and apply the case's single declared edit."""
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(BASE, destination)
    manifest_path = destination / em.EVIDENCE_MANIFEST
    base_value = em.parse((BASE / em.EVIDENCE_MANIFEST).read_bytes())
    if em.canonical(base_value) != (BASE / em.EVIDENCE_MANIFEST).read_bytes():
        raise ValueError("the base package manifest is not canonical")

    if case == "reject-admission":
        replace_once(destination / "surface-policy.policy.lara",
                     "checker(csv-row, 1)) = quarantine",
                     "checker(csv-row, 1)) = reject")
        repin(destination, "policy")
    elif case == "reject-binding":
        replace_once(destination / "artifact.lara",
                     "[evidence/measurements.csv]",
                     "[evidence/other.csv]")
        repin(destination, "source")
    elif case == "reject-capture":
        replace_once(destination / "evidence/measurements.csv", "drop,7", "drop,9")
        # Deliberately no re-pin: the manifest still declares the original bytes.
    elif case == "reject-extraction":
        replace_once(destination / "evidence/measurements.csv", "drop,7", "drop,8")
        repin(destination, "measurements")
    elif case == "reject-selection":
        replace_once(destination / "artifact.lara", "(key id drop)", "(key id absent)")
        repin(destination, "source")
    elif case == "invalid-global-digest":
        set_manifest_digest(destination, "paper", "sha256:" + "0" * 64)
    else:
        raise ValueError(f"unknown case {case!r}")


def corpus_rows() -> list[dict]:
    rows = []
    for row in ACCEPTED_ROWS + REJECTED_ROWS:
        rows.append({column: row[column] for column in em.CORPUS_COLUMNS})
    return rows


def manifest_text() -> str:
    lines = ["\t".join(em.CORPUS_COLUMNS)]
    for row in corpus_rows():
        lines.append("\t".join(row[column] for column in em.CORPUS_COLUMNS))
    return "\n".join(lines) + "\n"


def generate(root: Path) -> None:
    (root / OUT_ROOT).mkdir(parents=True, exist_ok=True)
    for row in REJECTED_ROWS:
        build_case(row["case"], root / row["root"])
    (root / OUT_ROOT / "MANIFEST.tsv").write_text(manifest_text(), encoding="utf-8")


def tree_files(root: Path) -> dict[str, bytes]:
    files = {}
    for path in sorted(root.rglob("*"), key=lambda p: p.relative_to(root).as_posix()):
        if path.is_dir():
            continue
        files[path.relative_to(root).as_posix()] = path.read_bytes()
    return files


def check(root: Path) -> int:
    committed_root = root / OUT_ROOT
    if not committed_root.is_dir():
        print(f"FAIL: no committed corpus at {OUT_ROOT}", file=sys.stderr)
        return 1
    with tempfile.TemporaryDirectory(prefix="lara-evidence-corpus.") as temporary:
        staged = Path(temporary)
        generate(staged)
        committed = tree_files(committed_root)
        staged_files = tree_files(staged / OUT_ROOT)
        failures = []
        for name in sorted(set(committed) | set(staged_files)):
            if name not in committed:
                failures.append(f"missing committed file: {OUT_ROOT}/{name}")
            elif name not in staged_files:
                failures.append(f"stale committed file: {OUT_ROOT}/{name}")
            elif committed[name] != staged_files[name]:
                failures.append(f"differs: {OUT_ROOT}/{name}")
        if failures:
            for failure in failures:
                print(f"FAIL: {failure}", file=sys.stderr)
            return 1
    print(f"PASS: {OUT_ROOT} regenerates byte-identically "
          f"({len(corpus_rows())} declared inputs)")
    return 0


def main(argv: list[str]) -> int:
    root = em.REPO_ROOT
    if argv == []:
        generate(root)
        print(f"wrote {OUT_ROOT} ({len(corpus_rows())} declared inputs)")
        return 0
    if argv == ["--check"]:
        return check(root)
    print("usage: gen-evidence-measured.py [--check]", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
