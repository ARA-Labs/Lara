#!/usr/bin/env python3
"""Run the real ``lara check-ara`` door over the additive measured-input corpus.

Usage:
    scripts/evidence-measure.py                     # write measurements/evidence-report.{json,tsv}
    scripts/evidence-measure.py --check [FROZEN]    # reproduce the committed freeze, no writes

The corpus is declared in ``fixtures/evidence/measured/MANIFEST.tsv`` and the
inputs are the committed real packages plus the generated rejected-input
fixtures.  Each declared input is run through the real binary; the measured
record carries the observed class, the located leaf and reason, the process
exit, the raw stdout/stderr digests, and — for accepted inputs — the report's
own scope identities and every independent re-verification of them.

This is a *measured-input* evaluation: it measures package capture, request
binding, extraction, and the core replay verdict.  It does not measure, and
must not be read as, scientific correctness or semantic faithfulness of the
ten certified leaves; those stay human and unreviewed (issue #20).

``--check`` recomputes the whole report and compares every deterministic block
(format, freeze, scope, corpus identity, aggregate, records) with the committed
frozen snapshot, ignoring only the per-machine environment block.  It is the
standing gate that a frozen report still describes the committed corpus and the
current door.

The freeze identifier is ``evidence-measured-inputs@1``; it is independent of
the ``m5-freeze-*`` evaluation snapshots, whose numbers this change never
touches.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import evidence_measured as em  # noqa: E402

FROZEN_DEFAULT = Path("measurements/frozen/evidence-report.json")
MEASURED_JSON = Path("measurements/evidence-report.json")
MEASURED_TSV = Path("measurements/evidence-report.tsv")

TSV_COLUMNS = (
    ("input", "input"),
    ("root", "root"),
    ("policy", "policy"),
    ("expected", "expected"),
    ("actual", "actual"),
    ("class_match", "class-match"),
    ("exit", "exit"),
    ("leaf", "leaf"),
    ("reason", "reason"),
    ("assurance", "assurance"),
    ("checked", "checked"),
    ("declared", "declared"),
    ("evidence_digest", "evidence-digest"),
)

SCOPE = {
    "door": "lara check-ara (real CLI binary)",
    "language": em.LANGUAGE_VERSION,
    "evidence": em.EVIDENCE_VERSION,
    "core": em.CORE_VERSION,
    "measures": "package capture, request binding, extraction, core replay verdict, evidence-report identities",
    "excludes": "scientific interpretation, semantic faithfulness, human review (issue #20)",
}


# ---------------------------------------------------------------------------
# Running the door
# ---------------------------------------------------------------------------


def resolve_lara(argument: str | None) -> Path:
    candidate = argument or os.environ.get("LARA_BIN")
    if candidate:
        path = Path(candidate).expanduser()
        if not path.is_absolute():
            path = em.REPO_ROOT / path
        path = path.resolve()
    else:
        try:
            output = subprocess.run(
                ["cabal", "list-bin", "exe:lara"], cwd=em.REPO_ROOT,
                capture_output=True, timeout=120,
            )
        except (OSError, subprocess.TimeoutExpired) as error:
            raise SystemExit(f"evidence-measure: cannot run cabal: {error}")
        if output.returncode != 0:
            raise SystemExit("evidence-measure: cabal list-bin failed; run `cabal build exe:lara` first")
        path = Path(output.stdout.decode("utf-8").strip()).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise SystemExit(f"evidence-measure: lara binary is not executable: {path}")
    return path


def run_door(lara: Path, row: dict) -> subprocess.CompletedProcess:
    command = [str(lara), "check-ara", str(row["root-path"])]
    if row["policy-path"] is not None:
        command += ["--policy", str(row["policy-path"])]
    try:
        return subprocess.run(command, cwd=em.REPO_ROOT, capture_output=True, timeout=120)
    except subprocess.TimeoutExpired as error:
        raise SystemExit(f"evidence-measure: the door hung on {row['case']}: {error}")


def measure_row(lara: Path, row: dict) -> dict:
    process = run_door(lara, row)
    stderr = process.stderr.decode("utf-8", errors="replace")
    observed = em.classify(process.returncode, process.stdout, stderr)
    expected = row["expect"]
    expected_exit = em.EXPECTED_EXIT[expected]
    record = {
        "input": row["case"],
        "root": row["root"],
        "policy": row["policy"],
        "input-digest": row["input-digest"],
        "policy-digest": row["policy-digest"],
        "expected": expected,
        "expected-exit": expected_exit,
        "actual": observed["class"],
        "exit": process.returncode,
        "stage": observed["stage"],
        "leaf": observed["leaf"],
        "object": observed["object"],
        "reason": observed["reason"],
        "stdout-sha256": em.sha256_label(process.stdout),
        "stderr-sha256": em.sha256_label(process.stderr),
        "versions": None,
        "assurance": None,
        "checked": None,
        "declared": None,
        "manifest-sha256": None,
        "source-sha256": None,
        "policy-origin": None,
        "policy-sha256": None,
        "core-replay": None,
        "core-outcome": None,
        "core-verdict": None,
        "replays": None,
        "captured": None,
        "dependency-report-digest": None,
        "evidence-digest": None,
        "verified": {},
    }
    matched = observed["class"] == expected and process.returncode == expected_exit
    if observed["class"] != expected:
        record["class-match"] = False
        return record
    if expected == "accepted":
        try:
            info = em.read_accepted_report(row["root-path"], row["policy-path"], process.stdout)
        except (ValueError, KeyError, IndexError) as error:
            record["class-match"] = False
            record["reason"] = f"accepted report did not parse: {error}"
            return record
        info["verified"]["empty-stderr"] = process.stderr == b""
        info["verified"]["checked-partition"] = info["checked"] == row["checked-list"]
        info["verified"]["declared-partition"] = info["declared"] == row["declared-list"]
        info["verified"]["assurance-label"] = info["assurance"] == row["assurance"]
        matched = matched and all(info["verified"].values())
        record.update(
            {
                "versions": info["versions"],
                "assurance": info["assurance"],
                "checked": info["checked"],
                "declared": info["declared"],
                "manifest-sha256": info["manifest-sha256"],
                "source-sha256": info["source-sha256"],
                "policy-origin": info["policy-origin"],
                "policy-sha256": info["policy-sha256"],
                "core-replay": info["core-replay"],
                "core-outcome": info["core-outcome"],
                "core-verdict": info["core-verdict"],
                "replays": info["replays"],
                "captured": info["captured"],
                "dependency-report-digest": info["dependency-report-digest"],
                "evidence-digest": info["evidence-digest"],
                "verified": info["verified"],
            }
        )
    else:
        record["verified"]["empty-stdout"] = process.stdout == b""
        matched = matched and record["verified"]["empty-stdout"]
        matched = matched and observed["leaf"] == row["leaf"]
        if row["reason"] != "-":
            matched = matched and observed["reason"] == row["reason"]
    record["class-match"] = bool(matched)
    return record


# ---------------------------------------------------------------------------
# Report assembly
# ---------------------------------------------------------------------------


def probe(*command: str) -> str:
    try:
        result = subprocess.run(command, cwd=em.REPO_ROOT, capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise SystemExit(f"evidence-measure: cannot record {' '.join(command)}: {error}") from error
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise SystemExit(f"evidence-measure: {' '.join(command)} exited {result.returncode}: {detail}")
    return result.stdout.decode("utf-8").strip()


def gather_env(lara: Path) -> dict:
    dirty = probe("git", "status", "--porcelain")
    return {
        "git-rev": probe("git", "rev-parse", "HEAD"),
        "git-dirty": bool(dirty),
        "lara-bin": str(lara),
        "lara-bin-sha256": em.sha256_label(lara.read_bytes()),
        "ghc": probe("ghc", "--numeric-version"),
        "python": sys.version.split()[0],
        "os": sys.platform,
        "cpu": probe("uname", "-m"),
    }


def aggregate(records: list[dict]) -> dict:
    classes = sorted({record["expected"] for record in records})
    assurances: dict = {}
    for record in records:
        if record["assurance"] is not None:
            assurances[record["assurance"]] = assurances.get(record["assurance"], 0) + 1
    return {
        "count": len(records),
        "class-match-rate": {
            "matched": sum(1 for record in records if record["class-match"]),
            "total": len(records),
        },
        "class-accuracy": {
            cls: {
                "matched": sum(1 for r in records if r["expected"] == cls and r["class-match"]),
                "total": sum(1 for r in records if r["expected"] == cls),
            }
            for cls in classes
        },
        "checked-leaves": sum(len(r["checked"] or []) for r in records),
        "declared-leaves": sum(len(r["declared"] or []) for r in records),
        "assurances": assurances,
    }


def identical_policy_invariant(base: dict, override: dict) -> bool:
    fixed = ("core-replay", "core-verdict", "replays",
             "dependency-report-digest", "captured", "policy-sha256")
    return (all(base[key] == override[key] for key in fixed)
            and base["evidence-digest"] != override["evidence-digest"])


def build_report(corpus: list[dict], lara: Path) -> dict:
    records = [measure_row(lara, row) for row in corpus]
    by_input = {record["input"]: record for record in records}
    override = by_input["package-a-verifier-policy"]
    policy_match = identical_policy_invariant(by_input["package-a"], override)
    override["verified"]["identical-verifier-policy"] = policy_match
    override["class-match"] = override["class-match"] and policy_match
    manifest_bytes = em.CORPUS_MANIFEST.read_bytes()
    return {
        "format": em.REPORT_FORMAT,
        "freeze": em.FREEZE_ID,
        "scope": SCOPE,
        "environment": gather_env(lara),
        "corpus": {
            "manifest": str(em.CORPUS_MANIFEST.relative_to(em.REPO_ROOT)),
            "manifest-sha256": em.sha256_label(manifest_bytes),
            "inputs": len(corpus),
            "identity": em.corpus_identity(corpus),
        },
        "aggregate": aggregate(records),
        "records": records,
    }


def render_tsv(records: list[dict]) -> str:
    def cell(value) -> str:
        if value is None:
            return "-"
        if isinstance(value, list):
            return ",".join(value) if value else "-"
        if isinstance(value, bool):
            return "true" if value else "false"
        return str(value)

    lines = ["\t".join(column for column, _ in TSV_COLUMNS)]
    for record in records:
        lines.append("\t".join(cell(record[key]) for _, key in TSV_COLUMNS))
    return "\n".join(lines) + "\n"


def deterministic(report: dict) -> dict:
    return {key: value for key, value in report.items() if key != "environment"}


def snapshot_errors(frozen: dict, observed: dict, frozen_tsv: str) -> list[str]:
    expected = deterministic(frozen)
    actual = deterministic(observed)
    failures = []
    for key in sorted(set(expected) | set(actual)):
        if key not in actual:
            failures.append(f"frozen has extra block {key!r}")
        elif key not in expected:
            failures.append(f"frozen is missing block {key!r}")
        elif expected[key] != actual[key]:
            failures.append(f"block {key!r} differs from the frozen snapshot")
    if frozen_tsv != render_tsv(observed["records"]):
        failures.append("TSV differs from the frozen snapshot")
    matched = observed["aggregate"]["class-match-rate"]
    if matched["matched"] != matched["total"]:
        failures.append("observed inputs do not all match their declared class")
    return failures


# ---------------------------------------------------------------------------
# Entry points
# ---------------------------------------------------------------------------


def parse_arguments(argv: list[str]) -> tuple[str, str | None, str]:
    mode = "measure"
    lara = None
    frozen = None
    index = 0
    while index < len(argv):
        argument = argv[index]
        if argument == "--check":
            mode = "check"
            if index + 1 < len(argv) and not argv[index + 1].startswith("--"):
                frozen = argv[index + 1]
                index += 1
        elif argument == "--lara":
            if index + 1 >= len(argv):
                raise SystemExit("evidence-measure: --lara needs a path")
            lara = argv[index + 1]
            index += 1
        elif argument in ("--help", "-h"):
            print(__doc__)
            raise SystemExit(0)
        else:
            raise SystemExit(f"evidence-measure: unknown argument {argument!r}")
        index += 1
    return mode, lara, frozen


def main(argv: list[str]) -> int:
    mode, lara_argument, frozen_argument = parse_arguments(argv)
    lara = resolve_lara(lara_argument)
    corpus = em.load_corpus()

    if mode == "measure":
        report = build_report(corpus, lara)
        (em.REPO_ROOT / "measurements").mkdir(parents=True, exist_ok=True)
        (em.REPO_ROOT / MEASURED_JSON).write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8"
        )
        (em.REPO_ROOT / MEASURED_TSV).write_text(render_tsv(report["records"]), encoding="utf-8")
        matched = report["aggregate"]["class-match-rate"]
        print(f"wrote {MEASURED_JSON} and {MEASURED_TSV}: "
              f"{matched['matched']}/{matched['total']} inputs match their declared class")
        for record in report["records"]:
            if not record["class-match"]:
                print(f"  MISMATCH {record['input']}: expected {record['expected']} "
                      f"got {record['actual']} (exit {record['exit']}): {record['reason']}",
                      file=sys.stderr)
        return 0 if matched["matched"] == matched["total"] else 1

    frozen_path = em.REPO_ROOT / (frozen_argument or FROZEN_DEFAULT)
    if not frozen_path.is_file():
        print(
            f"evidence-measure: no frozen report at {frozen_path}; freeze it first:\n"
            "  scripts/gen-evidence-measured.py --check\n"
            "  cabal build exe:lara\n"
            "  scripts/evidence-measure.py\n"
            "  cp measurements/evidence-report.json measurements/evidence-report.tsv "
            "measurements/frozen/",
            file=sys.stderr,
        )
        return 2
    try:
        frozen = json.loads(frozen_path.read_text(encoding="utf-8"))
        frozen_tsv = frozen_path.with_suffix(".tsv").read_text(encoding="utf-8")
    except (OSError, ValueError) as error:
        print(f"evidence-measure: cannot read frozen report pair: {error}", file=sys.stderr)
        return 2
    observed = deterministic(build_report(corpus, lara))
    failures = snapshot_errors(frozen, observed, frozen_tsv)
    if failures:
        for failure in failures:
            print(f"FAIL: {failure}", file=sys.stderr)
        return 1
    matched = observed["aggregate"]["class-match-rate"]
    print(f"PASS: {frozen_path} reproduces; freeze {observed['freeze']}, "
          f"corpus {observed['corpus']['identity']}, "
          f"{matched['matched']}/{matched['total']} inputs match")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
