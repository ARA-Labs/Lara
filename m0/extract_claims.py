#!/usr/bin/env python3
"""Build the M0 sampling frame from the pinned ara-paperbench submodule.

Parses every `logic/claims.md` into one TSV row per claim, and every
`trace/exploration_tree.yaml` into one TSV row per dead_end node (the
attack-candidate pool for annotation field 7, docs/corpus-map.md §4).

Stdlib only; run from the repo root:

    python3 m0/extract_claims.py

Outputs (overwritten in place):
    m0/claims-index.tsv     one row per claim (231 expected at pin 62e9b54)
    m0/deadends-index.tsv   one row per dead_end trace node (279 expected)

Schema note: `rebench-restricted_mlm` uses `Evidence` for `Proof` and omits
`Status`/`Falsification criteria`; both spellings of the falsification field
are accepted. Raw status text is kept verbatim in `status_raw` and normalized
into `status` (supported | partially_supported | untested | hypothesis).
"""

import csv
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
CORPUS = REPO_ROOT / "corpus" / "ara-paperbench" / "artifacts"
OUT_DIR = REPO_ROOT / "m0"

CLAIM_HEADER = re.compile(r"^##\s+(C\d+[a-z]?):?\s*(.*)$")
FIELD = re.compile(r"^-\s+\*\*([^*]+)\*\*:?\s*(.*)$")

# claims.md field name -> canonical column
FIELD_MAP = {
    "Statement": "statement",
    "Status": "status_raw",
    "Falsification criteria": "falsification",
    "Falsification": "falsification",
    "Proof": "proof",
    "Evidence": "proof",  # rebench-restricted_mlm variant
    "Dependencies": "dependencies",
    "Provenance": "provenance",
    "Tags": "tags",
}

CLAIM_COLUMNS = [
    "group", "artifact", "claim_id", "title", "statement", "status",
    "status_raw", "falsification", "proof", "dependencies", "provenance",
    "tags",
]

DEADEND_COLUMNS = [
    "group", "artifact", "node_id", "title", "hypothesis", "failure_mode",
]


def normalize_status(raw: str) -> str:
    low = raw.lower()
    if not low:
        return ""
    if low.startswith("partially supported"):
        return "partially_supported"
    if low.startswith("supported"):
        return "supported"
    if low.startswith("untested"):
        return "untested"
    if low.startswith("hypothesis"):
        return "hypothesis"
    return "other"


def parse_claims(path: Path, group: str, artifact: str) -> list[dict]:
    rows: list[dict] = []
    current: dict | None = None
    current_field: str | None = None
    for line in path.read_text(encoding="utf-8").splitlines():
        m = CLAIM_HEADER.match(line)
        if m:
            current = {c: "" for c in CLAIM_COLUMNS}
            current.update(group=group, artifact=artifact,
                           claim_id=m.group(1), title=m.group(2).strip())
            rows.append(current)
            current_field = None
            continue
        if current is None:
            continue
        f = FIELD.match(line)
        if f and f.group(1).strip() in FIELD_MAP:
            current_field = FIELD_MAP[f.group(1).strip()]
            current[current_field] = f.group(2).strip()
        elif f:
            current_field = None  # unmapped bold field: skip its continuation
        elif current_field and line.strip():
            current[current_field] += " " + line.strip()
    for row in rows:
        row["status"] = normalize_status(row["status_raw"])
    return rows


# Every mapping key observed in the corpus trace YAMLs. A line is treated as
# a key line only if its key is in this set; anything else is continuation
# text (which may itself contain a colon).
TRACE_KEYS = frozenset({
    "id", "type", "title", "description", "hypothesis", "failure_mode",
    "lesson", "result", "evidence", "choice", "alternatives", "children",
    "also_depends_on", "resolution", "status", "date", "by", "note",
    "still_open", "approach_context", "provenance", "source", "timestamp",
    "tree", "root", "nodes",
})

WANTED = frozenset({"id", "type", "title", "hypothesis", "failure_mode"})
BLOCK_MARKERS = (">", ">-", "|", "|-")


def parse_deadends(path: Path, group: str, artifact: str) -> list[dict]:
    """Line-based scan; the trace YAMLs are hand-written (one is malformed,
    and key order varies — some artifacts alphabetize keys so `id` is not
    first), so a full YAML parse is deliberately avoided. A node is a list
    item (`- key: ...`); captures id, type, title, hypothesis, failure_mode.
    """
    rows: list[dict] = []
    node: dict | None = None

    def flush() -> None:
        if node and node.get("type") == "dead_end":
            rows.append({
                "group": group, "artifact": artifact,
                "node_id": node.get("id", ""), "title": node.get("title", ""),
                "hypothesis": node.get("hypothesis", ""),
                "failure_mode": node.get("failure_mode", ""),
            })

    item_start = re.compile(r"^(\s*)-\s+([A-Za-z_]+):\s*(.*)$")
    scalar = re.compile(r"^(\s*)([A-Za-z_]+):\s*(.*)$")
    pending_key: str | None = None
    pending_indent = 0

    def assign(key: str, value: str, indent: int) -> None:
        nonlocal pending_key, pending_indent
        pending_key = None
        if node is None or key not in WANTED:
            return
        if value in BLOCK_MARKERS:
            node[key] = ""
            pending_key, pending_indent = key, indent
        else:
            node[key] = value.strip('\'"')
            pending_key, pending_indent = key, indent

    for line in path.read_text(encoding="utf-8").splitlines():
        m = item_start.match(line)
        if m and m.group(2) in TRACE_KEYS:
            flush()
            node = {}
            assign(m.group(2), m.group(3).strip(), len(m.group(1)))
            continue
        m = scalar.match(line)
        if m and m.group(2) in TRACE_KEYS:
            assign(m.group(2), m.group(3).strip(), len(m.group(1)))
            continue
        if (node is not None and pending_key and line.strip()
                and len(line) - len(line.lstrip()) > pending_indent):
            joined = (node[pending_key] + " " + line.strip().strip('\'"'))
            node[pending_key] = joined.strip()
    flush()
    return rows


def main() -> int:
    if not CORPUS.is_dir():
        sys.exit("corpus submodule missing — run: "
                 "git submodule update --init --depth 1 corpus/ara-paperbench")
    claims: list[dict] = []
    deadends: list[dict] = []
    for claims_md in sorted(CORPUS.glob("*/*/logic/claims.md")):
        artifact_dir = claims_md.parent.parent
        group, artifact = artifact_dir.parent.name, artifact_dir.name
        claims.extend(parse_claims(claims_md, group, artifact))
        trace = artifact_dir / "trace" / "exploration_tree.yaml"
        if trace.is_file():
            deadends.extend(parse_deadends(trace, group, artifact))

    for name, columns, rows in (
        ("claims-index.tsv", CLAIM_COLUMNS, claims),
        ("deadends-index.tsv", DEADEND_COLUMNS, deadends),
    ):
        out = OUT_DIR / name
        with out.open("w", newline="", encoding="utf-8") as fh:
            writer = csv.DictWriter(fh, fieldnames=columns, delimiter="\t")
            writer.writeheader()
            writer.writerows(rows)
        print(f"{out.relative_to(REPO_ROOT)}: {len(rows)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main())
