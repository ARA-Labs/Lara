#!/usr/bin/env python3
"""Shared pure helpers for the additive certified-evidence measured-input gate.

Two CLIs read this module:

* ``scripts/gen-evidence-measured.py`` materializes the rejected-input fixtures
  under ``fixtures/evidence/measured/`` from the committed
  ``fixtures/evidence/quarantined`` package and writes the corpus
  ``MANIFEST.tsv``; ``--check`` proves the committed bytes still regenerate.
* ``scripts/evidence-measure.py`` runs the real ``lara check-ara`` door over
  every declared input and writes the measured report the freeze snapshot
  commits.

Everything here is stdlib-only and deterministic: the same bytes in produce the
same bytes, manifest, and corpus identity out.  Canonical S-expression printing
mirrors ``Lara.Wire.printSExpr`` (and the independent printer in
``test/evidence-cli.sh``) so that the harness can re-print a report and demand
byte equality instead of trusting a hand-rolled formatter.

Scope: this measures package capture, request binding, extraction, the core
replay verdict, and the evidence-report identities.  It does not measure
scientific interpretation, semantic faithfulness, or reviewer judgment. The
certified leaves' audit metadata records a separate mapping review that this
harness does not check.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent

CORPUS_DIR = REPO_ROOT / "fixtures/evidence/measured"
CORPUS_MANIFEST = CORPUS_DIR / "MANIFEST.tsv"
BASE_PACKAGE = REPO_ROOT / "fixtures/evidence/quarantined"
EVIDENCE_MANIFEST = "lara-evidence.sexp"

#: Freeze identifier for this additive, independently versioned evaluation.
FREEZE_ID = "evidence-measured-inputs@2"
#: Report envelope format (distinct from the door's own ``lara-evidence-report``).
REPORT_FORMAT = "lara-evidence-measure-report@1"
#: Public versions the measured door must report; core stays untouched.
LANGUAGE_VERSION = "lara-syntax@0.11"
EVIDENCE_VERSION = "lara-evidence@0.1"
CORE_VERSION = "lara-core@0.3"

#: Failure classes, borrowed verbatim from the typed model corpus
#: (``fixtures/evidence/model/MANIFEST.tsv``) so the measured and model
#: evaluations name the same boundaries.
CLASSES = ("accepted", "policy", "binding", "capture", "extraction", "invalid")
#: Expected process exit per class (mirrors ``Lara.Evidence.Load``).
EXPECTED_EXIT = {
    "accepted": 0,
    "invalid": 2,
    "policy": 1,
    "binding": 1,
    "capture": 1,
    "extraction": 1,
}

CORPUS_COLUMNS = (
    "case",
    "root",
    "policy",
    "expect",
    "leaf",
    "reason",
    "checked",
    "declared",
    "assurance",
)


# ---------------------------------------------------------------------------
# Canonical S-expression wire form
# ---------------------------------------------------------------------------


def is_bare_char(char: str) -> bool:
    code = ord(char)
    return 0x21 <= code <= 0x7E and char not in '();"\\'


def wire(value) -> str:
    """Canonical single-line S-expression text (no trailing newline)."""
    if isinstance(value, list):
        return "(" + " ".join(wire(item) for item in value) + ")"
    if not isinstance(value, str):
        raise TypeError(f"non-string S-expression atom: {value!r}")
    if value and all(is_bare_char(char) for char in value):
        return value
    escaped = value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
    return '"' + escaped + '"'


def canonical(value) -> bytes:
    """The canonical UTF-8 encoding: ``printSExpr`` plus exactly one LF."""
    return (wire(value) + "\n").encode("utf-8")


def parse(text) -> list:
    """Parse one canonical S-expression; reject trailing input."""
    source = text.decode("utf-8") if isinstance(text, bytes) else text
    position = 0

    def skip() -> None:
        nonlocal position
        while position < len(source):
            if source[position] in " \t\r\n":
                position += 1
            elif source[position] == ";":
                while position < len(source) and source[position] != "\n":
                    position += 1
            else:
                break

    def form():
        nonlocal position
        skip()
        if position >= len(source):
            raise ValueError("unexpected end of S-expression")
        char = source[position]
        position += 1
        if char == "(":
            items = []
            while True:
                skip()
                if position >= len(source):
                    raise ValueError("unclosed S-expression list")
                if source[position] == ")":
                    position += 1
                    return items
                items.append(form())
        if char == '"':
            items = []
            while position < len(source):
                char = source[position]
                position += 1
                if char == '"':
                    return "".join(items)
                if char == "\\":
                    if position >= len(source):
                        raise ValueError("unterminated Wire escape")
                    char = source[position]
                    position += 1
                    if char not in '"\\n':
                        raise ValueError(f"invalid Wire escape {char!r}")
                    char = "\n" if char == "n" else char
                items.append(char)
            raise ValueError("unclosed Wire quote")
        if not is_bare_char(char):
            raise ValueError(f"invalid bare atom character {char!r}")
        start = position - 1
        while position < len(source) and is_bare_char(source[position]):
            position += 1
        return source[start:position]

    value = form()
    skip()
    if position != len(source):
        raise ValueError("trailing S-expression input")
    return value


def field(value: list, name: str) -> list:
    """The payload of the one ``(name ...)`` field; exactly one is required."""
    matches = [
        item[1:] for item in value if isinstance(item, list) and item and item[0] == name
    ]
    if len(matches) != 1:
        raise ValueError(f"expected one {name!r} field, got {matches!r}")
    return matches[0]


def fields(value: list) -> dict:
    """Named fields of a list; duplicate names are a hard error."""
    result: dict = {}
    for item in value:
        if not isinstance(item, list) or not item:
            raise ValueError(f"not a named field: {item!r}")
        if item[0] in result:
            raise ValueError(f"duplicate field {item[0]!r}")
        result[item[0]] = item[1:]
    return result


# ---------------------------------------------------------------------------
# Digests
# ---------------------------------------------------------------------------


def sha256_label(raw: bytes) -> str:
    return "sha256:" + hashlib.sha256(raw).hexdigest()


def tree_digest(root: Path) -> str:
    """Digest a committed input directory: sorted relative paths and bytes.

    Symlinks are refused rather than followed, so the digest can never depend
    on bytes outside the measured tree.
    """
    entries = []
    for path in sorted(root.rglob("*"), key=lambda p: p.relative_to(root).as_posix()):
        if path.is_symlink():
            raise ValueError(f"symlink in a measured input tree: {path}")
        if path.is_dir():
            continue
        entries.append((path.relative_to(root).as_posix(), path.read_bytes()))
    digest = hashlib.sha256()
    for relative, data in entries:
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(len(data)).encode("ascii"))
        digest.update(b"\0")
        digest.update(data)
    return "sha256:" + digest.hexdigest()


def corpus_identity(rows: list[dict]) -> str:
    """Independent identity of the whole measured corpus declaration."""
    payload = [
        {
            "case": row["case"],
            "root": row["root"],
            "policy": row["policy"],
            "expect": row["expect"],
            "leaf": row["leaf"],
            "reason": row["reason"],
            "checked": row["checked"],
            "declared": row["declared"],
            "assurance": row["assurance"],
            "input-digest": row["input-digest"],
            "policy-digest": row["policy-digest"],
        }
        for row in rows
    ]
    return sha256_label(json.dumps(payload, sort_keys=True).encode("utf-8"))


# ---------------------------------------------------------------------------
# Corpus manifest
# ---------------------------------------------------------------------------


def _cells(text: str) -> list[str]:
    return [] if text == "-" else text.split(",")


def parse_corpus(text: str) -> list[dict]:
    """Parse and validate the corpus TSV.  Raises on any structural problem."""
    lines = [line for line in text.splitlines() if line.strip()]
    if not lines:
        raise ValueError("empty measured-input corpus manifest")
    header = lines[0].split("\t")
    if tuple(header) != CORPUS_COLUMNS:
        raise ValueError(f"unexpected corpus columns {header!r}")
    rows = []
    for line in lines[1:]:
        cells = line.split("\t")
        if len(cells) != len(CORPUS_COLUMNS):
            raise ValueError(f"ragged corpus row: {line!r}")
        row = dict(zip(CORPUS_COLUMNS, cells))
        if row["expect"] not in CLASSES:
            raise ValueError(f"unknown expected class {row['expect']!r}")
        if row["assurance"] != "-" and row["expect"] != "accepted":
            raise ValueError(f"assurance on a rejected row: {row['case']!r}")
        if row["expect"] == "accepted" and row["assurance"] == "-":
            raise ValueError(f"accepted row without an assurance: {row['case']!r}")
        if row["expect"] != "accepted" and (row["checked"] != "-" or row["declared"] != "-"):
            raise ValueError(f"partition on a rejected row: {row['case']!r}")
        row["root-path"] = (REPO_ROOT / row["root"]).resolve()
        if not row["root-path"].is_dir():
            raise ValueError(f"missing measured input root: {row['root']!r}")
        if row["policy"] == "-":
            row["policy-path"] = None
        else:
            row["policy-path"] = (REPO_ROOT / row["policy"]).resolve()
            if not row["policy-path"].is_file():
                raise ValueError(f"missing verifier policy: {row['policy']!r}")
        row["input-digest"] = tree_digest(row["root-path"])
        row["policy-digest"] = (
            "-" if row["policy-path"] is None else sha256_label(row["policy-path"].read_bytes())
        )
        row["checked-list"] = _cells(row["checked"])
        row["declared-list"] = _cells(row["declared"])
        rows.append(row)
    if len({row["case"] for row in rows}) != len(rows):
        raise ValueError("duplicate measured-input case")
    return rows


def load_corpus(path: Path = CORPUS_MANIFEST) -> list[dict]:
    if not path.is_file():
        raise ValueError(f"no measured-input corpus at {path}")
    return parse_corpus(path.read_text(encoding="utf-8"))


# ---------------------------------------------------------------------------
# Observed class and location
# ---------------------------------------------------------------------------


def classify_stderr(text: str) -> dict:
    """Read the class and located leaf/reason out of the door's diagnostics.

    The door writes exactly one ``lara: <rendered error>`` line to stderr.  The
    offending object id is *not* rendered there (``renderEvidenceRejection``
    carries the leaf and the reason only), so ``object`` stays ``"-"`` for every
    measured rejection; the typed model corpus is the artifact that fixes the
    object.
    """
    text = text.strip()
    if text.startswith("lara: "):
        text = text[len("lara: "):]
    leaf_match = re.search(r"leaf '([^']*)'", text)
    leaf = leaf_match.group(1) if leaf_match else "-"
    if text.startswith("package invalid: "):
        return {"class": "invalid", "leaf": leaf, "object": "-",
                "reason": text[len("package invalid: "):], "stage": "-"}
    if "matched admission row" in text:
        return {"class": "policy", "leaf": leaf, "object": "-", "reason": "-",
                "stage": "admission"}
    for stage, kind in (("binding", "binding"), ("capture", "capture"),
                        ("extraction", "extraction")):
        prefix = f"certified evidence {stage}: "
        if prefix in text:
            reason = text.split(prefix, 1)[1]
            if reason.endswith(" (R8)"):
                reason = reason[: -len(" (R8)")]
            return {"class": kind, "leaf": leaf, "object": "-", "reason": reason,
                    "stage": stage}
    return {"class": "unclassified", "leaf": leaf, "object": "-", "reason": text,
            "stage": "-"}


def classify(exit_code: int, stdout: bytes, stderr: str) -> dict:
    """The observed measured class for one door invocation."""
    if exit_code != 0 and stdout:
        return {"class": "error", "leaf": "-", "object": "-",
                "reason": "rejection emitted stdout", "stage": "-"}
    if exit_code == 0:
        return {"class": "accepted", "leaf": "-", "object": "-", "reason": "-",
                "stage": "-"}
    if exit_code == 2:
        return classify_stderr(stderr)
    if exit_code == 1 and "(R8)" in stderr:
        return classify_stderr(stderr)
    if exit_code == 1:
        return {"class": "core-reject", "leaf": "-", "object": "-",
                "reason": stderr.strip(), "stage": "-"}
    return {"class": "error", "leaf": "-", "object": "-", "reason": stderr.strip(),
            "stage": "-"}


# ---------------------------------------------------------------------------
# Accepted-report reading and independent verification
# ---------------------------------------------------------------------------


def manifest_entries(root: Path) -> list[list]:
    """The ``objects`` rows of the package manifest, in manifest order."""
    value = parse((root / EVIDENCE_MANIFEST).read_bytes())
    if value[:2] != ["lara-evidence", "1"]:
        raise ValueError("package manifest is not lara-evidence 1")
    return field(value, "objects")


def global_object_id(root: Path, name: str) -> str:
    value = parse((root / EVIDENCE_MANIFEST).read_bytes())
    payload = field(value, name)
    if len(payload) != 1:
        raise ValueError(f"global {name!r} is not one id")
    return payload[0]


def source_leaf_ids(text: str) -> list[str]:
    """Declared leaf ids of a source program, in declaration order."""
    return re.findall(r"^leaf\s+(\S+)\s*:", text, re.M)


def source_extract_requests(root: Path) -> tuple[str, dict]:
    """The declared source text and its per-leaf ``extract`` requests."""
    source_id = global_object_id(root, "source")
    path = None
    for entry in manifest_entries(root):
        if entry[1] == source_id:
            path = root / entry[2]
    if path is None:
        raise ValueError("manifest names no source path")
    text = path.read_text(encoding="utf-8")
    requests: dict = {}
    leaf = None
    for line in text.splitlines():
        match = re.match(r"^leaf\s+(\S+)\s*:", line)
        if match:
            leaf = match.group(1)
        match = re.match(r"\s*extract\s*=\s*(.*)", line)
        if match:
            requests[leaf] = parse(match.group(1))
    return text, requests


def source_replay_identity(source_text: str, policy_text: str) -> list:
    """Re-derive the core tuple from source headers and the effective policy."""
    identifier = r"[^\W\d][\w-]*"
    digest = rf"{identifier}\s*:\s*[\w.-]+"
    version = rf"(?:[+-]?[0-9]+(?:\.[0-9]+)?|{identifier})"
    # Strings and comments cannot contribute identity-bearing declarations.
    ignored = r'"(?:\\.|[^"\\])*"|#[^\n]*'
    source = re.sub(ignored, "", source_text)
    policy = re.sub(ignored, "", policy_text)
    header = re.match(
        rf"\s*artifact\s+{identifier}\s+at\s+(?P<artifact>{digest})"
        rf"\s+policy\s+{identifier}\s+use\s+backends\s*\[(?P<backends>[^\]]*)\]",
        source,
    )
    policy_header = re.match(rf"\s*policy\s+({identifier})", policy)
    if header is None or policy_header is None:
        raise ValueError("cannot derive core replay identity from source/policy headers")
    backends = []
    if header["backends"].strip():
        for item in header["backends"].split(","):
            backend = re.fullmatch(rf"\s*({identifier})\s*@\s*({version})\s*", item)
            if backend is None:
                raise ValueError(f"cannot derive core replay backend: {item!r}")
            backends.append(["backend", backend[1], backend[2]])
    theories = sorted(re.sub(r"\s+", "", match[1]) for match in
                      re.finditer(rf"\btheory\s+({digest})\s*=", policy))
    return ["replay-id", ["core", CORE_VERSION], ["policy", policy_header[1]],
            ["backends", *backends], ["theories", *theories],
            ["artifact", re.sub(r"\s+", "", header["artifact"])]]


def read_accepted_report(root: Path, policy_path, stdout: bytes) -> dict:
    """Parse an accepted report and independently re-verify its identities.

    Every boolean in ``verified`` is recomputed here from the package bytes and
    the reported replay tuples; nothing is taken on the report's word.  This
    mirrors the independent recomputation in ``test/evidence-cli.sh``.
    """
    report = parse(stdout)
    if report[:2] != ["lara-evidence-report", "1"]:
        raise ValueError("stdout is not a lara-evidence-report 1 envelope")
    versions = field(report, "versions")
    assurance = field(report, "assurance")[0]
    checked = field(report, "checked")
    declared = field(report, "declared")
    replays = field(report, "replays")
    dependency_digest = field(report, "dependency-report-digest")[0]
    captured = field(report, "captured")
    core_replay = field(report, "core-replay")[0]
    verdict = field(report, "core-verdict")[0]
    core_outcome = verdict[2] if len(verdict) > 2 else None
    evidence_digest = field(report, "evidence-digest")[0]
    manifest_sha = field(report, "manifest")[0]
    source_sha = field(report, "source")[0]
    origin, policy_sha = field(report, "policy")

    entries = manifest_entries(root)
    by_id = {entry[1]: entry for entry in entries}
    globals_ids = [global_object_id(root, name) for name in ("paper", "source", "policy")]

    verified: dict = {}
    verified["report-canonical"] = stdout == canonical(report)
    verified["versions"] = versions == [LANGUAGE_VERSION, EVIDENCE_VERSION]
    verified["core-accept"] = verdict[0] == "verdict" and core_outcome == "accept"
    verified["manifest-sha256"] = manifest_sha == sha256_label(
        (root / EVIDENCE_MANIFEST).read_bytes()
    )
    source_path = root / by_id[globals_ids[1]][2]
    verified["source-sha256"] = source_sha == sha256_label(source_path.read_bytes())
    policy_file = Path(policy_path) if policy_path is not None else root / by_id[globals_ids[2]][2]
    verified["policy-sha256"] = policy_sha == sha256_label(policy_file.read_bytes())
    verified["policy-origin"] = origin == ("verifier" if policy_path is not None else "package")

    source_text, requests = source_extract_requests(root)
    expected_replay = source_replay_identity(source_text, policy_file.read_text(encoding="utf-8"))
    verified["core-replay"] = len(verdict) > 1 and verdict[1] == core_replay == expected_replay
    verified["replays-match-checked"] = [item[1] for item in replays] == checked
    request_ok = True
    requested_ids = []
    dependency_rows = ["dependencies"]
    for replay in replays:
        if not (replay[0] == "leaf" and replay[1] in requests):
            request_ok = False
            continue
        if replay[2] != requests[replay[1]]:
            request_ok = False
        ident = requests[replay[1]][2]
        deps = field(replay, "deps")
        if ident not in by_id or deps != [by_id[ident]]:
            request_ok = False
        else:
            requested_ids.append(ident)
            dependency_rows.append(["leaf", replay[1], ["objects", *deps]])
    verified["replay-requests"] = request_ok
    verified["dependency-report-digest"] = dependency_digest == sha256_label(
        canonical(dependency_rows)
    )

    required = [
        entry
        for entry in entries
        if entry[1] in requested_ids and entry[1] not in globals_ids
    ]
    expected_captured = [by_id[ident] for ident in globals_ids] + required
    captured_ok = captured == expected_captured
    if captured_ok:
        for entry in captured:
            raw = (root / entry[2]).read_bytes()
            if entry[3:] != [str(len(raw)), sha256_label(raw)]:
                captured_ok = False
    verified["captured"] = captured_ok

    envelope = [
        item
        for item in report
        if not (isinstance(item, list) and item and item[0] == "evidence-digest")
    ]
    verified["evidence-digest"] = evidence_digest == sha256_label(canonical(envelope))
    verified["partition-disjoint"] = not (set(checked) & set(declared))
    verified["declared-is-declared"] = set(declared) <= set(source_leaf_ids(source_text))
    expected_assurance = (
        "evidence-declared" if not checked else "evidence-checked" if not declared else "mixed"
    )
    verified["assurance"] = assurance == expected_assurance

    return {
        "versions": versions,
        "assurance": assurance,
        "checked": checked,
        "declared": declared,
        "manifest-sha256": manifest_sha,
        "source-sha256": source_sha,
        "policy-origin": origin,
        "policy-sha256": policy_sha,
        "core-replay": core_replay,
        "core-outcome": core_outcome,
        "core-verdict": verdict,
        "replays": replays,
        "captured": captured,
        "dependency-report-digest": dependency_digest,
        "evidence-digest": evidence_digest,
        "verified": verified,
    }
