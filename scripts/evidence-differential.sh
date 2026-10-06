#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
tmp_dir="$(mktemp -d "${TMPDIR:-/tmp}/lara-evidence-diff.XXXXXX")"
trap 'rm -rf "$tmp_dir"' EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

cabal build exe:evidence-differential
haskell_bin="$(cabal list-bin exe:evidence-differential)"
(cd lean && lake build evidence-driver)

python3 - "$haskell_bin" \
  "$repo_root/lean/.lake/build/bin/evidence-driver" <<'PY'
from pathlib import Path
import csv
import json
import subprocess
import sys


def parse_sexp(text):
    position = 0

    def value():
        nonlocal position
        while position < len(text) and text[position].isspace():
            position += 1
        if position == len(text):
            raise ValueError("unexpected end of S-expression")
        if text[position] == "(":
            position += 1
            values = []
            while True:
                while position < len(text) and text[position].isspace():
                    position += 1
                if position == len(text):
                    raise ValueError("missing closing parenthesis")
                if text[position] == ")":
                    position += 1
                    return values
                values.append(value())
        if text[position] == '"':
            start = position
            position += 1
            while position < len(text):
                if text[position] == "\\":
                    position += 2
                elif text[position] == '"':
                    position += 1
                    return json.loads(text[start:position], strict=False)
                else:
                    position += 1
            raise ValueError("unterminated quoted atom")
        start = position
        while position < len(text) and not text[position].isspace() and text[position] not in "()":
            position += 1
        if position == start:
            raise ValueError("unexpected closing parenthesis")
        return text[start:position]

    result = value()
    if text[position:].strip():
        raise ValueError("trailing S-expression input")
    return result


def fields(nodes):
    result = {}
    for node in nodes:
        assert isinstance(node, list) and node and node[0] not in result, node
        result[node[0]] = node[1:]
    return result


def ids(cell):
    return [] if cell == "-" else cell.split(",")


root = Path("fixtures/evidence/model")
with (root / "MANIFEST.tsv").open(newline="") as stream:
    reader = csv.DictReader(stream, delimiter="\t")
    assert reader.fieldnames == ["case", "outcome", "leaf", "object", "reason", "checked", "declared", "retained_checked"]
    cases = list(reader)
assert cases, "empty evidence differential corpus"
assert len({case["case"] for case in cases}) == len(cases), "duplicate manifest case"
assert {case["case"] for case in cases} == {path.name for path in root.glob("*.sexp")}, "manifest/fixture mismatch"
required = {"accepted", "binding", "capture", "extraction", "policy", "codec-invalid"}
assert {case["outcome"] for case in cases} == required, "missing or unknown boundary class"
depth_boundaries = {
    f"json-depth-{depth}-{terminal}.sexp": "accepted" if depth <= 128 else "extraction"
    for depth in (127, 128, 129)
    for terminal in ("empty-array", "empty-object", "scalar")
}
request_boundaries = {
    "codec-csv-decimal-line.sexp": "codec-invalid",
    **{f"{family}-selectors-256.sexp": "accepted" for family in ("csv", "json")},
    **{f"codec-{family}-selectors-257.sexp": "codec-invalid" for family in ("csv", "json")},
}
manifest_outcomes = {case["case"]: case["outcome"] for case in cases}
for name, outcome in (depth_boundaries | request_boundaries).items():
    assert manifest_outcomes.get(name) == outcome, f"missing or misclassified boundary fixture: {name}"
commands = [sys.argv[1], sys.argv[2]]
failures = []

for case in cases:
    name = case["case"]
    path = root / name
    outputs = [subprocess.run([command, str(path)], capture_output=True, timeout=60) for command in commands]
    try:
        if case["outcome"] == "codec-invalid":
            assert all(output.returncode == 2 and output.stdout == b"" for output in outputs), "codec rejection must exit 2 without an authoritative result"
        else:
            assert all(output.returncode == 0 and output.stderr == b"" for output in outputs), "valid model execution failed"
            assert outputs[0].stdout == outputs[1].stdout, "Haskell/Lean stdout differs"
            envelope = parse_sexp(outputs[0].stdout.decode("utf-8"))
            assert envelope[:2] == ["evidence-result", "1"] and len(envelope) == 3, envelope
            outcome = envelope[2]
            if case["outcome"] != "accepted":
                assert outcome[:2] == ["rejected", case["outcome"]], outcome
                if case["outcome"] == "policy":
                    assert outcome[2][0] == "rejected", outcome
                else:
                    assert len(outcome) == 5 and outcome[2] == case["leaf"] and outcome[4] == case["reason"], outcome
                    if case["object"] != "-":
                        assert outcome[3] == case["object"], outcome
            else:
                assert outcome[0] == "accepted", outcome
                report = fields(outcome[1:])
                assert set(report) == {"checked", "declared", "retained-checked", "ordinary", "retained"}, report
                assert [leaf[1] for leaf in report["checked"]] == ids(case["checked"]), report
                assert report["declared"] == ids(case["declared"]), report
                assert report["retained-checked"] == ids(case["retained_checked"]), report
                assert report["ordinary"][0][0] == "accepted", report
                source = fields(parse_sexp(path.read_text())[2:])
                source_leaves = {leaf[1]: leaf for leaf in source["leaves"]}
                metadata = {obj[1]: obj for obj in source["manifest"]}
                for leaf in report["checked"]:
                    declared = source_leaves[leaf[1]]
                    assert leaf[0] == "leaf" and leaf[2] == declared[-1], leaf
                    dependency = declared[5][2]
                    assert leaf[3] == ["deps", metadata[dependency]], leaf
                retained = fields(report["retained"])
                if name == "retained-nested-holes.sexp":
                    assert retained["args"] == ["a", "hAll", "hPrem", "hDis"], retained
                    assert [hole[1] for hole in retained["holes"]] == ["hAll", "hPrem", "hDis"], retained
                    assert all(hole[0] == "hole" and hole[3][0] == "obligations" for hole in retained["holes"]), retained
                else:
                    assert retained["args"] == [] and retained["attacks"] == [] and retained["holes"] == [], retained
        print(f"PASS {name}: {case['outcome']}")
    except (AssertionError, ValueError, IndexError, KeyError) as error:
        failures.append(name)
        print(f"FAIL {name}: {error}", file=sys.stderr)
        for language, output in zip(["Haskell", "Lean"], outputs):
            print(f"{language}: exit={output.returncode}", file=sys.stderr)
            print(output.stdout.decode("utf-8", errors="replace"), file=sys.stderr)
            print(output.stderr.decode("utf-8", errors="replace"), file=sys.stderr)

if failures:
    raise SystemExit(f"evidence differential: {len(failures)}/{len(cases)} failed")
print(f"evidence differential: PASS {len(cases)} typed cases; concrete byte parsers and OS capture are separate checks")
PY
