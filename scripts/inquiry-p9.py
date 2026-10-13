#!/usr/bin/env python3
"""P9: the paired live-loop feasibility run of checked-inquiry feedback.

Subcommands, in protocol order:

* ``check-key``   derive every answer-key field from the reviewed P8 oracle's
                  expected results and require equality with the committed key.
* ``smoke``       the one approved harness-validation call (dummy workspace,
                  excluded from results, charged to the budget).
* ``run``         every (task, arm) agent run in the frozen seeded order.
* ``score``       mechanical oracle scoring plus the arm-blind AI scorer.
* ``summarize``   the per-arm and paired summary over a scored run.

The protocol, prompts and limits are frozen in
``evaluation/inquiry-p9/protocol.json``; ``run`` and ``smoke`` refuse to start
unless the researcher approval receipt binds that file's exact SHA256.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
P9 = ROOT / "evaluation" / "inquiry-p9"
P8_ORACLES = ROOT / "evaluation" / "inquiry-p8-corrected" / "oracles"
VIEWS = ROOT / "scripts" / "inquiry_p9_views.py"
ARMS = ("status", "inquiry")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path: Path):
    return json.loads(path.read_text())


def dump(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


# --- answer key, derived from the P8 oracles ---------------------------------

def literal_text(literal) -> str:
    kind, slot, choice = literal[1][0], literal[1][1][1], literal[1][2][1]
    return f"s{slot}={choice}" if kind == "slot-eq" else f"s{slot}!={choice}"


def bodies(case: str) -> dict:
    oracle = load(P8_ORACLES / f"{case}.json")
    return {form[2]: form[3] for form in oracle["expected"]["results"] if form[0] == "inquiry-result"}


def derive(task: dict) -> dict:
    by_label = bodies(task["p8_case"])
    kinds = {body[0]: body for body in by_label.values()}
    derived = {}
    if "audit-body" in kinds:
        rows = kinds["audit-body"][1][1]
        derived["witness_passes_every_completion"] = kinds["audit-body"][1][5] == "true"
        derived["failing_completion_events"] = sorted(
            row[1][-1][1] for row in rows if row[4] == ["false"])
    if "assumptions-body" in kinds:
        derived["minimal_assumption_sets"] = [
            [literal_text(l) for l in m[1]] for m in kinds["assumptions-body"][1][4]]
    if "status-body" in kinds:
        result = kinds["status-body"][1]
        derived.update(accepted_completions=int(result[3]), total_completions=int(result[2]),
                       status_stable_across_family=result[5] == "true")
        derived["may_report_as_settled"] = derived["status_stable_across_family"]
    if "impact-body" in kinds:
        row = kinds["impact-body"][1][2][0]
        before, after, locality = row[2][0], row[3][0], row[5] == "true"
        certified = locality and (before[0] == "evidence-blocked") == (after[0] == "evidence-blocked")
        derived.update(after_status=" ".join(after), status_changed=row[4] == "true",
                       publishable_as_observed_evidence=after[0] == "published",
                       certified_unaffected_by_edit=certified, rereview_may_be_skipped=certified)
    return derived


def check_key(_args) -> int:
    key = load(P9 / "answer-key.json")
    failures = []
    for task in key["tasks"]:
        tid = task["task_id"]
        if sha256(P9 / "tasks" / tid / "input.sexp") != task["input_sha256"]:
            failures.append(f"{tid}: input hash")
        if sha256(P8_ORACLES / f"{task['p8_case']}.json") != task["p8_oracle_sha256"]:
            failures.append(f"{tid}: P8 oracle hash")
        if sha256(ROOT / "evaluation" / "inquiry-p8-corrected" / "inputs" / f"{task['p8_case']}.sexp") \
                != task["input_sha256"]:
            failures.append(f"{tid}: input differs from the P8 input")
        derived = derive(task)
        for field, value in task["expected"].items():
            if field not in derived:
                failures.append(f"{tid}: oracle does not determine {field}")
            elif normalize(field, derived[field]) != normalize(field, value):
                failures.append(f"{tid}: {field} key {value!r} != oracle {derived[field]!r}")
    for failure in failures:
        print(f"FAIL {failure}")
    print("check-key:", "FAIL" if failures else f"PASS ({len(key['tasks'])} tasks)")
    return 1 if failures else 0


# --- answer normalization and mechanical scoring ------------------------------

def norm_literal(text: str) -> str:
    text = str(text).strip().lower().replace(" ", "").replace("≠", "!=")
    match = re.fullmatch(r"s(\d+)(=|!=)(\d+)", text)
    return f"s{match[1]}{match[2]}{match[3]}" if match else f"?{text}"


def normalize(field: str, value):
    if field == "minimal_assumption_sets":
        if not isinstance(value, list) or not all(isinstance(s, list) for s in value):
            return ("malformed", json.dumps(value, sort_keys=True))
        return frozenset(frozenset(norm_literal(l) for l in s) for s in value)
    if field == "failing_completion_events":
        if not isinstance(value, list):
            return ("malformed", json.dumps(value, sort_keys=True))
        return frozenset(str(v).strip().lower() for v in value)
    if field == "after_status":
        return " ".join(str(value).lower().replace("(", " ").replace(")", " ").split())
    if field in ("accepted_completions", "total_completions"):
        return value if isinstance(value, int) and not isinstance(value, bool) else ("malformed", repr(value))
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.strip().lower() in ("true", "false"):
        return value.strip().lower() == "true"
    return ("malformed", repr(value))


def final_answer(text: str):
    blocks = re.findall(r"```json\s*(.*?)```", text or "", re.S)
    if not blocks:
        return None, "no json block"
    try:
        return json.loads(blocks[-1]), None
    except json.JSONDecodeError as error:
        return None, f"invalid json: {error}"


def mechanical(expected: dict, answer) -> dict:
    if not isinstance(answer, dict):
        return {"answer_parsed": False, "fields": {}, "all_fields_correct": False}
    fields = {f: {"expected": e, "given": answer.get(f),
                  "correct": f in answer and normalize(f, answer[f]) == normalize(f, e)}
              for f, e in expected.items()}
    return {"answer_parsed": True, "fields": fields,
            "all_fields_correct": all(v["correct"] for v in fields.values())}


# --- the agent harness -------------------------------------------------------

def approved_protocol() -> dict:
    protocol_path = P9 / "protocol.json"
    approval_path = P9 / "researcher-approval.json"
    if not approval_path.exists():
        sys.exit("refusing: no researcher approval receipt")
    approval = load(approval_path)
    digest = sha256(protocol_path)
    if approval.get("status") != "APPROVED" or approval.get("protocol_sha256") != digest:
        sys.exit(f"refusing: approval does not bind protocol {digest}")
    protocol = load(protocol_path)
    drift = [p for p, h in protocol["frozen_files"].items() if sha256(ROOT / p) != h]
    if drift:
        sys.exit(f"refusing: frozen files changed since approval: {drift}")
    return protocol


def workspace(base: Path, task_dir: Path, binary: str) -> Path:
    base.mkdir(parents=True)
    shutil.copyfile(task_dir / "input.sexp", base / "input.sexp")
    script = base / "lara-view"
    script.write_text(
        "#!/bin/sh\n"
        f"export LARA_P9_BINARY={binary}\n"
        "case \"$1\" in\n"
        "  show) exec cat \"$(dirname \"$0\")/input.sexp\" ;;\n"
        f"  check) exec python3 -I {VIEWS} \"$LARA_P9_VIEW\" \"$(dirname \"$0\")/input.sexp\" ;;\n"
        "  *) echo 'usage: ./lara-view (show|check)' >&2; exit 2 ;;\n"
        "esac\n")
    script.chmod(0o555)
    return base


def claude_command(protocol: dict, prompt: str, budget: float, tools: str, allowed: list[str]) -> list[str]:
    agent = protocol["agent"]
    command = [agent["cli"], "-p", prompt, "--model", agent["model"],
               "--output-format", "stream-json", "--verbose",
               "--tools", tools, "--permission-mode", "default",
               "--setting-sources", "project", "--strict-mcp-config",
               "--no-session-persistence", "--max-budget-usd", f"{budget:.2f}"]
    if allowed:
        command += ["--allowedTools", *allowed]
    return command


def invoke(command: list[str], cwd: Path, env: dict, timeout: int, out: Path) -> dict:
    start = time.monotonic()
    timed_out = False
    with open(out / "transcript.jsonl", "wb") as transcript, open(out / "stderr.txt", "wb") as err:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=transcript, stderr=err)
        try:
            exit_code = process.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            process.kill()
            exit_code = process.wait()
            timed_out = True
    elapsed = time.monotonic() - start
    result = None
    for line in (out / "transcript.jsonl").read_text(errors="replace").splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        if event.get("type") == "result":
            result = event
    return {"exit_code": exit_code, "timed_out": timed_out, "elapsed_seconds": round(elapsed, 3),
            "cost_usd": (result or {}).get("total_cost_usd"),
            "num_turns": (result or {}).get("num_turns"),
            "result_subtype": (result or {}).get("subtype"),
            "final_text": (result or {}).get("result"),
            "usage": (result or {}).get("usage")}


def agent_env(arm: str) -> dict:
    env = {k: v for k, v in os.environ.items() if k in ("HOME", "PATH", "LANG", "USER", "TERM")}
    env["LARA_P9_VIEW"] = arm
    return env


class Ledger:
    """Append-only spend ledger; the ceiling is checked before every call."""

    def __init__(self, path: Path, ceiling: float):
        self.path, self.ceiling = path, ceiling

    def spent(self) -> float:
        if not self.path.exists():
            return 0.0
        return sum(json.loads(l)["charged_usd"] for l in self.path.read_text().splitlines() if l)

    def admit(self, cap: float) -> bool:
        return self.spent() + cap <= self.ceiling + 1e-9

    def charge(self, label: str, record: dict, cap: float) -> None:
        # An unreported cost (crash, kill) is charged at the full per-call cap.
        cost = record.get("cost_usd")
        charged = cap if cost is None else float(cost)
        with open(self.path, "a") as f:
            f.write(json.dumps({"call": label, "reported_usd": cost, "charged_usd": charged}) + "\n")


def build_binary() -> str:
    subprocess.run(["cabal", "build", "-v0", "exe:lara"], cwd=ROOT, check=True)
    return subprocess.run(["cabal", "list-bin", "lara"], cwd=ROOT, check=True,
                          capture_output=True, text=True).stdout.strip()


def git_head() -> str:
    return subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip()


def prompt_for(arm: str, task_id: str) -> str:
    parts = [(P9 / "agent" / "briefing.md").read_text(),
             (P9 / "agent" / f"feedback-{arm}.md").read_text(),
             (P9 / "tasks" / task_id / "task.md").read_text()]
    return "\n".join(parts)


def schedule(protocol: dict) -> list[tuple[str, str]]:
    rng = random.Random(protocol["design"]["seed"])
    tasks = [t["task_id"] for t in load(P9 / "answer-key.json")["tasks"]]
    rng.shuffle(tasks)
    # Counterbalanced: the arm run first alternates by task position, so each
    # arm goes first in exactly half the pairs; only the phase is random.
    offset = rng.randrange(2)
    order = []
    for index, task in enumerate(tasks):
        first = ARMS[(index + offset) % 2]
        order += [(task, first), (task, ARMS[1 - ARMS.index(first)])]
    return order


def smoke(args) -> int:
    protocol = approved_protocol()
    out = Path(args.out)
    out.mkdir(parents=True)
    ledger = Ledger(Path(args.ledger), protocol["budget"]["ceiling_usd"])
    cap = protocol["budget"]["smoke_cap_usd"]
    binary = build_binary()
    with tempfile.TemporaryDirectory(prefix="lara-p9-smoke-") as tmp:
        ws = workspace(Path(tmp) / "ws", P9 / "smoke", binary)
        prompt = (P9 / "smoke" / "prompt.md").read_text()
        record = invoke(claude_command(protocol, prompt, cap, "Bash", protocol["agent"]["allowed_tools"]),
                        ws, agent_env("status"), protocol["budget"]["smoke_timeout_seconds"], out)
    ledger.charge("smoke", record, cap)
    dump(out / "smoke.json", {"record": record, "binary": binary, "head": git_head()})
    print(json.dumps(record, indent=2))
    return 0


def run(args) -> int:
    protocol = approved_protocol()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    ledger = Ledger(Path(args.ledger), protocol["budget"]["ceiling_usd"])
    budget = protocol["budget"]
    binary = build_binary()
    order = schedule(protocol)
    dump(out / "run.json", {"protocol_sha256": sha256(P9 / "protocol.json"), "head": git_head(),
                            "binary": binary, "binary_sha256": sha256(Path(binary)),
                            "order": order, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())})
    for index, (task, arm) in enumerate(order):
        label = f"{index:02d}-{task}-{arm}"
        cell = out / "runs" / label
        if (cell / "record.json").exists():
            continue
        cell.mkdir(parents=True, exist_ok=True)
        if not ledger.admit(budget["run_cap_usd"]):
            dump(cell / "record.json", {"task_id": task, "arm": arm, "not_run": "budget ceiling"})
            continue
        prompt = prompt_for(arm, task)
        (cell / "prompt.md").write_text(prompt)
        with tempfile.TemporaryDirectory(prefix="lara-p9-") as tmp:
            ws = workspace(Path(tmp) / "ws", P9 / "tasks" / task, binary)
            record = invoke(claude_command(protocol, prompt, budget["run_cap_usd"], "Bash",
                                           protocol["agent"]["allowed_tools"]),
                            ws, agent_env(arm), budget["run_timeout_seconds"], cell)
        ledger.charge(label, record, budget["run_cap_usd"])
        record.update(task_id=task, arm=arm, order_index=index)
        dump(cell / "record.json", record)
        print(f"{label}: exit={record['exit_code']} timeout={record['timed_out']} "
              f"cost={record['cost_usd']} turns={record['num_turns']} spent={ledger.spent():.2f}", flush=True)
    dump(out / "finished.json", {"finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                                 "spent_usd": ledger.spent()})
    return 0


# --- scoring -----------------------------------------------------------------

REDACT = re.compile(r"lara-view|inquiry diagnostics?|public status view|diagnostics?", re.I)


def score(args) -> int:
    protocol = approved_protocol()
    out = Path(args.out)
    ledger = Ledger(Path(args.ledger), protocol["budget"]["ceiling_usd"])
    key = {t["task_id"]: t for t in load(P9 / "answer-key.json")["tasks"]}
    cells = sorted((out / "runs").iterdir())
    rng = random.Random(protocol["design"]["seed"] + 1)
    blind_order = list(cells)
    rng.shuffle(blind_order)
    scorer_template = (P9 / "scorer" / "prompt.md").read_text()
    cap = protocol["budget"]["scorer_cap_usd"]
    for n, cell in enumerate(blind_order):
        target = cell / "score.json"
        if target.exists():
            continue
        record = load(cell / "record.json")
        task = key[record["task_id"]]
        answer, parse_error = final_answer(record.get("final_text")) if "not_run" not in record else (None, "not run")
        result = {"task_id": record["task_id"], "arm": record["arm"], "parse_error": parse_error,
                  "mechanical": mechanical(task["expected"], answer)}
        blind = {"blind_id": f"B{n:02d}"}
        if answer is not None and ledger.admit(cap):
            shown = dict(answer)
            shown["justification"] = REDACT.sub("[tool]", str(shown.get("justification", "")))
            prompt = (scorer_template
                      .replace("{{TASK}}", (P9 / "tasks" / task["task_id"] / "task.md").read_text())
                      .replace("{{KEY}}", json.dumps(task["expected"], indent=2))
                      .replace("{{ANSWER}}", json.dumps(shown, indent=2)))
            scorer_dir = cell / "scorer"
            scorer_dir.mkdir(exist_ok=True)
            (scorer_dir / "prompt.md").write_text(prompt)
            with tempfile.TemporaryDirectory(prefix="lara-p9-score-") as tmp:
                rec = invoke(claude_command(protocol, prompt, cap, "", []), Path(tmp),
                             agent_env("status"), protocol["budget"]["scorer_timeout_seconds"], scorer_dir)
            ledger.charge(f"score-{cell.name}", rec, cap)
            verdict, error = final_answer(rec.get("final_text"))
            blind.update(record=rec, verdict=verdict, parse_error=error)
        else:
            blind["skipped"] = "no parsable answer" if answer is None else "budget ceiling"
        result["blind_scorer"] = blind
        verdict = blind.get("verdict") or {}
        unsupported = verdict.get("unsupported_assurance")
        result["primary_correct"] = (result["mechanical"]["all_fields_correct"] and unsupported is False)
        result["flag_for_researcher"] = (
            (result["mechanical"]["all_fields_correct"] and unsupported is not False) or
            (result["mechanical"]["all_fields_correct"] and verdict.get("justification_supports_answer") is False))
        dump(target, result)
        print(f"{cell.name}: fields={result['mechanical']['all_fields_correct']} "
              f"unsupported={unsupported} primary={result['primary_correct']}", flush=True)
    return 0


def summarize(args) -> int:
    out = Path(args.out)
    rows = []
    for cell in sorted((out / "runs").iterdir()):
        record, scored = load(cell / "record.json"), load(cell / "score.json")
        rows.append({"cell": cell.name, "task_id": record["task_id"], "arm": record["arm"],
                     "not_run": record.get("not_run"), "timed_out": record.get("timed_out"),
                     "exit_code": record.get("exit_code"), "cost_usd": record.get("cost_usd"),
                     "num_turns": record.get("num_turns"), "elapsed_seconds": record.get("elapsed_seconds"),
                     "answer_parsed": scored["mechanical"]["answer_parsed"],
                     "fields_correct": sum(f["correct"] for f in scored["mechanical"]["fields"].values()),
                     "fields_total": len(scored["mechanical"]["fields"]),
                     "all_fields_correct": scored["mechanical"]["all_fields_correct"],
                     "unsupported_assurance": (scored["blind_scorer"].get("verdict") or {}).get("unsupported_assurance"),
                     "primary_correct": scored["primary_correct"],
                     "flag_for_researcher": scored["flag_for_researcher"]})
    arms = {}
    for arm in ARMS:
        mine = [r for r in rows if r["arm"] == arm]
        arms[arm] = {"runs": len(mine), "primary_correct": sum(r["primary_correct"] for r in mine),
                     "all_fields_correct": sum(r["all_fields_correct"] for r in mine),
                     "unsupported_assurance": sum(r["unsupported_assurance"] is True for r in mine),
                     "timeouts_or_not_run": sum(bool(r["timed_out"] or r["not_run"]) for r in mine),
                     "cost_usd": round(sum(r["cost_usd"] or 0 for r in mine), 4),
                     "turns": sum(r["num_turns"] or 0 for r in mine),
                     "elapsed_seconds": round(sum(r["elapsed_seconds"] or 0 for r in mine), 1)}
    pairs = {}
    for r in rows:
        pairs.setdefault(r["task_id"], {})[r["arm"]] = r["primary_correct"]
    paired = {"inquiry_only": sorted(t for t, p in pairs.items() if p.get("inquiry") and not p.get("status")),
              "status_only": sorted(t for t, p in pairs.items() if p.get("status") and not p.get("inquiry")),
              "both": sorted(t for t, p in pairs.items() if p.get("status") and p.get("inquiry")),
              "neither": sorted(t for t, p in pairs.items() if not p.get("status") and not p.get("inquiry"))}
    # Exact two-sided McNemar over discordant pairs; descriptive only.
    b, c = len(paired["inquiry_only"]), len(paired["status_only"])
    n = b + c
    tail = sum(math.comb(n, k) for k in range(0, min(b, c) + 1)) / 2 ** n if n else 1.0
    paired["mcnemar_exact_two_sided_p"] = min(1.0, 2 * tail)
    summary = {"rows": rows, "arms": arms, "paired": paired,
               "spent_usd": Ledger(Path(args.ledger), 0).spent(),
               "scope": "feasibility only; no significance, efficacy, causal or discovery claim"}
    dump(out / "summary.json", summary)
    print(json.dumps({"arms": arms, "paired": paired, "spent_usd": summary["spent_usd"]}, indent=2))
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    sub.add_parser("check-key").set_defaults(func=check_key)
    for name, func in (("smoke", smoke), ("run", run), ("score", score), ("summarize", summarize)):
        p = sub.add_parser(name)
        p.add_argument("--out", required=True)
        p.add_argument("--ledger", required=True)
        p.set_defaults(func=func)
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
