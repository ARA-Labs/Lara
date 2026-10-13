#!/usr/bin/env python3
"""Post-hoc arm-isolation audit over every retained P9 task transcript.

The isolation check could not exercise direct execution of the views script or
the ``lara`` binary (the agent declined those steps), so this audit inspects the
actual runs instead. For every run it lists each Bash call, whether it was one
of the two allowed commands, whether the CLI refused it, and whether any tool
result in a status-arm run carries inquiry diagnostics. A status-arm run that
received diagnostics is a protocol breach.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ALLOWED = {"./lara-view show", "./lara-view check"}
DIAGNOSTIC_MARKERS = ("== inquiry diagnostics ==", "(inquiry-result ")


def allowed(command) -> bool:
    """A compound command is allowed when every part is an allowed command,
    matching how the CLI checks each subcommand against the allowlist."""
    if not isinstance(command, str):
        return False
    parts = [p.strip() for p in re.split(r"&&|\|\||;|\n", command) if p.strip()]
    return bool(parts) and all(p in ALLOWED for p in parts)


def text_of(content) -> str:
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "\n".join(text_of(c.get("text", c.get("content", ""))) if isinstance(c, dict) else str(c)
                         for c in content)
    return str(content)


def audit_run(cell: Path) -> dict:
    record = json.loads((cell / "record.json").read_text())
    calls, results = {}, {}
    transcript = cell / "transcript.jsonl"
    lines = transcript.read_text(errors="replace").splitlines() if transcript.exists() else []
    for line in lines:
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            continue
        message = event.get("message") if isinstance(event, dict) else None
        content = message.get("content") if isinstance(message, dict) else None
        if not isinstance(content, list):
            continue
        for item in content:
            if item.get("type") == "tool_use":
                calls[item["id"]] = {"tool": item["name"], "command": item["input"].get("command")}
            elif item.get("type") == "tool_result":
                results[item["tool_use_id"]] = {"is_error": bool(item.get("is_error")),
                                                "text": text_of(item.get("content"))}
    entries = []
    for call_id, call in calls.items():
        result = results.get(call_id, {"is_error": None, "text": ""})
        entries.append({"tool": call["tool"], "command": call["command"],
                        "allowed_command": allowed(call["command"]),
                        "refused": result["is_error"],
                        "diagnostics_in_result": any(m in result["text"] for m in DIAGNOSTIC_MARKERS)})
    arm = record.get("arm")
    breach = arm == "status" and any(e["diagnostics_in_result"] for e in entries)
    return {"cell": cell.name, "task_id": record.get("task_id"), "arm": arm, "calls": entries,
            "unlisted_calls_executed": [e["command"] for e in entries
                                        if not e["allowed_command"] and e["refused"] is False],
            "unlisted_calls_refused": [e["command"] for e in entries
                                       if not e["allowed_command"] and e["refused"]],
            "status_arm_received_diagnostics": breach}


def main(argv: list[str]) -> int:
    out = Path(argv[1])
    runs = [audit_run(cell) for cell in sorted((out / "runs").iterdir())]
    breaches = [r["cell"] for r in runs if r["status_arm_received_diagnostics"]]
    report = {"basis": "every tool call and tool result in each retained task transcript",
              "runs": runs, "breaches": breaches, "isolation_held": not breaches}
    (out / "isolation-audit.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for r in runs:
        print(f"{r['cell']}: calls={len(r['calls'])} unlisted_executed={r['unlisted_calls_executed']} "
              f"unlisted_refused={r['unlisted_calls_refused']} breach={r['status_arm_received_diagnostics']}")
    print("isolation:", "HELD" if not breaches else f"BREACHED in {breaches}")
    return 1 if breaches else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
