#!/usr/bin/env python3
"""The two P9 feedback views over one real ``lara inquiry`` capture.

``status`` is the control view: the full public status of every accepted family
row or impact endpoint, and nothing else -- the same projection as P8's
``snapshot_only``. ``inquiry`` is the treatment view: that status view plus the
complete inquiry result forms. Both views run the same binary on the same
document, so the treatment differs from the control only in the added
diagnostics.
"""
from __future__ import annotations

import os
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from evidence_measured import parse, wire  # noqa: E402


def forms_of(stdout: str) -> list:
    return [parse(line) for line in stdout.splitlines() if line.strip()]


def status_lines(forms: list) -> list[str]:
    """Public statuses only: rejected rows, audits, stability, sensitivity,
    assumptions and locality are omitted, exactly as in P8's snapshot view."""
    lines = []
    for form in forms:
        if form[0] != "inquiry-result":
            lines.append(f"refusal {wire(form)}")
            continue
        label, body = form[2], form[3]
        if body[0] == "status-body":
            for row in body[1][1]:
                if row[4]:
                    lines.append(f"{label} history={wire(row[1])} choices={wire(row[2])} "
                                 f"status={wire(row[4][0])}")
        elif body[0] == "impact-body":
            for row in body[1][2]:
                for endpoint, status in (("before", row[2]), ("after", row[3])):
                    if status:
                        lines.append(f"{label} query={wire(row[1])} {endpoint} status={wire(status[0])}")
    return lines


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[1] not in ("status", "inquiry"):
        print("usage: inquiry_p9_views.py (status|inquiry) FILE", file=sys.stderr)
        return 2
    binary = os.environ["LARA_P9_BINARY"]
    run = subprocess.run([binary, "inquiry", argv[2]], capture_output=True, text=True, timeout=60)
    if run.returncode not in (0, 1):
        print(f"lara inquiry failed with exit {run.returncode}", file=sys.stderr)
        return 1
    forms = forms_of(run.stdout)
    print("== public status view ==")
    print("\n".join(status_lines(forms)) or "(no accepted rows or endpoints)")
    if argv[1] == "inquiry":
        print("== inquiry diagnostics ==")
        sys.stdout.write(run.stdout)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
