#!/usr/bin/env python3
"""Check the runnable Lean report against the proved demo outcomes.

`make lean-gate` builds the executable first. The theorem module proves the
finite leaf check's connection to leaf_ok and refutes any withdrawn bridge;
this gate ensures the user-facing executable reports those same cases.
"""
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXPECTED = """Axiom withdrawal: separate Lean structural-contract witness
source admission (admit): accepted
source admission (quarantine): accepted
source admission (reject): rejected (R8)
unit checker (admit): true
unit checker (quarantine): true
local status (admit): justified
local status (quarantine): gap
identity leaf preservation (retained): true
identity leaf preservation (withdrawn): false
ND replay (premise present): true
ND replay (premise absent): false
"""


def main():
    result = subprocess.run(
        [str(ROOT / "lean/.lake/build/bin/axiom-withdrawal")],
        capture_output=True, text=True, timeout=30,
    )
    assert result.returncode == 0, (result.returncode, result.stdout, result.stderr)
    assert result.stderr == "", result.stderr
    assert result.stdout == EXPECTED, result.stdout
    print(result.stdout, end="")
    print("Axiom-withdrawal executable gate passed.")


if __name__ == "__main__":
    main()
