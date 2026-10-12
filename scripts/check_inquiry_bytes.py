#!/usr/bin/env python3
"""Exercise inquiry source-byte limits against actual UTF-8 input files."""
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BIN = ROOT / "lean/.lake/build/bin/inquiry-run"
FIXTURES = ROOT / "fixtures/process/inquiry"
LIMIT = re.compile(r"\(source-bytes \d+\)")


def with_cap(text: str, cap: int) -> str:
    return LIMIT.sub(f"(source-bytes {cap})", text)


def check(command: list[str] | None = None, observer=None) -> None:
    """Check six cases; observe verified output while its input still exists."""
    command = [str(BIN)] if command is None else list(command)
    assert command and all(isinstance(arg, str) and arg for arg in command), command
    base = (FIXTURES / "limit-source-bytes-at-cap.sexp").read_text(encoding="utf-8")
    expected = (FIXTURES / "limit-source-bytes-at-cap.expected").read_bytes()
    cases = {
        "ascii": base,
        "whitespace": " \n\t" + base + "\n  ",
        "unicode": base.replace("target interpretation", "观测解释"),
    }
    with tempfile.TemporaryDirectory(prefix="lara-inquiry-bytes-") as directory:
        for name, text in cases.items():
            for excess in (0, 1):
                cap = len(text.encode("utf-8")) - excess
                while True:
                    document = with_cap(text, cap).encode("utf-8")
                    required = len(document) - excess
                    if required == cap:
                        break
                    cap = required
                path = pathlib.Path(directory) / f"{name}-{excess}.sexp"
                path.write_bytes(document)
                try:
                    result = subprocess.run(command + [str(path)], capture_output=True, timeout=10)
                except (OSError, subprocess.TimeoutExpired) as error:
                    raise AssertionError(f"{name}-{excess}: command failed: {command!r}: {error}") from error
                assert result.returncode >= 0, ("driver killed by signal", command, result)
                if excess:
                    output = (
                        "(inquiry-error 1 () (limit (counter source-bytes) "
                        f"(actual {len(document)}) (cap {cap})))\n"
                    ).encode()
                else:
                    output = expected
                assert (result.returncode, result.stdout, result.stderr) == (
                    excess, output, b""
                ), (name, excess, cap, len(document), result)
                if observer is not None:
                    observer(path, result.stdout)
    print("inquiry UTF-8 byte limits: 6 boundary cases pass")


if __name__ == "__main__":
    check(sys.argv[1:] or None)
