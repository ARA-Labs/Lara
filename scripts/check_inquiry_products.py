#!/usr/bin/env python3
"""Exercise bounded guarded products without committing exponential fixtures."""
import itertools
import pathlib
import re
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
BIN = ROOT / "lean/.lake/build/bin/inquiry-run"
FIXTURES = ROOT / "fixtures/process/inquiry"
TIMEOUT = 10
HIGH_CAP = 10**18
BYTE_CAP = 1_000_000
TRUTH = "(truth)"
FALSE = "(not (truth))"


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) == 1, ("fixture shape changed", old)
    return text.replace(old, new, 1)


def document(base: str, guards: list[tuple[str, str]], cap: int) -> bytes:
    slots = []
    for slot_id, choices in enumerate(guards):
        choices_text = " ".join(
            f"(choice (choice-id {choice_id}) {guard} "
            "(checked-fragment 1 (node l (nil))))"
            for choice_id, guard in enumerate(choices)
        )
        slots.append(f"(slot (slot-id {slot_id}) ({choices_text}))")
    # These unique adjacent top-level blocks delimit the nested slot syntax.
    assert base.count(" (slots ") == base.count(" (bindings ") == 1
    prefix, remainder = base.split(" (slots ", 1)
    _, suffix = remainder.split(" (bindings ", 1)
    text = prefix + " (slots " + " ".join(slots) + ") (bindings " + suffix
    text = replace_once(text, "(claim)", "(claim c0)")
    text = replace_once(
        text, "(bindings () ())",
        "(bindings ((claim-binding c0 method (atom result (num 7)))) ())",
    )
    text = replace_once(text, "(requests)", "(requests (status products c0))")
    for counter in (
        "histories", "sources", "source-bytes", "declarations",
        "search-steps", "pairs", "subsets",
    ):
        value = cap if counter == "sources" else (
            BYTE_CAP if counter == "source-bytes" else HIGH_CAP
        )
        text, count = re.subn(rf"\({counter} \d+\)", f"({counter} {value})", text)
        assert count == 1, ("fixture limit changed", counter, count)
    result = text.encode("utf-8")
    assert len(result) < BYTE_CAP, ("source-byte cap masks product test", len(result))
    return result


def refusal(counter: str, actual: int, cap: int) -> bytes:
    return (
        f"(inquiry-error 1 () (limit (counter {counter}) "
        f"(actual {actual}) (cap {cap})))\n"
    ).encode()


def success(history: bytes, assignments: list[tuple[int, ...]]) -> bytes:
    rows = []
    for choices in assignments:
        assignment = " ".join(
            f"((slot-id {slot_id}) (choice-id {choice_id}))"
            for slot_id, choice_id in enumerate(choices)
        )
        rows.append(f"(family-row () ({assignment}) () ((published justified)))")
    size = len(rows)
    verdict = "true" if rows else "false"
    return history + (
        "(inquiry-result 1 products (status-body (family-status-result "
        f"({' '.join(rows)}) {size} {size} 0 {verdict})))\n"
    ).encode()


def check(command: list[str] | None = None, observer=None) -> None:
    """Check seven cases; observe verified output before temporary-file cleanup."""
    command = [str(BIN)] if command is None else list(command)
    assert command and all(isinstance(arg, str) and arg for arg in command), command
    base = (FIXTURES / "limit-sources-at-cap.sexp").read_text(encoding="utf-8")
    history = (FIXTURES / "limit-sources-at-cap.expected").read_bytes()
    assert history == (
        b"(inquiry-result 1 v0 (history-verdict (history-count 1) "
        b"(answer v0 certainTrue (completions 1))))\n"
    ), "fixture history changed"
    truth = (TRUTH, TRUTH)
    zero = (FALSE, FALSE)
    cases = [
        # Run this first so an old eager binary supplies failing-before evidence.
        ("huge-product", [truth] * 40, 1, 1, refusal("sources", 2, 1)),
        ("exact-at-cap", [truth] * 3, 8, 0,
         success(history, list(itertools.product(range(2), repeat=3)))),
        ("cap-plus-one", [truth] * 3, 7, 1, refusal("sources", 8, 7)),
        ("guard-pruned-at-cap", [(FALSE, TRUTH)] * 3, 1, 0,
         success(history, [(1, 1, 1)])),
        ("early-zero-survivors", [zero] + [truth] * 39, 1, 0,
         success(history, [])),
        # 65,536 live prefixes still fit the fixed 200,000 search-step ceiling.
        # The final false guard makes the family empty, not over the source cap.
        ("late-zero-survivors", [truth] * 16 + [zero], 1, 0,
         success(history, [])),
        # A larger prefix has zero rows too, but its logical extension count
        # exceeds the frozen search-step ceiling despite the high declared cap.
        ("late-zero-search-limit", [truth] * 39 + [zero], 1, 1,
         refusal("search-steps", 2**40 - 1, 200_000)),
    ]
    with tempfile.TemporaryDirectory(prefix="lara-inquiry-products-") as directory:
        for name, guards, cap, code, expected in cases:
            path = pathlib.Path(directory) / f"{name}.sexp"
            path.write_bytes(document(base, guards, cap))
            try:
                result = subprocess.run(
                    command + [str(path)], capture_output=True, timeout=TIMEOUT,
                )
            except (OSError, subprocess.TimeoutExpired) as error:
                raise AssertionError(
                    f"{name}: command failed within {TIMEOUT}s: {command!r}: {error}"
                ) from error
            assert result.returncode >= 0, ("driver killed by signal", command, result)
            # Exact output also rejects partial result envelopes before refusal.
            assert (result.returncode, result.stdout, result.stderr) == (
                code, expected, b""
            ), (name, result, expected)
            if observer is not None:
                observer(path, result.stdout)
    print(f"inquiry bounded products: {len(cases)} cases pass")


if __name__ == "__main__":
    check(sys.argv[1:] or None)
