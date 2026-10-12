#!/usr/bin/env python3
"""Pin each inquiry driver independently to frozen bytes and adversarial contracts.

Build each driver once, invoke binaries directly, and exercise the public Haskell
consumer codecs on the original documents and actual captured output. Goldens are
read-only: this gate has no update mode and never normalizes driver stdout.
"""
from __future__ import annotations

import os
import pathlib
import subprocess
import sys
import tempfile

from evidence_measured import canonical, parse
from inquiry_conformance_cases import Case, error, generated_cases
import check_inquiry_bytes
import check_inquiry_products

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROCESS = ROOT / "fixtures/process"
TIMEOUT = 10


def run(command, *, cwd=ROOT, env=None, timeout=TIMEOUT):
    """Spawn, timeout and signal failures are gate failures, never agreement."""
    try:
        result = subprocess.run([str(arg) for arg in command], cwd=cwd, env=env,
                                capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise AssertionError(f"command failed: {command!r}: {exc}") from exc
    assert result.returncode >= 0, ("driver killed by signal", command, result)
    return result


def build(command, *, cwd=ROOT):
    result = run(command, cwd=cwd, timeout=1800)
    assert result.returncode == 0, ("build failed", command, result)


def protocol(output, code):
    """Assert exact envelope ownership and refusal atomicity before comparison."""
    assert code in (0, 1, 2), ("unexpected exit", code, output)
    if not output:
        assert code == 0, ("empty refusal", code)
        return
    assert output.endswith(b"\n"), ("missing final LF", output)
    lines = output.split(b"\n")[:-1]
    assert all(lines), ("blank output line", output)
    forms = [parse(line) for line in lines]
    assert all(canonical(form) == line + b"\n" for form, line in zip(forms, lines)), ("noncanonical wire bytes", output)
    if code == 0:
        assert all(form[:2] == ["inquiry-result", "1"] for form in forms), (code, output)
    else:
        assert len(forms) == 1 and forms[0][:3] == ["inquiry-error", "1", []], ("partial results or multiple refusals", output)
        kind = forms[0][3][0]
        assert code == (1 if kind in ("limit", "unsupported") else 2), ("wrong refusal exit", code, output)


def golden_code(output):
    if not output:
        return 0
    first = parse(output.split(b"\n", 1)[0])
    code = 0 if first[0] == "inquiry-result" else (1 if first[3][0] in ("limit", "unsupported") else 2)
    protocol(output, code)
    return code


def discover():
    """The excluded process subtree has exactly two immediate fixture owners."""
    assert PROCESS.is_dir(), f"missing fixture family: {PROCESS}"
    for path in sorted(PROCESS.rglob("*")):
        if path.is_file() and path.suffix in (".sexp", ".expected"):
            relative = path.relative_to(PROCESS)
            assert len(relative.parts) == 2 and relative.parts[0] in ("run", "inquiry"), ("unowned or nested process fixture", relative)
            partner = path.with_suffix(".expected" if path.suffix == ".sexp" else ".sexp")
            assert partner.is_file(), ("missing fixture/golden partner", path, partner)
    for family in ("run", "inquiry"):
        assert list((PROCESS / family).glob("*.sexp")), ("empty process fixture family", family)
    return sorted((PROCESS / "inquiry").glob("*.sexp"))


def check_one(name, command, args, code, expected, *, env=None):
    protocol(expected, code)
    result = run(command + args, env=env)
    assert (result.returncode, result.stdout, result.stderr) == (code, expected, b""), (
        name, command, args, "expected", (code, expected, b""), "actual", result)
    protocol(result.stdout, result.returncode)
    return result.stdout


def input_mode(expected):
    """Predict decoder acceptance from the independently expected protocol."""
    if expected:
        envelope = parse(expected.split(b"\n", 1)[0])
        if envelope[0] == "inquiry-error":
            refusal = envelope[3]
            if refusal[0] in ("syntax", "version") or (
                refusal[0] == "malformed" and refusal[1] in (
                    "malformed inquiry-input", "expected an inquiry-input document")):
                return "rejected"
    return "accepted"


def consume(client, source, output, directory, serial, *, mode):
    capture = directory / f"stdout-{serial}.sexp"
    capture.write_bytes(output)
    result = run([client, "consume", mode, source, capture])
    assert (result.returncode, result.stdout, result.stderr) == (0, b"", b""), ("typed consumer", source, result)


def io_cases(commands, client, directory, serial, *, env=None, locale="default"):
    missing = directory / "missing-α\\file.sexp"
    unreadable = directory / "directory-α"
    unreadable.mkdir(exist_ok=True)
    for path in (missing, unreadable):
        for command in commands:
            stdout = check_one(f"{locale}/cannot-read", command, [str(path)], 2, error("io", "cannot read " + str(path)), env=env)
            # No readable original document exists here; consume the actual error
            # using a known original input only to supply the client namespace.
            consume(client, PROCESS / "inquiry/fixed-witness.sexp", stdout, directory, serial, mode="accepted")
            serial += 1
    valid = (PROCESS / "inquiry/limit-sources-at-cap.sexp").read_bytes()
    for name, document in [
        ("invalid-leading", b"\xff" + valid),
        ("invalid-comment", b"; comment \xff\n" + valid),
        ("invalid-trailing-comment", valid + b"; comment \xff"),
        ("invalid-trailing-bytes", valid + b"\xff"),
        ("invalid-before-syntax", b"( \xff"),
        ("invalid-after-syntax", b") ;\xff"),
        ("invalid-quoted", b'"\xff"'),
    ]:
        path = directory / f"{name}-α.sexp"
        path.write_bytes(document)
        for command in commands:
            stdout = check_one(f"{locale}/{name}", command, [str(path)], 2, error("io", "cannot read " + str(path)), env=env)
            consume(client, path, stdout, directory, serial, mode="invalid-utf8")
            serial += 1
    return serial


def main():
    fixtures = discover()
    # Fail setup before builds if independently expected cases are malformed.
    cases = generated_cases()
    assert len({case.name for case in cases}) == len(cases), "duplicate generated case names"
    for case in cases:
        protocol(case.stdout, case.code)
    build(["cabal", "build", "exe:lara"])
    build(["lake", "build", "inquiry-run"], cwd=ROOT / "lean")
    resolved = run(["cabal", "list-bin", "exe:lara"], timeout=60)
    assert resolved.returncode == 0 and resolved.stderr == b"", ("cannot resolve native driver", resolved)
    paths = resolved.stdout.decode("utf-8").splitlines()
    assert len(paths) == 1 and paths[0], ("ambiguous native driver", resolved)
    native = pathlib.Path(paths[0]).resolve()
    lean = (ROOT / "lean/.lake/build/bin/inquiry-run").resolve()
    assert native.is_file() and lean.is_file(), ("missing built driver", native, lean)
    commands = [[str(native), "inquiry"], [str(lean)]]
    with tempfile.TemporaryDirectory(prefix="lara-inquiry-conformance-") as temporary:
        directory = pathlib.Path(temporary)
        client = directory / "inquiry-codec-client"
        build(["cabal", "exec", "--", "ghc", "-package", "lara", "-outputdir", directory,
               "-o", client, ROOT / "scripts/inquiry-codec-client.hs"])
        values = run([client, "values", PROCESS / "inquiry/fixed-witness.sexp"])
        assert (values.returncode, values.stdout, values.stderr) == (0, b"", b""), ("typed constructor families", values)
        serial = 0
        for source in fixtures:
            expected = source.with_suffix(".expected").read_bytes()
            code = golden_code(expected)
            for command in commands:
                stdout = check_one(source.name, command, [str(source)], code, expected)
                consume(client, source, stdout, directory, serial, mode=input_mode(expected))
                serial += 1
        for case in cases:
            source = directory / f"{case.name}.sexp"
            source.write_bytes(case.document)
            for command in commands:
                stdout = check_one(case.name, command, [str(source)], case.code, case.stdout)
                consume(client, source, stdout, directory, serial, mode=input_mode(case.stdout))
                serial += 1
        for command, usage in zip(commands, ("usage: lara inquiry FILE", "usage: inquiry-run FILE")):
            for args in ([], [str(fixtures[0]), "extra"]):
                stdout = check_one("argument-arity", command, args, 2, error("usage", usage))
                consume(client, PROCESS / "inquiry/fixed-witness.sexp", stdout, directory, serial, mode="accepted")
                serial += 1
        serial = io_cases(commands, client, directory, serial)
        # C and POSIX are explicitly non-UTF-8 locales; C.utf8 is the contrast.
        # LC_ALL overrides any inherited UTF-8 locale. Drivers see real Unicode
        # argv paths, not an ASCII surrogate or a shell-generated replacement.
        locale_result = run(["locale", "-a"])
        assert locale_result.returncode == 0, locale_result
        available = set(locale_result.stdout.decode("ascii").splitlines())
        for locale in ("C", "POSIX", "C.utf8"):
            assert locale in available, ("required locale unavailable", locale, available)
            env = dict(os.environ, LC_ALL=locale, LANG=locale)
            serial = io_cases(commands, client, directory, serial, env=env, locale=locale)
            for case in cases:
                if case.name not in ("unicode-escaped-label", "unicode-bare", "backslash", "control-bare", "quoted-unicode-prefix", "invalid-unicode-escape"):
                    continue
                source = directory / f"路径-α-{case.name}.sexp"
                source.write_bytes(case.document)
                for command in commands:
                    stdout = check_one(f"{locale}/{case.name}", command, [str(source)], case.code, case.stdout, env=env)
                    consume(client, source, stdout, directory, serial, mode=input_mode(case.stdout))
                    serial += 1
        def boundary_consumer(source, stdout):
            nonlocal serial
            consume(client, source, stdout, directory, serial, mode="accepted")
            serial += 1

        for command in commands:
            check_inquiry_bytes.check(command, observer=boundary_consumer)
            check_inquiry_products.check(command, observer=boundary_consumer)
    print(f"inquiry conformance: {len(fixtures)} frozen fixtures, {len(cases)} generated cases, both boundary suites and CLI/locale contracts pass independently for both drivers")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, OSError, ValueError) as exc:
        print(f"FAIL: inquiry conformance: {exc}", file=sys.stderr)
        sys.exit(1)
