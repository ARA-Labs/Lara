#!/usr/bin/env bash
# Replay an untrusted lara-replay-bundle@1 without extending the trusted CLI.
#
# Usage:  scripts/replay.sh BUNDLE_DIR [LARA_BIN]
#         LARA_BIN=/path/to/lara scripts/replay.sh BUNDLE_DIR
#
# The manifest is parsed and schema/canonicalization-checked first. Every bundled
# trusted input is then hashed; a mismatch exits 1 before checker discovery or
# execution. Checker-source drift prints a loud warning but does not stop replay.
# Finally, `lara check emitted.lara` runs with BUNDLE_DIR as cwd and its stdout
# bytes and exit code are compared independently with the frozen verdict.
#
# Exit 0: replay stdout and exit code both match.
# Exit 1: trusted-input integrity failure or replay verdict/exit mismatch.
# Exit 2: usage, manifest/schema, bundle, or checker setup error.
set -eu

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
exec python3 - "$repo_root" "$@" <<'PY'
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

FORMAT = "lara-replay-bundle@1"
EXPECTED_SKELETON = "walking-skeleton"
CORE_VERSION = "0.2"
CHECKER_PATHS = ("src/", "app/", "lean/", "lara.cabal", "cabal.project")
EXPECTED_ARTIFACTS = {
    "core-sexp": "emitted.core.sexp",
    "emitted-lara": "emitted.lara",
    "policy-copy": "empirical-v1.policy.lara",
    "provenance": "provenance.json",
    "source": "source.yaml",
    "verdict": "verdict.txt",
}
HEX40_RE = re.compile(r"[0-9a-f]{40}\Z")
HEX64_RE = re.compile(r"[0-9a-f]{64}\Z")
VERSION_RE = re.compile(r"[0-9]+(?:\.[0-9]+)+\Z")
ID_RE = re.compile(r"[a-z][a-z0-9_-]*\Z")


class ReplayError(Exception):
    exit_code = 2


class IntegrityError(ReplayError):
    exit_code = 1


def fail(message: str) -> None:
    raise ReplayError(message)


def require(condition: bool, message: str) -> None:
    if not condition:
        fail(message)


def require_exact_keys(value: object, expected: set[str], where: str) -> dict[str, object]:
    require(type(value) is dict, f"manifest {where} must be an object")
    obj = value
    actual = set(obj)
    require(actual == expected, f"manifest {where} keys must be {sorted(expected)!r}, got {sorted(actual)!r}")
    return obj


def require_string(value: object, where: str) -> str:
    require(type(value) is str and bool(value), f"manifest {where} must be a non-empty string")
    return value


def load_manifest(bundle: Path) -> dict[str, object]:
    path = bundle / "manifest.json"
    require(path.is_file() and not path.is_symlink(), "manifest.json must be a regular file")
    try:
        raw = path.read_bytes()
        text = raw.decode("utf-8")
        value = json.loads(text)
    except (OSError, UnicodeError, json.JSONDecodeError) as exc:
        fail(f"cannot parse manifest.json: {exc}")
    canonical = (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("ascii")
    require(raw == canonical, "manifest.json is not canonical JSON (sorted keys, indent=2, ASCII, one LF)")
    return require_exact_keys(
        value,
        {
            "format",
            "skeleton",
            "lara-core",
            "artifacts",
            "trusted-inputs",
            "checker-source-revision",
            "producer-toolchain",
            "frozen-verdict",
        },
        "root",
    )


def validate_manifest(manifest: dict[str, object], bundle: Path) -> tuple[Path, Path, int, str]:
    require(manifest["format"] == FORMAT, f"manifest format must be {FORMAT!r}")
    require(manifest["lara-core"] == CORE_VERSION, f"manifest lara-core must be {CORE_VERSION!r}")
    skeleton = require_string(manifest["skeleton"], "skeleton")
    require(skeleton == EXPECTED_SKELETON, f"manifest skeleton must be {EXPECTED_SKELETON!r}")
    require(skeleton == bundle.name, f"manifest skeleton {skeleton!r} does not match bundle directory {bundle.name!r}")

    artifacts = require_exact_keys(manifest["artifacts"], set(EXPECTED_ARTIFACTS), "artifacts")
    require(artifacts == EXPECTED_ARTIFACTS, f"manifest artifacts must equal {EXPECTED_ARTIFACTS!r}")

    trusted = require_exact_keys(manifest["trusted-inputs"], {"policy", "backends", "theories"}, "trusted-inputs")
    backends = trusted["backends"]
    require(backends == ["nd@1"], "manifest trusted-inputs.backends must be ['nd@1']")

    theories = trusted["theories"]
    require(type(theories) is list, "manifest trusted-inputs.theories must be an array")
    for index, entry in enumerate(theories):
        theory = require_exact_keys(entry, {"backend", "theory", "sha256"}, f"trusted-inputs.theories[{index}]")
        require_string(theory["backend"], f"trusted-inputs.theories[{index}].backend")
        require_string(theory["theory"], f"trusted-inputs.theories[{index}].theory")
        theory_hash = require_string(theory["sha256"], f"trusted-inputs.theories[{index}].sha256")
        require(HEX64_RE.fullmatch(theory_hash) is not None, f"manifest theory sha256 at index {index} must be 64 lowercase hex")
    require(not theories, "non-empty theory registries are not supported by the current frozen frontend")

    policy = require_exact_keys(trusted["policy"], {"id", "sha256", "copied-from"}, "trusted-inputs.policy")
    policy_id = require_string(policy["id"], "trusted-inputs.policy.id")
    require(ID_RE.fullmatch(policy_id) is not None, "manifest trusted-inputs.policy.id is invalid")
    policy_hash = require_string(policy["sha256"], "trusted-inputs.policy.sha256")
    require(HEX64_RE.fullmatch(policy_hash) is not None, "manifest policy sha256 must be 64 lowercase hex")
    copied_from = require_string(policy["copied-from"], "trusted-inputs.policy.copied-from")
    copied_path = Path(copied_from)
    require(not copied_path.is_absolute() and ".." not in copied_path.parts, "manifest copied-from must be repo-relative without '..'")
    require(policy_id == "empirical-v1", "walking-skeleton policy id must be 'empirical-v1'")
    require(copied_from == "examples/E1/empirical-v1.policy.lara", "manifest policy copied-from is not the B0-pinned path")

    revision = require_string(manifest["checker-source-revision"], "checker-source-revision")
    require(HEX40_RE.fullmatch(revision) is not None, "manifest checker-source-revision must be 40 lowercase hex")

    toolchain = require_exact_keys(
        manifest["producer-toolchain"],
        {"elaborator", "python", "pyyaml", "uv"},
        "producer-toolchain",
    )
    require(toolchain["elaborator"] == "elaborator/elaborate.py", "manifest producer-toolchain.elaborator is invalid")
    for key in ("python", "pyyaml", "uv"):
        version = require_string(toolchain[key], f"producer-toolchain.{key}")
        require(VERSION_RE.fullmatch(version) is not None, f"manifest producer-toolchain.{key} must be a dotted version")

    frozen = require_exact_keys(manifest["frozen-verdict"], {"exit-code"}, "frozen-verdict")
    expected_exit = frozen["exit-code"]
    require(type(expected_exit) is int and expected_exit in (0, 1, 2), "manifest frozen-verdict.exit-code must be 0, 1, or 2")

    for filename in EXPECTED_ARTIFACTS.values():
        artifact_path = bundle / filename
        require(artifact_path.is_file() and not artifact_path.is_symlink(), f"bundle artifact must be a regular file: {filename}")

    policy_path = bundle / EXPECTED_ARTIFACTS["policy-copy"]
    verdict_path = bundle / EXPECTED_ARTIFACTS["verdict"]
    return policy_path, verdict_path, expected_exit, revision


def verify_trusted_inputs(policy_path: Path, manifest: dict[str, object]) -> None:
    trusted = manifest["trusted-inputs"]
    assert isinstance(trusted, dict)
    policy = trusted["policy"]
    assert isinstance(policy, dict)
    expected = policy["sha256"]
    try:
        actual = hashlib.sha256(policy_path.read_bytes()).hexdigest()
    except OSError as exc:
        raise ReplayError(f"cannot hash trusted policy {policy_path.name}: {exc}") from exc
    if actual != expected:
        raise IntegrityError(
            f"trusted input hash mismatch for {policy_path.name}: expected {expected}, got {actual}"
        )


def current_checker_revision(repo_root: Path) -> str | None:
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%H", "--", *CHECKER_PATHS],
            cwd=repo_root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError:
        return None
    if result.returncode != 0:
        return None
    revision = result.stdout.decode("ascii", errors="ignore").strip()
    return revision if HEX40_RE.fullmatch(revision) is not None else None


def warn_revision(repo_root: Path, expected: str) -> None:
    current = current_checker_revision(repo_root)
    if current == expected:
        return
    print("WARNING: CHECKER SOURCE REVISION DRIFT", file=sys.stderr)
    print(f"  frozen:  {expected}", file=sys.stderr)
    print(f"  current: {current if current is not None else 'unavailable (not a checker source checkout)'}", file=sys.stderr)
    print("  replay will continue; verdict bytes and exit code decide", file=sys.stderr)


def resolve_checker(repo_root: Path, argument: str | None) -> Path:
    candidate = argument or os.environ.get("LARA_BIN")
    if candidate:
        path = Path(candidate).expanduser()
        if not path.is_absolute():
            path = Path.cwd() / path
        path = path.resolve()
    else:
        cabal = shutil.which("cabal")
        if cabal is None:
            fail("no LARA_BIN supplied and cabal is unavailable")
        build = subprocess.run(
            [cabal, "build", "exe:lara"],
            cwd=repo_root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if build.returncode != 0:
            detail = build.stderr.decode("utf-8", errors="replace").strip()
            fail(f"cabal build exe:lara failed{': ' + detail if detail else ''}")
        located = subprocess.run(
            [cabal, "list-bin", "exe:lara"],
            cwd=repo_root,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if located.returncode != 0:
            fail("cabal list-bin exe:lara failed")
        path = Path(located.stdout.decode("utf-8", errors="strict").strip()).resolve()
    require(path.is_file() and os.access(path, os.X_OK), f"lara binary is not executable: {path}")
    return path


def first_difference(expected: bytes, actual: bytes) -> str:
    limit = min(len(expected), len(actual))
    for offset in range(limit):
        if expected[offset] != actual[offset]:
            return f"first byte difference at offset {offset}: expected 0x{expected[offset]:02x}, got 0x{actual[offset]:02x}"
    return f"common prefix length {limit}; expected {len(expected)} bytes, got {len(actual)} bytes"


def replay(repo_root: Path, bundle_arg: str, checker_arg: str | None) -> int:
    bundle = Path(bundle_arg).expanduser()
    if not bundle.is_absolute():
        bundle = Path.cwd() / bundle
    bundle = bundle.resolve()
    require(bundle.is_dir(), f"bundle directory does not exist: {bundle}")

    manifest = load_manifest(bundle)
    policy_path, verdict_path, expected_exit, expected_revision = validate_manifest(manifest, bundle)
    verify_trusted_inputs(policy_path, manifest)
    warn_revision(repo_root, expected_revision)

    checker = resolve_checker(repo_root, checker_arg)
    try:
        expected_stdout = verdict_path.read_bytes()
    except OSError as exc:
        fail(f"cannot read frozen verdict: {exc}")
    try:
        result = subprocess.run(
            [str(checker), "check", EXPECTED_ARTIFACTS["emitted-lara"]],
            cwd=bundle,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except OSError as exc:
        fail(f"cannot execute checker: {exc}")
    if result.stderr:
        sys.stderr.buffer.write(result.stderr)

    stdout_matches = result.stdout == expected_stdout
    exit_matches = result.returncode == expected_exit
    if not stdout_matches:
        print(f"ERROR: replay verdict bytes differ: {first_difference(expected_stdout, result.stdout)}", file=sys.stderr)
    if not exit_matches:
        print(f"ERROR: replay exit code differs: expected {expected_exit}, got {result.returncode}", file=sys.stderr)
    if not stdout_matches or not exit_matches:
        return 1

    print(f"PASS: replay matched {verdict_path} byte-for-byte (exit {expected_exit})")
    return 0


def main() -> int:
    if len(sys.argv) not in (3, 4):
        print("usage: replay.sh BUNDLE_DIR [LARA_BIN]", file=sys.stderr)
        return 2
    repo_root = Path(sys.argv[1]).resolve()
    try:
        return replay(repo_root, sys.argv[2], sys.argv[3] if len(sys.argv) == 4 else None)
    except ReplayError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return exc.exit_code
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
PY
