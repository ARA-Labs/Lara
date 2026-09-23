#!/usr/bin/env python3
"""Freeze the B2-derived replay artifacts for one bundle.

Usage:
    scripts/freeze-bundle.py BUNDLE_DIR [LARA_BIN]

The writer derives emitted.core.sexp through gen-worked-examples.hs, captures the
exact stdout and exit code of `lara check emitted.lara` with BUNDLE_DIR as cwd,
and writes the canonical manifest last. LARA_BIN may also be supplied through
$LARA_BIN. Without either, the script builds and locates exe:lara with cabal.

Exit 0 means all three files were frozen. Exit 2 means inputs, tools, derivation,
or checker execution failed; no new manifest is installed on failure.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAT = "lara-replay-bundle@1"
CORE_VERSION = "0.2"
ARTIFACTS = {
    "core-sexp": "emitted.core.sexp",
    "emitted-lara": "emitted.lara",
    "policy-copy": "empirical-v1.policy.lara",
    "provenance": "provenance.json",
    "source": "source.yaml",
    "verdict": "verdict.txt",
}
CHECKER_PATHS = ("src/", "app/", "lean/", "lara.cabal", "cabal.project")
HEX40_RE = re.compile(r"[0-9a-f]{40}\Z")
POLICY_RE = re.compile(r"(?m)^policy ([a-z][a-z0-9_-]*)\s*$")
BACKENDS_RE = re.compile(r"(?m)^use backends \[([^\]]*)\]\s*$")
REQUIRES_PYTHON_RE = re.compile(r'^# requires-python = "([^"]+)"$', re.MULTILINE)
PYYAML_RE = re.compile(r'pyyaml==([0-9]+(?:\.[0-9]+)*)', re.IGNORECASE)


class FreezeError(Exception):
    """A deterministic freeze/setup failure reported with exit code 2."""


def run(
    argv: list[str],
    *,
    cwd: Path,
    allowed_exits: set[int] | None = None,
) -> subprocess.CompletedProcess[bytes]:
    try:
        result = subprocess.run(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as exc:
        raise FreezeError(f"cannot execute {argv[0]!r}: {exc}") from exc
    allowed = {0} if allowed_exits is None else allowed_exits
    if result.returncode not in allowed:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        suffix = f": {detail}" if detail else ""
        raise FreezeError(f"command exited {result.returncode}: {' '.join(argv)}{suffix}")
    return result


def find_repo_root() -> Path:
    return Path(__file__).resolve().parent.parent


def resolve_checker(repo_root: Path, argument: str | None) -> Path:
    candidate = argument or os.environ.get("LARA_BIN")
    if candidate:
        path = Path(candidate).expanduser()
        if not path.is_absolute():
            path = Path.cwd() / path
        path = path.resolve()
    else:
        run(["cabal", "build", "exe:lara"], cwd=repo_root)
        output = run(["cabal", "list-bin", "exe:lara"], cwd=repo_root).stdout
        path = Path(output.decode("utf-8").strip()).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        raise FreezeError(f"lara binary is not executable: {path}")
    return path


def read_program_identity(bundle: Path) -> tuple[str, list[str]]:
    emitted_path = bundle / ARTIFACTS["emitted-lara"]
    try:
        text = emitted_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise FreezeError(f"cannot read {emitted_path}: {exc}") from exc
    policy_match = POLICY_RE.search(text)
    backends_match = BACKENDS_RE.search(text)
    if policy_match is None or backends_match is None:
        raise FreezeError("emitted.lara is missing its policy or backend header")
    policy_id = policy_match.group(1)
    backends_text = backends_match.group(1).strip()
    backends = [] if not backends_text else [item.strip() for item in backends_text.split(",")]
    if policy_id != "empirical-v1":
        raise FreezeError(f"walking-skeleton policy must be empirical-v1, got {policy_id}")
    if backends != ["nd@1"]:
        raise FreezeError(f"walking-skeleton backends must be ['nd@1'], got {backends!r}")
    return policy_id, backends


def checker_revision(repo_root: Path) -> str:
    result = run(
        ["git", "log", "-1", "--format=%H", "--", *CHECKER_PATHS],
        cwd=repo_root,
    )
    revision = result.stdout.decode("ascii", errors="strict").strip()
    if HEX40_RE.fullmatch(revision) is None:
        raise FreezeError(f"invalid checker source revision: {revision!r}")
    return revision


def producer_toolchain(repo_root: Path) -> dict[str, str]:
    elaborator_path = repo_root / "elaborator" / "elaborate.py"
    try:
        source = elaborator_path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise FreezeError(f"cannot read {elaborator_path}: {exc}") from exc
    python_match = REQUIRES_PYTHON_RE.search(source)
    pyyaml_match = PYYAML_RE.search(source)
    if python_match is None or pyyaml_match is None:
        raise FreezeError("elaborator PEP 723 header is missing pinned Python/PyYAML metadata")
    requires_python = python_match.group(1)
    pyyaml_version = pyyaml_match.group(1)

    uv_output = run(["uv", "--version"], cwd=repo_root).stdout.decode("ascii", errors="strict").strip()
    uv_fields = uv_output.split()
    if len(uv_fields) < 2 or uv_fields[0] != "uv":
        raise FreezeError(f"unexpected uv --version output: {uv_output!r}")
    uv_version = uv_fields[1]

    python_output = run(
        [
            "uv",
            "run",
            "--no-project",
            "--python",
            requires_python,
            "--with",
            f"pyyaml=={pyyaml_version}",
            "python",
            "-c",
            "import platform, yaml; print(platform.python_version()); print(yaml.__version__)",
        ],
        cwd=repo_root,
    ).stdout.decode("ascii", errors="strict").splitlines()
    if len(python_output) != 2 or python_output[1] != pyyaml_version:
        raise FreezeError(f"unexpected producer environment versions: {python_output!r}")
    return {
        "elaborator": "elaborator/elaborate.py",
        "python": python_output[0],
        "pyyaml": python_output[1],
        "uv": uv_version,
    }


def canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("ascii")


def install_frozen_outputs(stage: Path, outputs: list[tuple[Path, Path]]) -> None:
    """Install staged outputs transactionally, preserving every prior destination."""
    destination_states: list[tuple[Path, bool]] = []
    for _, destination in outputs:
        try:
            mode = destination.lstat().st_mode
        except FileNotFoundError:
            destination_states.append((destination, False))
            continue
        except OSError as exc:
            raise FreezeError(f"cannot inspect freeze output {destination}: {exc}") from exc
        if not stat.S_ISREG(mode):
            raise FreezeError(
                f"freeze output destination is not a regular non-symlink file: {destination}"
            )
        destination_states.append((destination, True))

    try:
        backup_dir = Path(tempfile.mkdtemp(prefix=".rollback-", dir=stage))
    except OSError as exc:
        raise FreezeError(f"cannot prepare freeze rollback: {exc}") from exc

    backups: dict[Path, Path] = {}
    installed: set[Path] = set()
    try:
        for index, (destination, existed) in enumerate(destination_states):
            if existed:
                backup = backup_dir / f"{index}-{destination.name}"
                os.replace(destination, backup)
                backups[destination] = backup
        for source, destination in outputs:
            os.replace(source, destination)
            installed.add(destination)
    except OSError as install_error:
        rollback_errors: list[str] = []
        for destination, existed in reversed(destination_states):
            try:
                if existed and destination in backups:
                    os.replace(backups[destination], destination)
                elif not existed and destination in installed:
                    destination.unlink()
            except OSError as rollback_error:
                rollback_errors.append(f"{destination}: {rollback_error}")
        message = f"cannot install frozen outputs: {install_error}"
        if rollback_errors:
            message += "; rollback failed: " + "; ".join(rollback_errors)
        raise FreezeError(message) from install_error


def freeze(bundle_arg: str, checker_arg: str | None) -> None:
    repo_root = find_repo_root()
    bundle = Path(bundle_arg).expanduser()
    if not bundle.is_absolute():
        bundle = Path.cwd() / bundle
    bundle = bundle.resolve()
    if not bundle.is_dir():
        raise FreezeError(f"bundle directory does not exist: {bundle}")
    if bundle.name != "walking-skeleton":
        raise FreezeError(f"B2 freezes only walking-skeleton, got {bundle.name!r}")

    policy_id, backends = read_program_identity(bundle)
    for artifact in ("source", "policy-copy", "emitted-lara", "provenance"):
        path = bundle / ARTIFACTS[artifact]
        if not path.is_file() or path.is_symlink():
            raise FreezeError(f"required bundle input is not a regular file: {path}")

    checker = resolve_checker(repo_root, checker_arg)
    revision = checker_revision(repo_root)
    toolchain = producer_toolchain(repo_root)
    policy_path = bundle / ARTIFACTS["policy-copy"]
    policy_sha256 = hashlib.sha256(policy_path.read_bytes()).hexdigest()

    with tempfile.TemporaryDirectory(prefix=".freeze-", dir=bundle) as stage_name:
        stage = Path(stage_name)
        shutil.copyfile(bundle / ARTIFACTS["emitted-lara"], stage / ARTIFACTS["emitted-lara"])
        shutil.copyfile(policy_path, stage / ARTIFACTS["policy-copy"])
        run(
            [
                "cabal",
                "exec",
                "--",
                "runghc",
                "scripts/gen-worked-examples.hs",
                "--bundle",
                str(stage),
            ],
            cwd=repo_root,
        )
        core_path = stage / ARTIFACTS["core-sexp"]
        if not core_path.is_file():
            raise FreezeError("core generator did not produce emitted.core.sexp")

        verdict = run(
            [str(checker), "check", ARTIFACTS["emitted-lara"]],
            cwd=bundle,
            allowed_exits={0, 1, 2},
        )
        if verdict.returncode == 2 and verdict.stdout:
            raise FreezeError("checker boundary failure unexpectedly wrote stdout")

        manifest = {
            "format": FORMAT,
            "skeleton": bundle.name,
            "lara-core": CORE_VERSION,
            "artifacts": ARTIFACTS,
            "trusted-inputs": {
                "policy": {
                    "id": policy_id,
                    "sha256": policy_sha256,
                    "copied-from": f"examples/E1/{policy_id}.policy.lara",
                },
                "backends": backends,
                "theories": [],
            },
            "checker-source-revision": revision,
            "producer-toolchain": toolchain,
            "frozen-verdict": {"exit-code": verdict.returncode},
        }
        (stage / ARTIFACTS["verdict"]).write_bytes(verdict.stdout)
        (stage / "manifest.json").write_bytes(canonical_json(manifest))

        install_frozen_outputs(
            stage,
            [
                (core_path, bundle / ARTIFACTS["core-sexp"]),
                (stage / ARTIFACTS["verdict"], bundle / ARTIFACTS["verdict"]),
                (stage / "manifest.json", bundle / "manifest.json"),
            ],
        )

    print(f"froze {bundle / ARTIFACTS['core-sexp']}")
    print(f"froze {bundle / ARTIFACTS['verdict']}")
    print(f"froze {bundle / 'manifest.json'}")


def main() -> int:
    if len(sys.argv) not in (2, 3):
        print("usage: freeze-bundle.py BUNDLE_DIR [LARA_BIN]", file=sys.stderr)
        return 2
    try:
        freeze(sys.argv[1], sys.argv[2] if len(sys.argv) == 3 else None)
    except FreezeError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    except (OSError, UnicodeError, ValueError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
