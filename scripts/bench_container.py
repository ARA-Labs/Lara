#!/usr/bin/env python3
"""Run the publication benchmark in a pinned local arm64 container."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Dict, List, Mapping, Optional, Sequence


WORKFLOW = "Haskell"
PLATFORM = "linux/arm64"
DOCKERFILE = Path("containers/bench/Dockerfile")
REQUIRED_OUTPUTS = (
    "bench.json",
    "performance.txt",
    "performance.md",
    "performance.tex",
)


class BenchError(RuntimeError):
    """A publication-run precondition or execution failure."""


class QuietWindowTimeout(BenchError):
    """A quiet-window timeout with the samples collected before failure."""

    def __init__(self, message: str, events: Sequence[Mapping[str, Any]]) -> None:
        super().__init__(message)
        self.events = [dict(event) for event in events]


class QuietWindowInterrupted(KeyboardInterrupt):
    """An operator interruption with the quiet samples collected so far."""

    def __init__(self, events: Sequence[Mapping[str, Any]]) -> None:
        super().__init__("interrupted")
        self.events = [dict(event) for event in events]



def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def run_command(
    command: Sequence[str],
    *,
    cwd: Optional[Path] = None,
    env: Optional[Mapping[str, str]] = None,
) -> str:
    try:
        result = subprocess.run(
            list(command),
            cwd=cwd,
            env=None if env is None else dict(env),
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError as error:
        raise BenchError(
            f"command failed to start ({' '.join(command)}): {error}"
        ) from error
    if result.returncode != 0:
        detail = result.stderr.strip() or result.stdout.strip() or "no diagnostic"
        raise BenchError(f"command failed ({' '.join(command)}): {detail}")
    return result.stdout.strip()


def select_ci_run(runs: Sequence[Mapping[str, Any]], sha: str) -> Mapping[str, Any]:
    exact = [run for run in runs if run.get("headSha") == sha]
    if not exact:
        raise BenchError(f"no CI run found for exact commit {sha}")
    successful = [
        run
        for run in exact
        if run.get("status") == "completed" and run.get("conclusion") == "success"
    ]
    if not successful:
        raise BenchError(f"exact commit {sha} has no completed successful CI run")
    newest_time = max(str(run.get("createdAt", "")) for run in successful)
    newest = [run for run in successful if str(run.get("createdAt", "")) == newest_time]
    if len(newest) != 1:
        raise BenchError(f"ambiguous successful CI runs for exact commit {sha}")
    return newest[0]


def wait_for_quiet(
    load_average: Callable[[], float],
    sleep: Callable[[float], None],
    monotonic: Callable[[], float],
    *,
    threshold: float,
    quiet_seconds: float,
    sample_interval: float,
    max_wait_seconds: Optional[float] = None,
) -> List[Dict[str, Any]]:
    if threshold <= 0:
        raise BenchError("load threshold must be positive")
    if quiet_seconds < 0 or sample_interval <= 0:
        raise BenchError("quiet seconds must be nonnegative and sample interval positive")

    first = monotonic()
    if quiet_seconds == 0:
        return [
            {
                "monotonic_seconds": first,
                "load_1m": load_average(),
                "elapsed_quiet_seconds": 0.0,
                "reset": False,
                "bypassed": True,
            }
        ]

    quiet_start: Optional[float] = None
    events: List[Dict[str, Any]] = []
    while True:
        try:
            now = monotonic()
            if max_wait_seconds is not None and now - first > max_wait_seconds:
                raise QuietWindowTimeout(
                    f"host did not remain below load {threshold} for {quiet_seconds}s "
                    f"within {max_wait_seconds}s",
                    events,
                )
            load = float(load_average())
            reset = load >= threshold and quiet_start is not None
            if load < threshold:
                if quiet_start is None:
                    quiet_start = now
                elapsed = now - quiet_start
            else:
                quiet_start = None
                elapsed = 0.0
            events.append(
                {
                    "monotonic_seconds": now,
                    "load_1m": load,
                    "elapsed_quiet_seconds": elapsed,
                    "reset": reset,
                    "bypassed": False,
                }
            )
            if quiet_start is not None and elapsed >= quiet_seconds:
                return events
            sleep(sample_interval)
        except KeyboardInterrupt as error:
            raise QuietWindowInterrupted(events) from error


def docker_run_command(
    *,
    image_id: str,
    run_dir: Path,
    git_sha: str,
    host_cpu: str,
    host_ram_bytes: int,
) -> List[str]:
    return [
        "docker",
        "run",
        "--rm",
        "--platform",
        PLATFORM,
        "--network",
        "none",
        "--read-only",
        "--tmpfs",
        "/tmp:rw,noexec,nosuid,size=256m",
        "--mount",
        f"type=bind,src={run_dir.resolve()},dst=/out",
        "-e",
        f"LARA_BENCH_GIT_REV={git_sha}",
        "-e",
        f"LARA_BENCH_HOST_CPU={host_cpu}",
        "-e",
        f"LARA_BENCH_HOST_RAM_BYTES={host_ram_bytes}",
        image_id,
    ]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_outputs(run_dir: Path, *, expected_git_rev: str) -> Dict[str, str]:
    missing = [name for name in REQUIRED_OUTPUTS if not (run_dir / name).is_file()]
    if missing:
        raise BenchError("missing benchmark output: " + ", ".join(missing))
    try:
        raw = json.loads((run_dir / "bench.json").read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise BenchError(f"invalid benchmark JSON: {error}") from error
    if not isinstance(raw, dict) or not isinstance(raw.get("environment"), dict):
        raise BenchError("invalid benchmark JSON: missing environment object")
    environment = raw["environment"]
    observed_git_rev = environment.get("git_rev")
    if observed_git_rev != expected_git_rev:
        raise BenchError(
            f"benchmark revision {observed_git_rev!r} does not match checkout "
            f"{expected_git_rev}"
        )
    if not isinstance(raw.get("units"), list):
        raise BenchError("invalid benchmark JSON: missing units array")
    return {name: sha256_file(run_dir / name) for name in REQUIRED_OUTPUTS}


def write_json_atomic(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    payload = json.dumps(value, indent=2, sort_keys=True) + "\n"
    with temporary.open("w", encoding="utf-8", newline="\n") as handle:
        handle.write(payload)
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)
    directory = os.open(str(path.parent), os.O_RDONLY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def command_json(command: Sequence[str], *, cwd: Path) -> Any:
    raw = run_command(command, cwd=cwd)
    try:
        return json.loads(raw)
    except json.JSONDecodeError as error:
        raise BenchError(f"command returned invalid JSON ({' '.join(command)}): {error}") from error


def require_clean_tree(root: Path) -> str:
    status = run_command(
        ["git", "status", "--porcelain", "--untracked-files=all"],
        cwd=root,
    )
    if status:
        raise BenchError("Git tree is not clean; commit or remove every change before measuring")
    return run_command(["git", "rev-parse", "HEAD"], cwd=root)


def exact_ci(root: Path, sha: str) -> Dict[str, Any]:
    repo_data = command_json(["gh", "repo", "view", "--json", "nameWithOwner"], cwd=root)
    repository = repo_data.get("nameWithOwner")
    if not isinstance(repository, str) or not repository:
        raise BenchError("gh repo view did not return nameWithOwner")
    runs = command_json(
        [
            "gh",
            "run",
            "list",
            "--commit",
            sha,
            "--workflow",
            WORKFLOW,
            "--limit",
            "20",
            "--json",
            "databaseId,headSha,status,conclusion,event,createdAt,startedAt,updatedAt,url",
        ],
        cwd=root,
    )
    if not isinstance(runs, list):
        raise BenchError("gh run list did not return an array")
    selected = dict(select_ci_run(runs, sha))
    jobs_data = command_json(
        [
            "gh",
            "api",
            f"repos/{repository}/actions/runs/{selected['databaseId']}/jobs?per_page=100",
        ],
        cwd=root,
    )
    jobs = jobs_data.get("jobs") if isinstance(jobs_data, dict) else None
    if not isinstance(jobs, list):
        raise BenchError("GitHub jobs response did not contain a jobs array")
    selected["jobs"] = [
        {
            "name": job.get("name"),
            "status": job.get("status"),
            "conclusion": job.get("conclusion"),
            "started_at": job.get("started_at"),
            "completed_at": job.get("completed_at"),
            "runner_name": job.get("runner_name"),
            "runner_group_name": job.get("runner_group_name"),
            "labels": job.get("labels"),
        }
        for job in jobs
    ]
    selected["repository"] = repository
    selected["fetched_at"] = utc_now()
    return selected


def host_metadata(root: Path) -> Dict[str, Any]:
    cpu = run_command(["sysctl", "-n", "machdep.cpu.brand_string"], cwd=root)
    ram_raw = run_command(["sysctl", "-n", "hw.memsize"], cwd=root)
    try:
        ram = int(ram_raw)
    except ValueError as error:
        raise BenchError(f"sysctl hw.memsize returned {ram_raw!r}") from error
    return {
        "cpu": cpu,
        "ram_bytes": ram,
        "system": platform.system(),
        "release": platform.release(),
        "machine": platform.machine(),
        "platform": platform.platform(),
    }


def compact_docker_metadata(
    version: Mapping[str, Any],
    info: Mapping[str, Any],
) -> Dict[str, Any]:
    version_keys = ("Version", "ApiVersion", "GitCommit", "GoVersion", "Os", "Arch")
    engine_keys = (
        "Architecture",
        "OSType",
        "NCPU",
        "MemTotal",
        "ServerVersion",
        "OperatingSystem",
        "KernelVersion",
        "CgroupVersion",
        "Driver",
    )
    client = version.get("Client")
    server = version.get("Server")
    return {
        "client": {
            key: client.get(key)
            for key in version_keys
            if isinstance(client, dict) and key in client
        },
        "server": {
            key: server.get(key)
            for key in version_keys
            if isinstance(server, dict) and key in server
        },
        "engine": {key: info.get(key) for key in engine_keys if key in info},
    }


def docker_metadata(root: Path) -> Dict[str, Any]:
    version = command_json(["docker", "version", "--format", "{{json .}}"], cwd=root)
    info = command_json(["docker", "info", "--format", "{{json .}}"], cwd=root)
    architecture = info.get("Architecture") if isinstance(info, dict) else None
    operating_system = info.get("OSType") if isinstance(info, dict) else None
    if architecture not in ("arm64", "aarch64") or operating_system != "linux":
        raise BenchError(
            f"Docker engine must be linux/arm64, got {operating_system}/{architecture}"
        )
    return compact_docker_metadata(version, info)


def image_metadata(root: Path, image: str, expected_git_rev: str) -> Dict[str, Any]:
    inspected = command_json(["docker", "image", "inspect", image], cwd=root)
    if not isinstance(inspected, list) or len(inspected) != 1:
        raise BenchError(f"docker image inspect returned no unique image for {image}")
    image_data = inspected[0]
    if image_data.get("Architecture") != "arm64":
        raise BenchError(f"benchmark image is not arm64: {image_data.get('Architecture')}")
    config = image_data.get("Config")
    labels = config.get("Labels") if isinstance(config, dict) else None
    revision = (
        labels.get("org.opencontainers.image.revision")
        if isinstance(labels, dict)
        else None
    )
    if revision != expected_git_rev:
        raise BenchError(
            f"image source revision {revision!r} does not match checkout "
            f"{expected_git_rev}"
        )
    image_id = image_data.get("Id")
    if not isinstance(image_id, str) or not image_id.startswith("sha256:"):
        raise BenchError(f"benchmark image has no immutable image ID: {image_id!r}")
    return {
        "tag": image,
        "id": image_id,
        "source_revision": revision,
        "architecture": image_data.get("Architecture"),
        "os": image_data.get("Os"),
        "created": image_data.get("Created"),
        "entrypoint": config.get("Entrypoint") if isinstance(config, dict) else None,
        "user": config.get("User") if isinstance(config, dict) else None,
    }


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--skip-ci", action="store_true", help="smoke only; record that CI was not checked")
    parser.add_argument("--quiet-seconds", type=float, default=120.0)
    parser.add_argument("--load-threshold", type=float, default=0.5)
    parser.add_argument("--sample-interval", type=float, default=5.0)
    parser.add_argument("--max-wait-seconds", type=float, default=3600.0)
    parser.add_argument("--image", help="image tag; defaults to lara-bench:<short SHA>")
    parser.add_argument("--no-build", action="store_true", help="reuse the named image")
    parser.add_argument("--output-root", type=Path, default=Path("measurements/bench-runs"))
    return parser.parse_args(argv)


def run_publication(args: argparse.Namespace) -> Path:
    if args.no_build and not args.skip_ci:
        raise BenchError("--no-build requires --skip-ci; reused images are smoke-only")
    root = Path(run_command(["git", "rev-parse", "--show-toplevel"])).resolve()
    if platform.system() != "Darwin" or platform.machine() != "arm64":
        raise BenchError("publication runner requires a Darwin/arm64 physical host")
    sha = require_clean_tree(root)
    host = host_metadata(root)
    docker = docker_metadata(root)
    ci = {"skipped": True, "reason": "--skip-ci"} if args.skip_ci else exact_ci(root, sha)
    image = args.image or f"lara-bench:{sha[:12]}"
    build_command = [
        "docker",
        "build",
        "--platform",
        PLATFORM,
        "--build-arg",
        f"LARA_GIT_REV={sha}",
        "-f",
        str(DOCKERFILE),
        "-t",
        image,
        ".",
    ]
    if not args.no_build:
        run_command(build_command, cwd=root)
    image_info = image_metadata(root, image, sha)

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run_dir = (root / args.output_root / f"{stamp}-{sha[:12]}").resolve()
    try:
        run_dir.mkdir(parents=True, exist_ok=False)
    except OSError as error:
        raise BenchError(
            f"cannot create benchmark run directory {run_dir}: {error}"
        ) from error
    provenance_path = run_dir / "provenance.json"
    provenance: Dict[str, Any] = {
        "schema": "lara-bench-provenance@1",
        "status": "preparing",
        "stage": "quiet-window",
        "created_at": utc_now(),
        "source": {"git_rev": sha, "clean": True},
        "ci": ci,
        "host": host,
        "docker": docker,
        "image": image_info,
        "build": {"skipped": bool(args.no_build), "command": build_command},
        "quiet_window": {
            "threshold_1m": args.load_threshold,
            "required_seconds": args.quiet_seconds,
            "sample_interval_seconds": args.sample_interval,
            "max_wait_seconds": args.max_wait_seconds,
            "events": [],
        },
    }
    try:
        write_json_atomic(provenance_path, provenance)
    except OSError as error:
        raise BenchError(
            f"cannot initialize benchmark provenance {provenance_path}: {error}"
        ) from error

    try:
        events = wait_for_quiet(
            lambda: os.getloadavg()[0],
            time.sleep,
            time.monotonic,
            threshold=args.load_threshold,
            quiet_seconds=args.quiet_seconds,
            sample_interval=args.sample_interval,
            max_wait_seconds=args.max_wait_seconds,
        )
        provenance["quiet_window"]["events"] = events
        provenance["quiet_window"]["completed_at"] = utc_now()
        command = docker_run_command(
            image_id=str(image_info["id"]),
            run_dir=run_dir,
            git_sha=sha,
            host_cpu=str(host["cpu"]),
            host_ram_bytes=int(host["ram_bytes"]),
        )
        provenance["stage"] = "benchmark"
        provenance["benchmark"] = {"command": command, "started_at": utc_now()}
        write_json_atomic(provenance_path, provenance)
        run_command(command, cwd=root)
        provenance["benchmark"]["completed_at"] = utc_now()
        provenance["outputs"] = validate_outputs(run_dir, expected_git_rev=sha)
        provenance["status"] = "success"
        provenance["stage"] = "complete"
        provenance["completed_at"] = utc_now()
        write_json_atomic(provenance_path, provenance)
        return run_dir
    except (Exception, KeyboardInterrupt) as error:
        if isinstance(error, (QuietWindowTimeout, QuietWindowInterrupted)):
            provenance["quiet_window"]["events"] = error.events
        provenance["status"] = "failed"
        provenance["failed_stage"] = provenance.get("stage")
        provenance["error"] = (
            "interrupted" if isinstance(error, KeyboardInterrupt) else str(error)
        )
        provenance["completed_at"] = utc_now()
        write_json_atomic(provenance_path, provenance)
        if isinstance(error, KeyboardInterrupt):
            raise
        if isinstance(error, BenchError):
            raise
        raise BenchError(str(error)) from error


def main(argv: Optional[Sequence[str]] = None) -> int:
    try:
        run_dir = run_publication(parse_args(argv))
    except BenchError as error:
        print(f"bench-container: {error}", file=sys.stderr)
        return 1
    except KeyboardInterrupt:
        print("bench-container: interrupted", file=sys.stderr)
        return 130
    print(run_dir)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
