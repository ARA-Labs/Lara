#!/usr/bin/env python3
"""Capture one bounded inquiry run, or replay saved evidence without processes.

Native, Lean and consumer binaries must already be built. All original inputs,
selected binary bytes, raw streams, process exits and timings are retained.
An existing output directory is always refused. Replay executes nothing.
"""
from __future__ import annotations

import argparse
import datetime as dt
import gzip
import hashlib
import io
import locale
import os
import platform
import resource
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path

from inquiry_evaluation_manifest import (
    ROOT, checked, digest, git, json_bytes, load_suite, read_json,
    repository_preflight, require, safe_path,
)
from inquiry_evaluation_report import DRIVERS, report_bytes, score_case, summary

SCHEMA = "inquiry-p8-run"
SCHEMA_VERSION = 1
RUNNER_FILES = ("inquiry-evaluate.py", "inquiry_evaluation_manifest.py", "inquiry_evaluation_report.py",
                "evidence_measured.py")
MAX_ARCHIVE_BYTES = 100 * 1024 * 1024


class AggregateDeadline(OSError):
    """Evidence publication also cannot turn a late run into completion."""


def write_atomic(path, data, *, replace=False):
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(prefix="." + path.name + ".", dir=path.parent, delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
            stream.flush()
            os.fsync(stream.fileno())
        if replace:
            os.replace(temporary, path)
        else:
            # Hard-link publication preserves exclusive-create semantics.
            os.link(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def write_new(path, data):
    write_atomic(path, data)


def artifact(directory, relative, data, inventory):
    write_new(safe_path(directory, relative), data)
    inventory[relative] = digest(data)


def executable(value):
    selected = shutil.which(value) if not Path(value).is_absolute() else value
    require(selected is not None, f"executable not found: {value}")
    path = Path(selected).resolve(strict=True)
    require(path.is_file() and os.access(path, os.X_OK), f"not an executable file: {path}")
    # Read before driver startup: missing/unreadable binaries are preflight failures.
    return path, path.read_bytes()


def tool_version(command, *, cwd=ROOT):
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True, timeout=10)
        return {"command": command, "cwd": str(cwd), "exit_code": result.returncode,
                "stdout": result.stdout.decode("utf-8", errors="replace").strip(),
                "stderr": result.stderr.decode("utf-8", errors="replace").strip()}
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {"command": command, "unavailable": str(exc)}


def machine_metadata():
    meminfo = Path("/proc/meminfo")
    cpuinfo = Path("/proc/cpuinfo")
    return {"os": platform.platform(), "architecture": platform.machine(),
            "python": platform.python_version(), "locale": locale.setlocale(locale.LC_ALL),
            "locale_environment": {key: os.environ.get(key) for key in ("LC_ALL", "LANG", "LC_CTYPE")},
            "logical_cpus": os.cpu_count(),
            "cpuinfo": cpuinfo.read_text() if cpuinfo.is_file() else None,
            "memory": meminfo.read_text() if meminfo.is_file() else None,
            "process_resource_limits": {name: list(resource.getrlimit(getattr(resource, name)))
                for name in ("RLIMIT_AS", "RLIMIT_DATA", "RLIMIT_CPU", "RLIMIT_NOFILE")},
            "cgroup_limits": {name: (Path("/sys/fs/cgroup") / name).read_text().strip()
                for name in ("memory.max", "cpu.max", "cpuset.cpus.effective")
                if (Path("/sys/fs/cgroup") / name).is_file()},
            "ghc_version": tool_version(["ghc", "--numeric-version"]),
            "lean_version": tool_version(["lean", "--version"], cwd=ROOT / "lean")}


def verify_binary_archive(directory, binary):
    """Stream decompressed identity verification; never execute saved binaries."""
    data = checked(directory, binary["saved_path"], binary["archive_sha256"], {})
    hasher, size = hashlib.sha256(), 0
    with gzip.GzipFile(fileobj=io.BytesIO(data), mode="rb") as stream:
        while chunk := stream.read(1024 * 1024):
            size += len(chunk)
            require(size <= binary["bytes"], "binary archive exceeds recorded original size")
            hasher.update(chunk)
    require(size == binary["bytes"] and hasher.hexdigest() == binary["sha256"],
            "saved original binary identity mismatch")


def invoke(command, directory, stem, deadline, *, timeout=10):
    """Direct process IO; file captures survive timeout, signal and spawn failure.

    The child owns a process group so a timed-out wrapper cannot leave a child
    writing into retained captures. Affinity is inherited from the parent.
    """
    stdout_path = directory / "raw" / f"{stem}.stdout"
    stderr_path = directory / "raw" / f"{stem}.stderr"
    record = {"command": [str(x) for x in command], "stdout_path": stdout_path.relative_to(directory).as_posix(),
              "stderr_path": stderr_path.relative_to(directory).as_posix(), "exit_code": None,
              "signal": None, "timeout": False, "spawn_failure": None, "failure": None,
              "process_started": False,
              "timeout_seconds": min(timeout, max(0.0, deadline - time.monotonic()))}
    child = None
    # Open captures before the measured interval; emission itself is inside it.
    with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
        start = time.monotonic_ns()
        try:
            if record["timeout_seconds"] <= 0:
                record["failure"] = "aggregate-deadline"
            else:
                child = subprocess.Popen(record["command"], cwd=ROOT, stdout=stdout, stderr=stderr,
                                         start_new_session=True)
                record["process_started"] = True
                try:
                    record["exit_code"] = child.wait(timeout=record["timeout_seconds"])
                except subprocess.TimeoutExpired:
                    record["timeout"] = True
                    record["failure"] = ("aggregate-deadline" if record["timeout_seconds"] < timeout else "timeout")
                    os.killpg(child.pid, signal.SIGKILL)
                    record["exit_code"] = child.wait()
                if record["exit_code"] is not None and record["exit_code"] < 0:
                    record["signal"] = -record["exit_code"]
                    record["failure"] = record["failure"] or "signal"
        except OSError as exc:
            record["spawn_failure"] = str(exc)
            record["failure"] = "spawn-failure"
            if child and child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                record["exit_code"] = child.wait()
                record["signal"] = -record["exit_code"] if record["exit_code"] < 0 else None
        except KeyboardInterrupt:
            record["failure"] = "interrupted"
            if child and child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                record["exit_code"] = child.wait()
                record["signal"] = -record["exit_code"] if record["exit_code"] < 0 else None
        except BaseException:
            if child and child.poll() is None:
                os.killpg(child.pid, signal.SIGKILL)
                child.wait()
            raise
        finally:
            record["elapsed_ms"] = (time.monotonic_ns() - start) / 1_000_000
        stdout.flush()
        stderr.flush()
        os.fsync(stdout.fileno())
        os.fsync(stderr.fileno())
    for key, path in (("stdout", stdout_path), ("stderr", stderr_path)):
        data = path.read_bytes()
        record[f"{key}_sha256"] = digest(data)
        record[f"{key}_bytes"] = len(data)
    return record


def capture_inventory(run, record):
    for name in ("stdout", "stderr"):
        run["artifacts"][record[f"{name}_path"]] = record[f"{name}_sha256"]


def order(manifest):
    for position, case in enumerate(manifest["cases"]):
        for driver in (DRIVERS if position % 2 == 0 else tuple(reversed(DRIVERS))):
            yield case, driver


def score(directory, run, manifest, oracles):
    records = {(r["case_id"], r["driver"]): r for r in run["invocations"]}
    results = []
    for case in manifest["cases"]:
        captures = {}
        for driver in DRIVERS:
            record = records.get((case["case_id"], driver))
            if record:
                captures[driver] = (record, (directory / record["stdout_path"]).read_bytes(),
                                    (directory / record["stderr_path"]).read_bytes())
        data = (directory / "evidence" / "suite" / case["input_path"]).read_bytes()
        results.append(score_case(case, oracles[case["case_id"]], data, captures))
    return results, summary(results, manifest, run)


def seal(directory, run, results, report):
    for relative, data in report_bytes(results, report).items():
        artifact(directory, relative, data, run["artifacts"])
    # Captures are exclusive-create files. Only derived reports and status
    # checkpoints may be replaced during explicit incomplete recovery.
    run["deterministic_report_hashes"] = {p: run["artifacts"][p] for p in ("results.jsonl", "summary.json", "summary.tsv")}
    run["sealed"] = True
    run["active_operation"] = None
    publish_status(directory, run)


def publish_status(directory, run):
    data = json_bytes(run)
    write_atomic(directory / "run.json", data, replace=True)
    write_atomic(directory / "run.sha256", (digest(data) + "\n").encode("ascii"), replace=True)


def progress(directory, run, manifest, start):
    invoked = {(r["case_id"], r["driver"]) for r in run["invocations"]}
    run["missing_invocations"] = [{"case_id": c["case_id"], "driver": d}
                                  for c, d in order(manifest) if (c["case_id"], d) not in invoked]
    run["aggregate_elapsed_ms"] = (time.monotonic() - start) * 1000
    publish_status(directory, run)


def recover_reports(directory, run, manifest, oracles, start, exc):
    """One recovery of evidence scoring/writes, with no driver or consumer retry.

    Existing derived report bytes are retained before replacement. Raw captures
    and frozen evidence are never rewritten. A persistent/full-filesystem error
    still leaves the last atomically published incomplete checkpoint available.
    """
    run["completion"] = "INCOMPLETE"
    run["sealed"] = False
    run["stop_reason"] = ("aggregate-deadline" if isinstance(exc, AggregateDeadline) else
                          "interrupted" if isinstance(exc, KeyboardInterrupt) else "evidence-io-failure")
    run["stop_detail"] = str(exc)
    if run.get("active_operation") is not None:
        run["failed_or_interrupted_operation"] = run["active_operation"]
    run["recovery"] = {"driver_retries": 0, "consumer_retries": 0, "prior_report_artifacts": []}
    run["deterministic_report_hashes"] = {}
    progress(directory, run, manifest, start)
    for name in ("results.jsonl", "summary.json", "summary.tsv"):
        path = directory / name
        if path.exists():
            relative = "evidence/recovery/" + name
            artifact(directory, relative, path.read_bytes(), run["artifacts"])
            run["recovery"]["prior_report_artifacts"].append(relative)
        run["artifacts"].pop(name, None)
    results, report = score(directory, run, manifest, oracles)
    report_bytes(results, report)
    run["aggregate_elapsed_ms"] = (time.monotonic() - start) * 1000
    report = summary(results, manifest, run)
    # Replacement is restricted to derived reports inside this fresh run. The
    # pre-recovery bytes above remain immutable and hash-bound in the inventory.
    for relative, data in report_bytes(results, report).items():
        write_atomic(directory / relative, data, replace=True)
        run["artifacts"][relative] = digest(data)
    run["deterministic_report_hashes"] = {p: run["artifacts"][p] for p in ("results.jsonl", "summary.json", "summary.tsv")}
    run["sealed"] = True
    run["active_operation"] = None
    publish_status(directory, run)
    return report


def measure(args):
    out = Path(args.out).absolute()
    require(not out.exists() and not out.is_symlink(), f"output already exists: {out}")
    base, protocol, manifest, oracles, suite_inventory = load_suite(Path(args.manifest))
    input_commit, helper_inventory = repository_preflight(protocol, base, suite_inventory)
    binaries = {name: executable(getattr(args, name)) for name in (*DRIVERS, "consumer")}
    # Lossless binary compression is setup, outside all measurement intervals.
    # mtime=0 and no embedded filename make archives deterministic and portable.
    binary_archives = {name: gzip.compress(data, compresslevel=9, mtime=0)
                       for name, (_, data) in binaries.items()}
    require(all(len(data) <= MAX_ARCHIVE_BYTES for data in binary_archives.values()),
            "compressed binary exceeds the 100 MiB evidence delivery limit")
    metadata = machine_metadata()
    require(hasattr(os, "sched_getaffinity") and hasattr(os, "sched_setaffinity"),
            "one-CPU allocation requires Linux affinity support")
    affinity = os.sched_getaffinity(0)
    require(affinity, "empty CPU affinity allocation")
    selected_cpu = min(affinity)
    original_head = git("rev-parse", "HEAD").decode().strip()
    out.mkdir(parents=True, exist_ok=False)
    (out / "raw").mkdir()
    now = dt.datetime.now(dt.timezone.utc)
    run = {"schema": SCHEMA, "schema_version": SCHEMA_VERSION,
           "run_id": now.strftime("%Y%m%dT%H%M%S.%fZ") + "-" + protocol["code_commit"][:12],
           "started_utc": now.isoformat(), "code_commit": protocol["code_commit"],
           "input_commit": input_commit, "measurement_runner_commit": original_head,
           "measurement_runner_source_sha256": {
               name: digest((ROOT / "scripts" / name).read_bytes()) for name in RUNNER_FILES},
           "manifest_sha256": digest((base / Path(args.manifest).name).read_bytes()),
           "protocol_sha256": suite_inventory["protocol.json"],
           "machine": metadata, "affinity_before": sorted(affinity), "allocated_cpus": [selected_cpu],
           "effective_ceilings": protocol["ceilings"], "budget": protocol["budget"],
           "build_commands": {"native": ["cabal", "build", "exe:lara"],
                              "lean": ["lake", "build", "inquiry-run"],
                              "consumer": read_json(base / "authoring-validation.json")["consumer_build_command"]},
           "builds_executed_by_runner": False, "binaries": {}, "artifacts": {}, "invocations": [],
           "completion": "INCOMPLETE", "stop_reason": None, "aggregate_elapsed_ms": 0,
           "missing_invocations": [], "sealed": False, "active_operation": None,
           "failed_or_interrupted_operation": None,
           "deterministic_report_hashes": {}, "recovery": None}
    # Complete all evidence copies before starting the aggregate measurement.
    for relative, expected in suite_inventory.items():
        data = checked(base, relative, expected, {})
        artifact(out, "evidence/suite/" + relative, data, run["artifacts"])
    for relative, expected in helper_inventory.items():
        data = checked(ROOT, relative, expected, {})
        artifact(out, "evidence/repository/" + relative, data, run["artifacts"])
    for name in RUNNER_FILES:
        artifact(out, "evidence/runner/" + name, (ROOT / "scripts" / name).read_bytes(), run["artifacts"])
    for name, (path, data) in binaries.items():
        relative = "evidence/binaries/" + name + ".gz"
        compressed = binary_archives[name]
        artifact(out, relative, compressed, run["artifacts"])
        (out / relative).chmod(0o444)
        run["binaries"][name] = {"selected_path": str(path), "saved_path": relative,
                                  "sha256": digest(data), "bytes": len(data),
                                  "archive_sha256": digest(compressed), "archive_bytes": len(compressed),
                                  "archive_format": "gzip; mtime=0; no filename; level=9"}
    os.sched_setaffinity(0, {selected_cpu})
    start = time.monotonic()
    deadline = start + protocol["budget"]["aggregate_deadline_seconds"]
    try:
        progress(out, run, manifest, start)
        for case, driver in order(manifest):
            if time.monotonic() >= deadline:
                run["stop_reason"] = "aggregate-deadline"
                break
            source = base / case["input_path"]
            # Check selected bytes again outside each measured driver interval.
            require(digest(source.read_bytes()) == case["input_sha256"], f"input changed after preflight: {source}")
            for name in (driver, "consumer"):
                require(digest(binaries[name][0].read_bytes()) == run["binaries"][name]["sha256"],
                        f"binary changed after preflight: {name}")
            command = [str(binaries[driver][0])]
            if driver == "native":
                command.append("inquiry")
            command.append(str(source))
            run["active_operation"] = {"case_id": case["case_id"], "driver": driver,
                                       "stage": "driver", "command": command}
            progress(out, run, manifest, start)
            record = invoke(command, out, case["case_id"] + "." + driver, deadline)
            record.update(case_id=case["case_id"], driver=driver)
            record["driver_failure"] = record["failure"]
            run["invocations"].append(record)
            capture_inventory(run, record)
            if record["failure"]:
                run["stop_reason"] = record["failure"]
                break
            consumer_command = [str(binaries["consumer"][0]), "consume", "accepted", str(source),
                                str(out / record["stdout_path"])]
            run["active_operation"] = {"case_id": case["case_id"], "driver": driver,
                                       "stage": "consumer", "command": consumer_command}
            progress(out, run, manifest, start)
            consumer = invoke(consumer_command, out,
                              case["case_id"] + "." + driver + ".consumer", deadline)
            # Consumer success includes its documented silence contract.
            consumer["accepted"] = (consumer["exit_code"] == 0 and not consumer["failure"] and
                                     consumer["stdout_bytes"] == consumer["stderr_bytes"] == 0)
            record["consumer"] = consumer
            capture_inventory(run, consumer)
            run["active_operation"] = None
            progress(out, run, manifest, start)
            if not consumer["accepted"]:
                record["failure"] = consumer["failure"] or "consumer-failure"
                run["stop_reason"] = record["failure"]
                break
        else:
            run["completion"] = "COMPLETE"
    except (OSError, ValueError, KeyboardInterrupt) as exc:
        run["stop_reason"] = "interrupted" if isinstance(exc, KeyboardInterrupt) else "evidence-io-or-integrity-failure"
        run["stop_detail"] = str(exc)
        if run["active_operation"] is not None:
            run["failed_or_interrupted_operation"] = run["active_operation"]
    invoked = {(r["case_id"], r["driver"]) for r in run["invocations"]}
    run["missing_invocations"] = [{"case_id": c["case_id"], "driver": d}
                                  for c, d in order(manifest) if (c["case_id"], d) not in invoked]
    # An IO failure between process capture and record attachment may leave
    # streams without a complete invocation record. Preserve those too, and
    # disclose them instead of silently dropping bytes from the evidence set.
    run["unattached_capture_paths"] = []
    try:
        for path in sorted((out / "raw").iterdir()):
            relative = path.relative_to(out).as_posix()
            if relative not in run["artifacts"]:
                run["artifacts"][relative] = digest(path.read_bytes())
                run["unattached_capture_paths"].append(relative)
    except (OSError, KeyboardInterrupt) as exc:
        run["completion"] = "INCOMPLETE"
        run["stop_reason"] = "interrupted" if isinstance(exc, KeyboardInterrupt) else "evidence-io-failure"
        run["stop_detail"] = str(exc)
    # Scoring is part of the aggregate budget. A deadline may not be rescued by
    # fast replay later; the original completion state is retained verbatim.
    try:
        results, report = score(out, run, manifest, oracles)
        # Include report computation and encoding, before adding final elapsed
        # metadata. The saved elapsed value is reused verbatim during replay.
        report_bytes(results, report)
        run["aggregate_elapsed_ms"] = (time.monotonic() - start) * 1000
        if time.monotonic() >= deadline:
            run["completion"] = "INCOMPLETE"
            run["stop_reason"] = "aggregate-deadline"
        report = summary(results, manifest, run)
        seal(out, run, results, report)
        if time.monotonic() >= deadline:
            raise AggregateDeadline("aggregate deadline exhausted during evidence publication")
    except (OSError, KeyboardInterrupt) as exc:
        report = recover_reports(out, run, manifest, oracles, start, exc)
    finally:
        os.sched_setaffinity(0, affinity)
    print(f"{run['completion']}: {'PASS' if report['passed'] else 'FAIL'}: {out}")
    return 0 if report["passed"] else 1


def validate_saved(source, manifest_path):
    """Replay trust checks perform file reads only, including binary identities."""
    raw = (source / "run.json").read_bytes()
    require(digest(raw) == (source / "run.sha256").read_text().strip(), "saved run metadata hash mismatch")
    run = read_json(source / "run.json")
    require(run["schema"] == SCHEMA and run["schema_version"] == SCHEMA_VERSION, "unsupported saved run schema")
    require(run.get("sealed") is True, "saved run is an incomplete checkpoint without sealed deterministic reports")
    base, protocol, manifest, oracles, inventory = load_suite(manifest_path)
    require(run["manifest_sha256"] == digest(manifest_path.read_bytes()) and
            run["protocol_sha256"] == inventory["protocol.json"] and
            run["code_commit"] == protocol["code_commit"] and run["budget"] == protocol["budget"],
            "saved run freeze identity mismatch")
    for relative, expected in run["artifacts"].items():
        checked(source, relative, expected, {})
    for relative, expected in inventory.items():
        require(run["artifacts"].get("evidence/suite/" + relative) == expected,
                f"missing frozen evidence: {relative}")
    recipe = protocol["recipes"]
    helpers = [(recipe["generator_path"], recipe["generator_sha256"]),
               ("evaluation/inquiry-p8/review/independent_finite_audit.py", recipe["independent_audit_tool_sha256"]),
               (recipe["certificate_producer_path"], recipe["certificate_producer_sha256"])]
    quality = read_json(base / "quality-review.json")
    helpers.append((quality["boundary_test_path"], quality["boundary_test_sha256"]))
    for path, expected in helpers:
        require(run["artifacts"].get("evidence/repository/" + path) == expected,
                f"missing frozen helper source: {path}")
    require(set(run["measurement_runner_source_sha256"]) == set(RUNNER_FILES),
            "incomplete measurement runner source identity")
    for name, expected in run["measurement_runner_source_sha256"].items():
        require(run["artifacts"].get("evidence/runner/" + name) == expected,
                f"runner source identity mismatch: {name}")
    for name in (*DRIVERS, "consumer"):
        binary = run["binaries"][name]
        verify_binary_archive(source, binary)
        require(run["artifacts"].get(binary["saved_path"]) == binary["archive_sha256"],
                f"saved binary identity mismatch: {name}")
    planned = [(c["case_id"], d) for c, d in order(manifest)]
    observed = [(r["case_id"], r["driver"]) for r in run["invocations"]]
    require(observed == planned[:len(observed)], "changed invocation sequence or repeated invocation")
    missing = [{"case_id": c, "driver": d} for c, d in planned[len(observed):]]
    require(run["missing_invocations"] == missing, "missing invocation list mismatch")
    require(run["completion"] in ("COMPLETE", "INCOMPLETE"), "invalid completion state")
    require(run["completion"] != "COMPLETE" or not missing, "partial run marked complete")
    for record in run["invocations"]:
        for entry in (record, record.get("consumer")):
            if entry is None:
                continue
            for stream in ("stdout", "stderr"):
                data = checked(source, entry[f"{stream}_path"], entry[f"{stream}_sha256"], {})
                require(len(data) == entry[f"{stream}_bytes"] and
                        run["artifacts"].get(entry[f"{stream}_path"]) == entry[f"{stream}_sha256"],
                        "capture metadata mismatch")
    results, report = score(source, run, manifest, oracles)
    outputs = report_bytes(results, report)
    require({p: digest(data) for p, data in outputs.items()} == run["deterministic_report_hashes"],
            "deterministic replay report mismatch")
    return run, report


def replay(args):
    source, out = Path(args.replay).resolve(), Path(args.out).absolute()
    require(not out.exists() and not out.is_symlink(), f"output already exists: {out}")
    run, report = validate_saved(source, Path(args.manifest).resolve())
    # Validation precedes destination creation; copy original metadata and timing.
    # No executable path is resolved or read, and no subprocess is started here.
    out.mkdir(parents=True, exist_ok=False)
    for relative, expected in run["artifacts"].items():
        artifact(out, relative, checked(source, relative, expected, {}), {})
    write_new(out / "run.json", (source / "run.json").read_bytes())
    write_new(out / "run.sha256", (source / "run.sha256").read_bytes())
    print(f"REPLAY {run['completion']}: {'PASS' if report['passed'] else 'FAIL'}: {out}")
    return 0 if report["passed"] else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", required=True, type=str)
    parser.add_argument("--native")
    parser.add_argument("--lean")
    parser.add_argument("--consumer")
    parser.add_argument("--replay", help="saved run directory; starts no processes")
    parser.add_argument("--out", required=True)
    args = parser.parse_args(argv)
    if args.replay:
        require(not any((args.native, args.lean, args.consumer)), "replay replaces all executable arguments")
        return replay(args)
    require(all((args.native, args.lean, args.consumer)), "measurement requires --native, --lean and --consumer")
    return measure(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"FAIL: inquiry evaluation: {exc}", file=sys.stderr)
        sys.exit(1)
