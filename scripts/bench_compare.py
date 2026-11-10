#!/usr/bin/env python3
"""Compare the timed runs of one `make bench-container` batch.

Reads every run directory under the output root whose provenance names the
batch, and reports, for the `check + render, pre-decoded` control row
(`kernel_ns` in bench.json), each run's median across corpus units, the host
load sampled while that run was timed, and the per-unit median and range
across runs. Every run is listed. A run is excluded from the statistics only
for the reasons fixed in advance: its provenance status is not `success`, or
its outputs no longer match the digests the runner recorded.

The table run is chosen by a rule fixed in advance: sort the included runs by
their control-row median (ties broken by directory name) and take the lower
median, index (n - 1) // 2.

Usage: bench_compare.py --batch ID [--output-root DIR] [--json PATH]
"""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence

CONTROL = "kernel_ns"
CONTROL_LABEL = "check + render, pre-decoded"


class CompareError(RuntimeError):
    """A batch that cannot be compared."""


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, json.JSONDecodeError) as error:
        raise CompareError(f"cannot read {path}: {error}") from error


def load_summary(samples: Sequence[Dict[str, Any]]) -> Optional[Dict[str, float]]:
    loads = [float(sample["load_1m"]) for sample in samples]
    if not loads:
        return None
    return {
        "samples": len(loads),
        "min": min(loads),
        "median": statistics.median(loads),
        "max": max(loads),
    }


def batch_runs(output_root: Path, batch_id: str) -> List[Path]:
    if not output_root.is_dir():
        raise CompareError(f"output root {output_root} is not a directory")
    runs = []
    for run_dir in sorted(output_root.iterdir()):
        provenance_path = run_dir / "provenance.json"
        if not provenance_path.is_file():
            continue
        provenance = read_json(provenance_path)
        batch = provenance.get("batch") if isinstance(provenance, dict) else None
        if isinstance(batch, dict) and batch.get("id") == batch_id:
            runs.append(run_dir)
    if not runs:
        raise CompareError(f"no run directory under {output_root} belongs to batch {batch_id}")
    return runs


def describe_run(run_dir: Path) -> Dict[str, Any]:
    provenance = read_json(run_dir / "provenance.json")
    benchmark = provenance.get("benchmark") or {}
    record: Dict[str, Any] = {
        "run": run_dir.name,
        "index": (provenance.get("batch") or {}).get("index"),
        "git_rev": (provenance.get("source") or {}).get("git_rev"),
        "image": (provenance.get("image") or {}).get("id"),
        "cpuset": (provenance.get("cpuset") or {}).get("requested"),
        "status": provenance.get("status"),
        "load_during_run": load_summary(benchmark.get("load_samples") or []),
        "included": False,
        "exclusion": None,
    }
    if provenance.get("status") != "success":
        record["exclusion"] = f"status {provenance.get('status')}: {provenance.get('error')}"
        return record
    recorded = provenance.get("outputs")
    if not isinstance(recorded, dict) or not recorded:
        record["exclusion"] = "no recorded output digests"
        return record
    for name, digest in recorded.items():
        path = run_dir / name
        if not path.is_file() or sha256_file(path) != digest:
            raise CompareError(
                f"{run_dir.name}: {name} does not match the digest the runner recorded"
            )
    bench = read_json(run_dir / "bench.json")
    units = bench.get("units")
    if not isinstance(units, list) or not units:
        raise CompareError(f"{run_dir.name}: bench.json has no units")
    record["units"] = {str(unit["base"]): int(unit[CONTROL]) for unit in units}
    record["control_median_ns"] = statistics.median(record["units"].values())
    record["included"] = True
    return record


def compare(output_root: Path, batch_id: str) -> Dict[str, Any]:
    runs = [describe_run(run_dir) for run_dir in batch_runs(output_root, batch_id)]
    included = [run for run in runs if run["included"]]
    if not included:
        raise CompareError(f"batch {batch_id} has no successful run")
    revisions = {run["git_rev"] for run in included}
    images = {run["image"] for run in included}
    if len(revisions) != 1 or len(images) != 1:
        raise CompareError(f"batch {batch_id} mixes revisions {revisions} or images {images}")
    unit_sets = {tuple(sorted(run["units"])) for run in included}
    if len(unit_sets) != 1:
        raise CompareError(f"batch {batch_id} runs measured different unit sets")
    bases = sorted(included[0]["units"])
    per_unit = []
    for base in bases:
        values = [run["units"][base] for run in included]
        median = statistics.median(values)
        per_unit.append(
            {
                "base": base,
                "median_ns": median,
                "min_ns": min(values),
                "max_ns": max(values),
                "range_pct": 100.0 * (max(values) - min(values)) / median,
            }
        )
    medians = [run["control_median_ns"] for run in included]
    ordered = sorted(included, key=lambda run: (run["control_median_ns"], run["run"]))
    table_run = ordered[(len(ordered) - 1) // 2]["run"]
    batch_median = statistics.median(medians)
    for run in runs:
        run.pop("units", None)
    return {
        "batch": batch_id,
        "control_row": CONTROL_LABEL,
        "git_rev": revisions.pop(),
        "image": images.pop(),
        "runs": runs,
        "included_runs": len(included),
        "control_median_ns": {
            "median": batch_median,
            "min": min(medians),
            "max": max(medians),
            "range_pct": 100.0 * (max(medians) - min(medians)) / batch_median,
        },
        "per_unit_range_pct": {
            "median": statistics.median(unit["range_pct"] for unit in per_unit),
            "max": max(unit["range_pct"] for unit in per_unit),
        },
        "per_unit": per_unit,
        "table_run": table_run,
    }


def us(ns: float) -> str:
    return f"{ns / 1000:.1f}"


def render_markdown(result: Dict[str, Any]) -> str:
    lines = [
        f"Batch `{result['batch']}` at `{result['git_rev'][:12]}`, image `{result['image']}`.",
        f"Control row: {result['control_row']} (µs, median over corpus units).",
        "",
        "| Run | Pinned CPUs | Status | Control median (µs) | Load during run (min / median / max) |",
        "| --- | --- | --- | ---: | --- |",
    ]
    for run in result["runs"]:
        load = run["load_during_run"]
        load_text = (
            "-" if load is None else f"{load['min']:.2f} / {load['median']:.2f} / {load['max']:.2f}"
        )
        status = "included" if run["included"] else f"excluded: {run['exclusion']}"
        control = us(run["control_median_ns"]) if run["included"] else "-"
        marker = " (table)" if run["run"] == result["table_run"] else ""
        lines.append(
            f"| `{run['run']}`{marker} | {run['cpuset'] or '-'} | {status} | {control} | {load_text} |"
        )
    summary = result["control_median_ns"]
    spread = result["per_unit_range_pct"]
    lines += [
        "",
        f"Across {result['included_runs']} included runs the control-row median is "
        f"{us(summary['median'])} µs (range {us(summary['min'])} to {us(summary['max'])} µs, "
        f"{summary['range_pct']:.1f}% of the median). Per unit, the range across runs is "
        f"{spread['median']:.1f}% of the unit's median at the median unit and "
        f"{spread['max']:.1f}% at most.",
    ]
    return "\n".join(lines) + "\n"


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--batch", required=True, help="batch id recorded in provenance.json")
    parser.add_argument("--output-root", type=Path, default=Path("measurements/bench-runs"))
    parser.add_argument("--json", type=Path, help="also write the full comparison as JSON")
    args = parser.parse_args(argv)
    try:
        result = compare(args.output_root, args.batch)
    except CompareError as error:
        print(f"bench-compare: {error}", file=sys.stderr)
        return 1
    if args.json is not None:
        args.json.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    sys.stdout.write(render_markdown(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
