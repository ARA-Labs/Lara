#!/usr/bin/env python3
"""Draw the stratified M0 annotation sample (docs/corpus-map.md §4 process).

Joins claims-index.tsv with claim-types.tsv and draws SAMPLE_SIZE claims
stratified by claim type:

- Quotas: largest-remainder proportional allocation over the six types,
  then a floor of MIN_PER_TYPE per type (taken from the largest strata).
- Within a stratum, benchmark groups are exhausted in priority order
  paperbench > extra > rebench > speedrun ("drawing first from paperbench");
  within a group, claims are taken round-robin across artifacts so no single
  artifact dominates a stratum.
- DOUBLE_FRACTION of each stratum (min 1) is flagged for double annotation.

Everything is seeded (SEED) — reruns are byte-identical. Run from repo root:

    python3 m0/draw_sample.py

Output: m0/sample.tsv
"""

import csv
import random
from collections import defaultdict
from pathlib import Path

M0 = Path(__file__).resolve().parent

SEED = 42
SAMPLE_SIZE = 60
MIN_PER_TYPE = 5
DOUBLE_FRACTION = 0.30
GROUP_PRIORITY = {"paperbench": 0, "extra": 1, "rebench": 2, "speedrun": 3}
TYPES = ["descriptive", "comparative", "causal", "generalization",
         "negative-result", "implementation-behavioral"]


def read_tsv(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


def allocate(counts: dict[str, int]) -> dict[str, int]:
    """Largest-remainder proportional quotas, then enforce MIN_PER_TYPE."""
    total = sum(counts.values())
    exact = {t: SAMPLE_SIZE * counts[t] / total for t in TYPES}
    quota = {t: int(exact[t]) for t in TYPES}
    for t in sorted(TYPES, key=lambda t: exact[t] - quota[t], reverse=True):
        if sum(quota.values()) == SAMPLE_SIZE:
            break
        quota[t] += 1
    for t in TYPES:  # floor, funded by the largest strata
        while quota[t] < min(MIN_PER_TYPE, counts[t]):
            donor = max(TYPES, key=lambda d: quota[d])
            quota[donor] -= 1
            quota[t] += 1
    return quota


def draw_stratum(rng: random.Random, pool: list[dict], quota: int) -> list[dict]:
    """Exhaust groups in priority order; round-robin over artifacts within."""
    picked: list[dict] = []
    for prio in sorted({GROUP_PRIORITY[c["group"]] for c in pool}):
        if len(picked) >= quota:
            break
        tier = [c for c in pool if GROUP_PRIORITY[c["group"]] == prio]
        by_artifact = defaultdict(list)
        for c in tier:
            by_artifact[c["artifact"]].append(c)
        artifacts = sorted(by_artifact)
        rng.shuffle(artifacts)
        for a in artifacts:
            rng.shuffle(by_artifact[a])
        while len(picked) < quota and any(by_artifact[a] for a in artifacts):
            for a in artifacts:
                if len(picked) >= quota:
                    break
                if by_artifact[a]:
                    picked.append(by_artifact[a].pop())
    return picked


def main() -> None:
    claims = {(c["artifact"], c["claim_id"]): c
              for c in read_tsv(M0 / "claims-index.tsv")}
    typed = read_tsv(M0 / "claim-types.tsv")
    assert len(typed) == len(claims), "typing table out of sync with index"

    pools: dict[str, list[dict]] = {t: [] for t in TYPES}
    for row in typed:
        key = (row["artifact"], row["claim_id"])
        merged = {**claims[key], "claim_type": row["claim_type"]}
        pools[row["claim_type"]].append(merged)
    # deterministic base order before any shuffling
    for t in TYPES:
        pools[t].sort(key=lambda c: (c["artifact"], c["claim_id"]))

    quota = allocate({t: len(pools[t]) for t in TYPES})
    rng = random.Random(SEED)
    sample: list[dict] = []
    for t in TYPES:
        stratum = draw_stratum(rng, pools[t], quota[t])
        n_double = max(1, round(DOUBLE_FRACTION * len(stratum)))
        doubles = set(id(c) for c in rng.sample(stratum, n_double))
        for c in stratum:
            c["double_annotate"] = "yes" if id(c) in doubles else "no"
        sample.extend(stratum)

    sample.sort(key=lambda c: (GROUP_PRIORITY[c["group"]], c["artifact"],
                               c["claim_id"]))
    columns = ["group", "artifact", "claim_id", "claim_type",
               "double_annotate", "title"]
    with (M0 / "sample.tsv").open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=columns, delimiter="\t",
                                extrasaction="ignore")
        writer.writeheader()
        writer.writerows(sample)

    n_double = sum(1 for c in sample if c["double_annotate"] == "yes")
    print(f"sample.tsv: {len(sample)} claims "
          f"({n_double} double-annotate, {100 * n_double // len(sample)}%)")
    for t in TYPES:
        n = sum(1 for c in sample if c["claim_type"] == t)
        print(f"  {t:28s} {n:3d} / pool {len(pools[t])}")


if __name__ == "__main__":
    main()
