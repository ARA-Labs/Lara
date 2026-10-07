#!/usr/bin/env python3
"""Validate append-only ARA observation aliases and audited historical references.

The original staging records remain authoritative. Duplicate historical IDs are
not lookup keys: each occurrence needs a fresh canonical alias with an exact
(timestamp, bound_to) selector and a fingerprint of its immutable identity fields.
Qualified historical references are forward records, never edits to the trace.
See docs/ara-observation-identity-decision.md for the consumer contract.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

import yaml


OBSERVATIONS = "ara/staging/observations.yaml"
ALIASES = "ara/staging/observation_aliases.yaml"
IDENTIFIER = re.compile(r"O[0-9]+\Z")
TOKEN = re.compile(r"\bO[0-9]+\b")
PROMOTION_STATE_FIELDS = frozenset({"promoted", "promoted_to", "crystallized_via", "stale"})


class StrictLoader(yaml.SafeLoader):
    """Use the same duplicate-key refusal as the session-index gate."""

    def construct_mapping(self, node, deep=False):
        seen = set()
        for key_node, _ in node.value:
            key = self.construct_object(key_node, deep=deep)
            if key in seen:
                raise yaml.constructor.ConstructorError(
                    "while constructing a mapping", node.start_mark,
                    f"found duplicate key {key!r}", key_node.start_mark,
                )
            seen.add(key)
        return super().construct_mapping(node, deep=deep)


def read_yaml(path: Path) -> dict:
    try:
        document = yaml.load(path.read_text(encoding="utf-8"), Loader=StrictLoader)
    except (OSError, yaml.YAMLError) as exc:
        raise ValueError(f"{path}: cannot read: {exc}") from exc
    if not isinstance(document, dict):
        raise ValueError(f"{path}: must be a mapping")
    return document


def list_field(document: dict, key: str) -> list:
    value = document.get(key)
    if not isinstance(value, list) or any(not isinstance(row, dict) for row in value):
        raise ValueError(f"{key}: must be a list of mappings")
    return value


def record_fingerprint(record: dict) -> str:
    identity = {key: value for key, value in record.items() if key not in PROMOTION_STATE_FIELDS}
    encoded = json.dumps(identity, ensure_ascii=False, sort_keys=True,
                         separators=(",", ":"), default=str).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


class ObservationIndex:
    def __init__(self, effective: dict, ambiguous: set, references: dict):
        self.effective = effective
        self.ambiguous = ambiguous
        self.references = references

    def lookup(self, identifier: str, *, source: str | None = None,
               line: int | None = None) -> dict:
        """Resolve a unique ID, or a pinned historical source line; never guess."""
        if source is not None or line is not None:
            reference = self.references.get((source, line))
            if reference is None:
                raise ValueError(f"unaudited reference: {source}:{line}")
            if reference["kind"] == "aggregate":
                raise ValueError(f"non-lookup aggregate reference: {source}:{line}")
            targets = [binding["canonical_id"] for binding in reference["bindings"]
                       if binding["historical_id"] == identifier]
            if len(targets) != 1:
                raise ValueError(f"ambiguous or missing contextual lookup: {identifier} at {source}:{line}")
            return self.effective[targets[0]]
        if identifier in self.ambiguous:
            raise ValueError(f"ambiguous historical observation ID: {identifier}; use a canonical ID or audited reference")
        if identifier not in self.effective:
            raise ValueError(f"unknown observation ID: {identifier}")
        return self.effective[identifier]


def load_observations(repo_root: Path) -> ObservationIndex:
    """Build the effective index only after every alias and reference validates."""
    repo_root = repo_root.resolve()
    rows = list_field(read_yaml(repo_root / OBSERVATIONS), "observations")
    registry = read_yaml(repo_root / ALIASES)
    if type(registry.get("schema_version")) is not int or registry["schema_version"] != 1:
        raise ValueError("observation aliases: unsupported schema_version")
    aliases = list_field(registry, "aliases")
    reference_rows = list_field(registry, "references")
    groups = defaultdict(list)
    for row in rows:
        identifier = row.get("id")
        if not isinstance(identifier, str) or not IDENTIFIER.fullmatch(identifier):
            raise ValueError(f"invalid observation ID: {identifier!r}")
        groups[identifier].append(row)
    ambiguous = {identifier for identifier, group in groups.items() if len(group) > 1}
    effective = {identifier: group[0] for identifier, group in groups.items() if len(group) == 1}
    registered = set()
    spellings = {}
    for alias in aliases:
        canonical = alias.get("canonical_id")
        historical = alias.get("historical_id")
        if (not isinstance(canonical, str) or not IDENTIFIER.fullmatch(canonical)
                or canonical in groups or canonical in effective):
            raise ValueError(f"invalid or colliding canonical ID: {canonical!r}")
        if not isinstance(historical, str) or historical not in ambiguous:
            raise ValueError(f"alias {canonical}: historical ID is not a duplicate")
        if not isinstance(alias.get("bound_to"), list) or not alias.get("timestamp"):
            raise ValueError(f"alias {canonical}: missing occurrence selector")
        prior_ids = alias.get("prior_ids", [])
        if (not isinstance(prior_ids, list)
                or any(not isinstance(prior, str) or not IDENTIFIER.fullmatch(prior)
                       for prior in prior_ids)):
            raise ValueError(f"alias {canonical}: invalid prior_ids")
        matches = [(index, row) for index, row in enumerate(groups[historical])
                   if str(row.get("timestamp")) == alias["timestamp"]
                   and row.get("bound_to") == alias["bound_to"]]
        if len(matches) != 1:
            raise ValueError(f"alias {canonical}: occurrence selector matches {len(matches)} records")
        index, row = matches[0]
        occurrence = (historical, index)
        if occurrence in registered:
            raise ValueError(f"alias {canonical}: occurrence already registered")
        if record_fingerprint(row) != alias.get("record_sha256"):
            raise ValueError(f"alias {canonical}: record fingerprint mismatch")
        registered.add(occurrence)
        effective[canonical] = row
        spellings[canonical] = {historical, *prior_ids}
    for historical in sorted(ambiguous):
        for index in range(len(groups[historical])):
            if (historical, index) not in registered:
                raise ValueError(f"unregistered duplicate occurrence: {historical} #{index + 1}")

    references = {}
    for reference in reference_rows:
        relative, line = reference.get("path"), reference.get("line")
        if not isinstance(relative, str) or type(line) is not int or line < 1:
            raise ValueError("reference: path and positive line are required")
        path = (repo_root / relative).resolve()
        if (not path.is_relative_to(repo_root / "ara") or Path(relative).is_absolute()
                or path in (repo_root / OBSERVATIONS, repo_root / ALIASES)
                or path.suffix not in (".md", ".yaml", ".yml")):
            raise ValueError(f"reference: invalid artifact path {relative!r}")
        if path.relative_to(repo_root).as_posix() != relative:
            raise ValueError(f"reference: path is not normalized: {relative!r}")
        key = (relative, line)
        if key in references:
            raise ValueError(f"duplicate reference registration: {relative}:{line}")
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except OSError as exc:
            raise ValueError(f"reference: cannot read {relative}: {exc}") from exc
        if line > len(lines):
            raise ValueError(f"reference: missing line {relative}:{line}")
        text = lines[line - 1]
        if hashlib.sha256(text.encode("utf-8")).hexdigest() != reference.get("line_sha256"):
            raise ValueError(f"reference fingerprint mismatch: {relative}:{line}")
        tokens = set(TOKEN.findall(text))
        kind = reference.get("kind")
        if kind not in ("lookup", "aggregate") or not reference.get("reason"):
            raise ValueError(f"reference: invalid kind or missing reason: {relative}:{line}")
        bindings = list_field(reference, "bindings")
        if kind == "aggregate":
            if bindings or not tokens.intersection(ambiguous):
                raise ValueError(f"aggregate reference must be non-lookup: {relative}:{line}")
        else:
            bound_tokens = set()
            for binding in bindings:
                historical, canonical = binding.get("historical_id"), binding.get("canonical_id")
                if (not isinstance(historical, str) or historical not in tokens
                        or not isinstance(canonical, str)
                        or canonical not in effective or canonical in groups):
                    raise ValueError(f"invalid reference binding: {relative}:{line}")
                if historical not in spellings[canonical]:
                    raise ValueError(f"reference occurrence has different historical ID: {relative}:{line}")
                if record_fingerprint(effective[canonical]) != binding.get("record_sha256"):
                    raise ValueError(f"reference occurrence mismatch: {relative}:{line}")
                if historical in bound_tokens:
                    raise ValueError(f"ambiguous reference binding: {relative}:{line}")
                bound_tokens.add(historical)
            if not bindings or not tokens.intersection(ambiguous).issubset(bound_tokens):
                raise ValueError(f"incomplete reference binding: {relative}:{line}")
        references[key] = reference

    # Scan the complete local artifact, not just trace files known at repair time.
    for path in sorted((repo_root / "ara").rglob("*")):
        if (not path.is_file() or path.suffix not in (".md", ".yaml", ".yml")
                or path in (repo_root / OBSERVATIONS, repo_root / ALIASES)):
            continue
        relative = path.relative_to(repo_root).as_posix()
        for line, text in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if ambiguous.intersection(TOKEN.findall(text)) and (relative, line) not in references:
                raise ValueError(f"unaudited historical observation reference: {relative}:{line}")
    return ObservationIndex(effective, ambiguous, references)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--lookup", help="unique canonical observation ID")
    parser.add_argument("--source", help="repository-relative audited historical reference path")
    parser.add_argument("--line", type=int, help="audited historical reference line")
    args = parser.parse_args(argv)
    try:
        if (args.source is not None or args.line is not None) and not args.lookup:
            raise ValueError("--source/--line require --lookup")
        index = load_observations(args.repo_root)
        if args.lookup:
            record = index.lookup(args.lookup, source=args.source, line=args.line)
            print(json.dumps({"lookup_id": args.lookup, "observation": record},
                             ensure_ascii=False, sort_keys=True, default=str))
        else:
            print(f"ARA observations: PASS ({len(index.effective)} unique effective observations, "
                  f"{len(index.ambiguous)} ambiguous historical IDs, "
                  f"{len(index.references)} audited reference lines)")
    except (ValueError, OSError) as exc:
        print(f"ARA observations: FAIL: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
