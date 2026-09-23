#!/usr/bin/env python3
"""Fail when public Lean theorems are absent from AxCheck.lean.

Usage:
    scripts/check-axcheck-coverage.py lean/AxCheck.lean SOURCE.lean [...]

The source scan understands namespace/section/mutual nesting, attribute-prefixed
declarations, and private declarations. It intentionally checks only the source
files named by the caller so milestones can enforce complete coverage without
retroactively changing the audit policy for older modules.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path


ATTRIBUTE_PREFIX = r"(?:@\[[^]]*\]\s*)*"
MODIFIER = r"(?:(?:protected|noncomputable|unsafe|opaque|private)\s+)*"
DECLARATION_RE = re.compile(
    rf"^\s*{ATTRIBUTE_PREFIX}(?P<modifiers>{MODIFIER})(?:theorem|lemma)\s+"
    r"(?P<name>[^\s:{(\[]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([A-Za-z_][\w'.]*(?:\.[A-Za-z_][\w']*)*)")
SECTION_RE = re.compile(r"^\s*(private\s+)?section(?:\s+([A-Za-z_][\w']*))?\s*$")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[A-Za-z_][\w'.]*)?\s*$")
AXCHECK_RE = re.compile(r"^\s*#print\s+axioms\s+([^\s]+)", re.MULTILINE)


@dataclass(frozen=True)
class Block:
    kind: str
    namespace_parts: tuple[str, ...] = ()
    private: bool = False


def strip_comments(text: str) -> str:
    """Remove nested Lean comments while preserving line numbers and strings."""
    output: list[str] = []
    depth = 0
    in_string = False
    escaped = False
    index = 0
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if depth:
            if pair == "/-":
                depth += 1
                output.extend("  ")
                index += 2
            elif pair == "-/":
                depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            output.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            newline = text.find("\n", index)
            if newline == -1:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (newline - index))
            index = newline
            continue
        output.append(char)
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif char == '"':
            in_string = True
        index += 1
    return "".join(output)


def public_theorems(path: Path) -> dict[str, int]:
    blocks: list[Block] = []
    namespace: list[str] = []
    declarations: dict[str, int] = {}
    clean = strip_comments(path.read_text(encoding="utf-8"))

    for line_number, line in enumerate(clean.splitlines(), start=1):
        if match := NAMESPACE_RE.match(line):
            parts = tuple(match.group(1).split("."))
            namespace.extend(parts)
            blocks.append(Block("namespace", parts))
            continue
        if match := SECTION_RE.match(line):
            blocks.append(Block("section", private=bool(match.group(1))))
            continue
        if MUTUAL_RE.match(line):
            blocks.append(Block("mutual"))
            continue
        if END_RE.match(line):
            if blocks:
                block = blocks.pop()
                if block.kind == "namespace":
                    del namespace[-len(block.namespace_parts) :]
            continue
        match = DECLARATION_RE.match(line)
        if not match:
            continue
        modifiers = match.group("modifiers").split()
        if "private" in modifiers or any(block.private for block in blocks):
            continue
        short_name = match.group("name")
        full_name = ".".join([*namespace, short_name])
        declarations[full_name] = line_number

    return declarations


def main(arguments: list[str]) -> int:
    if len(arguments) < 2:
        print(
            "usage: check-axcheck-coverage.py AXCHECK.lean SOURCE.lean [...]",
            file=sys.stderr,
        )
        return 2

    axcheck_path = Path(arguments[0])
    source_paths = [Path(argument) for argument in arguments[1:]]
    audited = set(AXCHECK_RE.findall(strip_comments(axcheck_path.read_text(encoding="utf-8"))))

    missing: list[tuple[str, Path, int]] = []
    count = 0
    for source_path in source_paths:
        declarations = public_theorems(source_path)
        count += len(declarations)
        missing.extend(
            (name, source_path, line)
            for name, line in declarations.items()
            if name not in audited
        )

    if missing:
        print("::error::Public Lean declarations missing from AxCheck.lean:", file=sys.stderr)
        for name, source_path, line in sorted(missing):
            print(f"  {name} ({source_path}:{line})", file=sys.stderr)
        return 1

    print(f"AxCheck coverage passed ({count} declarations).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
