#!/usr/bin/env python3
"""elaborate.py — the untrusted M4b elaborator (spec §11; bundles/README.md §4).

Invocation:

    uv run --no-project elaborator/elaborate.py <bundle-dir>

Reads `<bundle-dir>/source.yaml` (ara-mini-trace@1), loads the trusted policy
referenced by id (`meta.policy`) READ-ONLY from the canonical repo location
`examples/E1/<policy-id>.policy.lara`, performs the six §11 lowering tasks per
the binding derivation contract (bundles/README.md §4), and writes three bundle
artifacts TRANSACTIONALLY (T9): the byte-for-byte policy copy
`<policy-id>.policy.lara`, `emitted.lara`, and `provenance.json`.

Trust boundary: this script is outside the TCB. It never defines policy rules,
schemas, or backends; it parses the trusted policy to SELECT and INSTANTIATE by
premise/conclusion shape and references every trusted input by id.

Exit codes: 0 = success; 2 = malformed source (6A) or trusted-input/IO failure.
On ANY failure the run emits no `.lara` and leaves no partial or stale bundle
artifacts (the three owned files are removed).

Determinism (D3): every output byte is a pure function of `source.yaml` and the
trusted policy — no timestamps, no absolute paths, no randomness.
"""

# /// script
# requires-python = ">=3.12,<3.13"
# dependencies = ["pyyaml==6.0.2"]
# ///

from __future__ import annotations

import json
import os
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass, field

import yaml

# --------------------------------------------------------------------------
# Constants (format contract, not policy content)
# --------------------------------------------------------------------------

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
POLICY_REL = os.path.join("examples", "E1")  # README §4.0 pins the canonical copy

SOURCE_FORMAT = "ara-mini-trace@1"
PROVENANCE_FORMAT = "lara-elaborator-provenance@1"

NODE_TYPES = {"question", "claim", "experiment", "dead_end"}
TOPICS = {
    "positive-effect-report",
    "randomization",
    "power",
    "generalization",
    "distribution-shift",
    "generalization-failure",
}
RECORDED_KINDS = {"run-output", "paper-text"}

ID_RE = re.compile(r"[a-z][a-z0-9_]*\Z")
REF_RE = re.compile(r"[^\s\[\],]+\Z")  # refs are emitted bare inside [ … ]

# Verbatim provenance strings pinned by README §7.
HOLE_REASON = (
    "no evidence cell answers the question; the frozen frontend rejects surface "
    "holes (PEIncompleteArgument), so the incomplete argument is not emitted and "
    "the claim's complete support is empty"
)
NONE_NOTE = "documents unmet questions; routed to task-4 hole, never an attack (spec §7)"
TASK5_ENTRY = {
    "status": "not-applicable",
    "reason": "defeasible source; Lara.Syntax forces assurance = none (T1); "
    "no strict instance is certified",
}


class ElabError(Exception):
    """Fatal elaboration error; message is printed located on stderr, exit 2."""


# --------------------------------------------------------------------------
# Propositions: tiny term machinery for parsing/matching/rendering
# --------------------------------------------------------------------------
# A proposition is ("atom", name) or ("prop", head, [args]). In policy patterns
# an atom whose name starts uppercase is a VARIABLE (M, Q, D, Exp); everything
# else is a constant. Derived (concrete) propositions contain no variables.


def split_top(s: str) -> list[str]:
    """Split a comma-separated term list at paren depth 0."""
    parts, depth, start = [], 0, 0
    for i, ch in enumerate(s):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == "," and depth == 0:
            parts.append(s[start:i])
            start = i + 1
    parts.append(s[start:])
    return [p.strip() for p in parts if p.strip()]


def parse_prop_prefix(s: str, loc: str) -> tuple[tuple, int]:
    """Parse one proposition at the start of s; return (prop, end index)."""
    m = re.match(r"\s*([A-Za-z][A-Za-z0-9_]*)", s)
    if not m:
        raise ElabError(f"{loc}: expected a proposition, got: {s!r}")
    head = m.group(1)
    i = m.end()
    if i >= len(s) or s[i] != "(":
        return ("atom", head), i
    depth, start = 0, i
    while i < len(s):
        if s[i] == "(":
            depth += 1
        elif s[i] == ")":
            depth -= 1
            if depth == 0:
                inner = s[start + 1 : i]
                args = [parse_prop(p, loc) for p in split_top(inner)]
                return ("prop", head, args), i + 1
        i += 1
    raise ElabError(f"{loc}: unbalanced parentheses in proposition: {s!r}")


def parse_prop(s: str, loc: str) -> tuple:
    prop, end = parse_prop_prefix(s, loc)
    if s[end:].strip():
        raise ElabError(f"{loc}: trailing text after proposition: {s!r}")
    return prop


def render_prop(p: tuple) -> str:
    if p[0] == "atom":
        return p[1]
    return f"{p[1]}({', '.join(render_prop(a) for a in p[2])})"


def prop_vars(p: tuple) -> set[str]:
    if p[0] == "atom":
        return {p[1]} if p[1][0].isupper() else set()
    out: set[str] = set()
    for a in p[2]:
        out |= prop_vars(a)
    return out


def match_prop(pat: tuple, conc: tuple, bind: dict[str, str]) -> bool:
    """Match a policy pattern against a concrete proposition, updating `bind`.

    Variables (uppercase atoms) bind consistently; constants must be equal.
    """
    if pat[0] == "atom":
        name = pat[1]
        if name[0].isupper():
            key = render_prop(conc)
            if name in bind:
                return bind[name] == key
            bind[name] = key
            return True
        return conc[0] == "atom" and conc[1] == name
    if conc[0] != "prop" or conc[1] != pat[1] or len(conc[2]) != len(pat[2]):
        return False
    return all(
        match_prop(pa, ca, bind) for pa, ca in zip(pat[2], conc[2])
    )


# --------------------------------------------------------------------------
# Trusted policy: parsed READ-ONLY, referenced by id, never defined here
# --------------------------------------------------------------------------


@dataclass
class Question:
    name: str
    pattern: tuple
    mandatory: bool


@dataclass
class Rule:
    name: str
    params: list[str]
    mode: str = ""
    premises: list[tuple] = field(default_factory=list)
    conclusion: tuple | None = None
    questions: list[Question] = field(default_factory=list)


@dataclass
class Policy:
    pid: str
    rules: list[Rule]
    contraries: list[tuple[tuple, tuple]]
    exceptions: list[tuple[str, tuple]]  # (rule name, pattern)
    # The `lara-core@0.2` signature blocks (`sort` / `con` / `pred`), retained
    # verbatim. This seed elaborator does not sort-check — that is the trusted
    # checker's stage 2 — but it must not be *silently* lenient about lines it
    # does not understand, so they are recorded rather than skipped.
    signature: list[str] = field(default_factory=list)


def parse_policy(text: str, path: str) -> Policy:
    pid = None
    rules: list[Rule] = []
    contraries: list[tuple[tuple, tuple]] = []
    exceptions: list[tuple[str, tuple]] = []
    signature: list[str] = []
    cur: Rule | None = None
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        loc = f"{path}:{lineno}"
        if not line or line.startswith("#"):
            continue
        if line.startswith("policy "):
            pid = line.split()[1]
            cur = None
            continue
        if re.match(r"(sort|con|pred)\s", line):
            signature.append(line)
            cur = None
            continue
        m = re.fullmatch(r"rule\s+([a-z][a-z0-9_]*)\(([^)]*)\)", line)
        if m:
            cur = Rule(m.group(1), [p.strip() for p in m.group(2).split(",")])
            rules.append(cur)
            continue
        if line.startswith("contrary "):
            rest = line[len("contrary ") :]
            p1, end = parse_prop_prefix(rest, loc)
            p2 = parse_prop(rest[end:].strip(), loc)
            contraries.append((p1, p2))
            cur = None
            continue
        m = re.fullmatch(r"exception\s+([a-z][a-z0-9_]*)\s*:\s*(.+)", line)
        if m:
            exceptions.append((m.group(1), parse_prop(m.group(2), loc)))
            cur = None
            continue
        if cur is None:
            raise ElabError(f"{loc}: unrecognized policy line: {line!r}")
        m = re.fullmatch(r"mode\s*=\s*(\w+)", line)
        if m:
            cur.mode = m.group(1)
            continue
        m = re.fullmatch(r"premises\s*=\s*\[(.*)\]", line)
        if m:
            cur.premises = [parse_prop(p, loc) for p in split_top(m.group(1))]
            continue
        m = re.fullmatch(r"conclusion\s*=\s*(.+)", line)
        if m:
            cur.conclusion = parse_prop(m.group(1), loc)
            continue
        m = re.fullmatch(
            r"question\s+([a-z][a-z0-9_]*)\s*:\s*(.*)\((mandatory|optional)\)", line
        )
        if m:
            cur.questions.append(
                Question(m.group(1), parse_prop(m.group(2).strip(), loc), m.group(3) == "mandatory")
            )
            continue
        raise ElabError(f"{loc}: unrecognized policy line: {line!r}")
    if pid is None:
        raise ElabError(f"{path}: policy id line missing")
    return Policy(pid, rules, contraries, exceptions, signature)


# --------------------------------------------------------------------------
# Source model (ara-mini-trace@1) with 6A validation
# --------------------------------------------------------------------------


@dataclass
class Cell:
    id: str
    topic: str
    what: str
    recorded: str
    refs: list[str]
    loc: str


@dataclass
class Node:
    id: str
    kind: str
    loc: str
    children: list["Node"] = field(default_factory=list)
    cells: list[Cell] = field(default_factory=list)
    # claim payload
    text: str = ""
    subject: tuple[str, str, str] = ("", "", "")
    author: str = ""
    reviewed: bool = False


ALLOWED_NODE_KEYS = {
    "question": {"id", "type", "title", "children"},
    "claim": {"id", "type", "text", "subject", "stance", "author", "reviewed", "children"},
    "experiment": {"id", "type", "title", "summary", "evidence_cells"},
    "dead_end": {"id", "type", "title", "narrative", "evidence_cells"},
}
ALLOWED_CELL_KEYS = {"id", "topic", "what", "value", "recorded", "refs"}
CHILD_KINDS = {
    "question": {"question", "claim"},
    "claim": {"experiment", "dead_end"},
}


def _req(mapping: dict, key: str, loc: str):
    if key not in mapping:
        raise ElabError(f"{loc}: missing required field {key!r}")
    return mapping[key]


def _atom(value, what: str, loc: str) -> str:
    if not isinstance(value, str) or not ID_RE.fullmatch(value):
        raise ElabError(f"{loc}: {what} must match [a-z][a-z0-9_]*, got {value!r}")
    return value


def _read_utf8(path: str, display_path: str, kind: str) -> tuple[bytes, str]:
    try:
        with open(path, "rb") as fh:
            data = fh.read()
    except OSError as e:
        raise ElabError(f"{display_path}: cannot read {kind}: {e}")
    try:
        return data, data.decode("utf-8")
    except UnicodeError as e:
        raise ElabError(f"{display_path}: invalid UTF-8 in {kind}: {e}")


def _is_lara_identifier(value: str) -> bool:
    """Lara.Syntax identifier: letter/_ then letters, ASCII digits, _, or -."""
    return bool(value) and (value[0].isalpha() or value[0] == "_") and all(
        c.isalpha() or "0" <= c <= "9" or c in "_-" for c in value[1:]
    )


def _is_lara_digest(value) -> bool:
    """Lara.Syntax digestLit without the parser's surrounding trivia."""
    if not isinstance(value, str):
        return False
    head, separator, body = value.partition(":")
    return (
        separator == ":"
        and _is_lara_identifier(head)
        and bool(body)
        and all(c.isalpha() or "0" <= c <= "9" or c in "._-" for c in body)
    )


def parse_cell(raw, loc: str) -> Cell:
    if not isinstance(raw, dict):
        raise ElabError(f"{loc}: evidence cell must be a mapping")
    cid = raw.get("id", "<no id>")
    cloc = f"{loc} (cell {cid!r})" if isinstance(cid, str) else loc
    unknown = set(raw) - ALLOWED_CELL_KEYS
    if unknown:
        raise ElabError(f"{cloc}: unknown cell field(s) {sorted(unknown)}")
    cid = _atom(_req(raw, "id", cloc), "cell id", cloc)
    if not cid.startswith("cell_"):
        raise ElabError(f"{cloc}: cell id must start with 'cell_'")
    topic = _req(raw, "topic", cloc)
    if topic not in TOPICS:
        raise ElabError(f"{cloc}: unknown evidence topic {topic!r}")
    what = _req(raw, "what", cloc)
    if not isinstance(what, str):
        raise ElabError(f"{cloc}: 'what' must be a string")
    recorded = _req(raw, "recorded", cloc)
    if recorded not in RECORDED_KINDS:
        raise ElabError(f"{cloc}: 'recorded' must be one of {sorted(RECORDED_KINDS)}")
    refs = _req(raw, "refs", cloc)
    if not isinstance(refs, list) or not all(isinstance(r, str) for r in refs):
        raise ElabError(f"{cloc}: 'refs' must be a list of strings")
    for r in refs:
        if not REF_RE.fullmatch(r):
            raise ElabError(f"{cloc}: ref {r!r} is not emittable bare (whitespace/[]/,)")
    if "value" in raw and not isinstance(raw["value"], str):
        raise ElabError(f"{cloc}: 'value' must be a string")
    return Cell(cid, topic, what, recorded, list(refs), cloc)


def parse_node(raw, loc: str) -> Node:
    if not isinstance(raw, dict):
        raise ElabError(f"{loc}: node must be a mapping")
    nid = raw.get("id")
    nloc = f"{loc} (node {nid!r})" if isinstance(nid, str) else loc
    kind = _req(raw, "type", nloc)
    if kind not in NODE_TYPES:
        raise ElabError(f"{nloc}: unknown node kind {kind!r}")
    unknown = set(raw) - ALLOWED_NODE_KEYS[kind]
    if unknown:
        raise ElabError(f"{nloc}: unknown field(s) {sorted(unknown)} for a {kind} node")
    nid = _atom(_req(raw, "id", nloc), "node id", nloc)
    nloc = f"{loc} (node {nid!r})"
    node = Node(nid, kind, nloc)
    if kind in ("question", "experiment", "dead_end"):
        title = _req(raw, "title", nloc)
        if not isinstance(title, str):
            raise ElabError(f"{nloc}: 'title' must be a string")
    if kind in ("experiment", "dead_end"):
        summary_key = "summary" if kind == "experiment" else "narrative"
        if not isinstance(_req(raw, summary_key, nloc), str):
            raise ElabError(f"{nloc}: {summary_key!r} must be a string")
    if kind == "claim":
        if not nid.startswith("claim_"):
            raise ElabError(f"{nloc}: claim node id must start with 'claim_'")
        text = _req(raw, "text", nloc)
        if not isinstance(text, str):
            raise ElabError(f"{nloc}: 'text' must be a string")
        node.text = text
        subject = _req(raw, "subject", nloc)
        if not isinstance(subject, dict):
            raise ElabError(f"{nloc}: 'subject' must be a mapping")
        node.subject = tuple(
            _atom(_req(subject, k, nloc), f"subject.{k}", nloc)
            for k in ("method", "quality", "distribution")
        )
        stance = _req(raw, "stance", nloc)
        if stance != "improvement":
            raise ElabError(f"{nloc}: unsupported stance {stance!r} (no derivation defined)")
        node.author = _atom(_req(raw, "author", nloc), "author", nloc)
        reviewed = _req(raw, "reviewed", nloc)
        if not isinstance(reviewed, bool):
            raise ElabError(f"{nloc}: 'reviewed' must be a boolean")
        node.reviewed = reviewed
    if kind in ("experiment", "dead_end"):
        if kind == "experiment" and not nid.startswith("exp_"):
            raise ElabError(f"{nloc}: experiment node id must start with 'exp_'")
        cells = raw["evidence_cells"] if "evidence_cells" in raw else []
        if not isinstance(cells, list):
            raise ElabError(f"{nloc}: 'evidence_cells' must be a list")
        node.cells = [
            parse_cell(c, f"{nloc}.evidence_cells[{i}]")
            for i, c in enumerate(cells)
        ]
    else:
        children = raw["children"] if "children" in raw else []
        if not isinstance(children, list):
            raise ElabError(f"{nloc}: 'children' must be a list")
        for i, c in enumerate(children):
            child = parse_node(c, f"{nloc}.children[{i}]")
            if child.kind not in CHILD_KINDS[kind]:
                raise ElabError(
                    f"{child.loc}: a {child.kind} node cannot be a child of a {kind} node"
                )
            node.children.append(child)
    return node


@dataclass
class Source:
    policy_id: str
    artifact_id: str
    digest: str
    claims: list[Node]  # claim nodes in source tree (pre-order)


def load_source(bundle_dir: str) -> Source:
    src_path = os.path.join(bundle_dir, "source.yaml")
    _, text = _read_utf8(src_path, src_path, "source")
    try:
        doc = yaml.safe_load(text)
    except yaml.YAMLError as e:
        mark = getattr(e, "problem_mark", None)
        problem = getattr(e, "problem", None) or str(e)
        where = f"line {mark.line + 1}, column {mark.column + 1}" if mark else "unknown position"
        raise ElabError(f"{src_path}: {where}: unparseable YAML: {problem}")
    if not isinstance(doc, dict):
        raise ElabError(f"{src_path}: top level must be a mapping with 'meta' and 'tree'")
    meta = _req(doc, "meta", src_path)
    if not isinstance(meta, dict):
        raise ElabError(f"{src_path}: 'meta' must be a mapping")
    if meta.get("format") != SOURCE_FORMAT:
        raise ElabError(f"{src_path}: meta.format must be {SOURCE_FORMAT!r}")
    artifact = _req(meta, "artifact", f"{src_path}: meta")
    if not isinstance(artifact, dict):
        raise ElabError(f"{src_path}: meta.artifact must be a mapping")
    artifact_id = _atom(_req(artifact, "id", f"{src_path}: meta.artifact"), "artifact id", src_path)
    digest = _req(artifact, "digest", f"{src_path}: meta.artifact")
    if not _is_lara_digest(digest):
        raise ElabError(
            f"{src_path}: meta.artifact.digest must be a Lara digest "
            "(identifier:non-empty body of letters, digits, '.', '_', or '-'), "
            f"got {digest!r}"
        )
    policy_id = _req(meta, "policy", f"{src_path}: meta")
    if not isinstance(policy_id, str) or not re.fullmatch(r"[a-z][a-z0-9-]*", policy_id):
        raise ElabError(f"{src_path}: meta.policy must be a policy id, got {policy_id!r}")
    tree = _req(doc, "tree", src_path)
    if not isinstance(tree, list):
        raise ElabError(f"{src_path}: 'tree' must be a list")
    claims: list[Node] = []

    def collect(node: Node):
        if node.kind == "claim":
            claims.append(node)
        for c in node.children:
            collect(c)

    for i, raw in enumerate(tree):
        node = parse_node(raw, f"{src_path}: tree[{i}]")
        if node.kind not in CHILD_KINDS["question"]:
            raise ElabError(
                f"{node.loc}: a {node.kind} node cannot appear at the top level of 'tree'"
            )
        collect(node)
    if not claims:
        raise ElabError(f"{src_path}: the trace contains no claim nodes")
    return Source(policy_id, artifact_id, digest, claims)


# --------------------------------------------------------------------------
# The six §11 tasks (derivation contract: bundles/README.md §4.2)
# --------------------------------------------------------------------------


@dataclass
class Leaf:
    lid: str
    prop: tuple
    kind: str
    provenance: str
    refs: list[str]
    cell: Cell


@dataclass
class Instantiation:
    arg: str
    rule: Rule
    substitution: list[tuple[str, str]]  # rule parameter order
    premise_leaves: list[str]
    experiment: Node
    discharges: list[dict] = field(default_factory=list)  # task-4 entries
    emitted: bool = False


@dataclass
class Attack:
    attacker: str
    kind: str  # "undercut" | "undermine"
    challenges: str
    target: str
    source_node: str
    policy_basis: str
    leaf: str


@dataclass
class ClaimDerivation:
    node: Node
    cid: str
    formal: tuple
    nl: str
    author: str
    audit_status: str
    leaves: list[Leaf] = field(default_factory=list)
    instantiations: list[Instantiation] = field(default_factory=list)
    attacks: list[Attack] = field(default_factory=list)


def is_positive_report(p: tuple) -> bool:
    """Premise shape: reports(X, effect(M, Q, D, positive))."""
    return (
        p[0] == "prop"
        and p[1] == "reports"
        and len(p[2]) == 2
        and p[2][1][0] == "prop"
        and p[2][1][1] == "effect"
        and len(p[2][1][2]) == 4
        and p[2][1][2][3] == ("atom", "positive")
    )


def derive(src: Source, policy: Policy) -> tuple[list[ClaimDerivation], dict]:
    prov1, prov2, prov3, prov4, prov6 = [], [], [], [], []
    derivations: list[ClaimDerivation] = []

    for claim in src.claims:
        m, q, d = claim.subject
        cd = ClaimDerivation(
            node=claim,
            cid="c_" + claim.id[len("claim_") :],
            formal=("prop", "improves", [("atom", m), ("atom", q), ("atom", d)]),
            nl=claim.text,
            author=claim.author,
            audit_status="reviewed" if claim.reviewed else "unreviewed",
        )
        derivations.append(cd)

        # ---- Task 1: NL proposition formalization --------------------------
        prov1.append(
            {
                "source-node": claim.id,
                "claim": cd.cid,
                "nl": cd.nl,
                "formal": render_prop(cd.formal),
                "binding": {"author": cd.author, "audit-status": cd.audit_status},
            }
        )

        # The claim's supporting experiments: those carrying a
        # positive-effect-report cell (task-3 instantiation targets).
        support_exps = [
            n
            for n in claim.children
            if n.kind == "experiment"
            and any(c.topic == "positive-effect-report" for c in n.cells)
        ]

        def bind_experiment(node: Node, cell: Cell) -> str:
            if node.kind == "experiment":
                return node.id
            # A dead-end-nested cell binds the claim context's unique
            # supporting experiment (README §4.2 task 2).
            if len(support_exps) != 1:
                raise ElabError(
                    f"{cell.loc}: dead-end-nested cell needs a unique supporting "
                    f"experiment in claim {claim.id!r}, found {len(support_exps)}"
                )
            return support_exps[0].id

        # ---- Task 2: evidence-leaf extraction + source binding -------------
        for node in claim.children:  # tree-walk order
            for cell in node.cells:
                exp_const = bind_experiment(node, cell)
                M, Q, D, E = ("atom", m), ("atom", q), ("atom", d), ("atom", exp_const)
                prop = {
                    "positive-effect-report": (
                        "prop",
                        "reports",
                        [E, ("prop", "effect", [M, Q, D, ("atom", "positive")])],
                    ),
                    "randomization": ("prop", "randomized", [E]),
                    "power": ("prop", "powered", [E]),
                    "generalization": ("prop", "generalizes", [M, Q, D]),
                    "distribution-shift": ("prop", "distribution_shift", [M, Q, D]),
                    "generalization-failure": ("prop", "not_generalizes", [M, Q, D]),
                }[cell.topic]
                kind, leaf_prov = (
                    ("observed", "ai-executed")
                    if cell.recorded == "run-output"
                    else ("attested", "user")
                )
                leaf = Leaf(
                    lid="e_" + cell.id[len("cell_") :],
                    prop=prop,
                    kind=kind,
                    provenance=leaf_prov,
                    refs=cell.refs,
                    cell=cell,
                )
                cd.leaves.append(leaf)
                prov2.append(
                    {
                        "source-cell": cell.id,
                        "leaf": leaf.lid,
                        "proposition": render_prop(prop),
                        "kind": kind,
                        "provenance": leaf_prov,
                        "refs": list(cell.refs),
                        "grain": "result-cell",
                        "duplicate-report": (
                            {"locations": list(cell.refs)} if len(cell.refs) > 1 else None
                        ),
                    }
                )

        # ---- Task 3: scheme selection + instantiation ----------------------
        # Select from the trusted policy by premise/conclusion SHAPE: the
        # unique defeasible rule with a positive-effect-report premise whose
        # conclusion matches the task-1 predicate. Never by an id in the source.
        selected: list[tuple[Rule, dict[str, str]]] = []
        for rule in policy.rules:
            if rule.mode != "defeasible" or rule.conclusion is None:
                continue
            if not any(is_positive_report(p) for p in rule.premises):
                continue
            bind: dict[str, str] = {}
            if match_prop(rule.conclusion, cd.formal, bind):
                selected.append((rule, bind))
        if support_exps and len(selected) != 1:
            raise ElabError(
                f"{claim.loc}: expected exactly one policy rule matching the "
                f"positive-report/improvement shape, found {len(selected)}"
            )
        for exp in support_exps:
            rule, bind = selected[0]
            premise_prop = next(p for p in rule.premises if is_positive_report(p))
            exp_var = next(
                (
                    a[1]
                    for a in premise_prop[2][:1]
                    if a[0] == "atom" and a[1][0].isupper()
                ),
                None,
            )
            if exp_var is None:
                raise ElabError(
                    f"{claim.loc}: policy rule {rule.name!r} positive-report premise "
                    f"lacks an experiment variable in its first argument"
                )
            bind = dict(bind)
            bind[exp_var] = exp.id
            missing = [p for p in rule.params if p not in bind]
            if missing:
                raise ElabError(
                    f"{claim.loc}: policy rule {rule.name!r} params {missing} are "
                    f"unbound after matching (conclusion/premise shape mismatch)"
                )
            substitution = [(p, bind[p]) for p in rule.params]
            inst = Instantiation(
                arg="a_" + exp.id[len("exp_") :],
                rule=rule,
                substitution=substitution,
                premise_leaves=[
                    lf.lid
                    for lf in cd.leaves
                    if lf.cell.topic == "positive-effect-report"
                    and lf.prop[2][0] == ("atom", exp.id)
                ],
                experiment=exp,
            )
            cd.instantiations.append(inst)
            prov3.append(
                {
                    "source-node": exp.id,
                    "arg": inst.arg,
                    "rule": rule.name,
                    "substitution": [[v, val] for v, val in substitution],
                    "premise-leaves": list(inst.premise_leaves),
                }
            )

        # ---- Task 4: critical-question discharge or explicit hole ----------
        cell_less_dead_ends = [
            n for n in claim.children if n.kind == "dead_end" and not n.cells
        ]
        for inst in cd.instantiations:
            subst = dict(inst.substitution)
            holes: list[Question] = []
            for question in inst.rule.questions:  # policy declaration order
                # Instantiate the question's answer pattern.
                answer_bind = {k: ("atom", v) for k, v in subst.items()}

                def instantiate(p: tuple) -> tuple:
                    if p[0] == "atom":
                        if p[1][0].isupper():
                            if p[1] not in answer_bind:
                                raise ElabError(
                                    f"{claim.loc}: critical question "
                                    f"{question.name!r} of rule {inst.rule.name!r} "
                                    f"references unbound variable {p[1]!r}"
                                )
                            return answer_bind[p[1]]
                        return p
                    return ("prop", p[1], [instantiate(a) for a in p[2]])

                answer = instantiate(question.pattern)
                leaf = next((lf for lf in cd.leaves if lf.prop == answer), None)
                if leaf is not None:
                    inst.discharges.append(
                        {
                            "arg": inst.arg,
                            "question": question.name,
                            "decision": "discharge",
                            "with": leaf.lid,
                            "source-cell": leaf.cell.id,
                        }
                    )
                else:
                    holes.append(question)
                    responsible = (
                        cell_less_dead_ends[0].id
                        if len(cell_less_dead_ends) == 1
                        else claim.id
                    )
                    inst.discharges.append(
                        {
                            "claim": cd.cid,
                            "question": question.name,
                            "decision": "hole",
                            "source-node": responsible,
                            "lowered": "gap",
                            "reason": HOLE_REASON,
                        }
                    )
            prov4.extend(inst.discharges)
            # Hole lowering (README §1): an open mandatory question is a whole-
            # unit rejection, so the incomplete argument is NOT emitted; the
            # claim's complete-support set stays empty (-> gap).
            inst.emitted = not holes

        # ---- Task 6: typed-attack extraction over the whole trace ----------
        discharge_records = [
            (inst, entry, next(lf for lf in cd.leaves if lf.lid == entry["with"]))
            for inst in cd.instantiations
            for entry in inst.discharges
            if entry["decision"] == "discharge"
        ]
        support_props = set()
        for inst in cd.instantiations:
            subst = dict(inst.substitution)
            b = {k: ("atom", v) for k, v in subst.items()}

            def inst_prop(p: tuple) -> tuple:
                if p[0] == "atom":
                    return b[p[1]] if p[1][0].isupper() else p
                return ("prop", p[1], [inst_prop(a) for a in p[2]])

            for prem in inst.rule.premises:
                support_props.add(render_prop(inst_prop(prem)))
            for question in inst.rule.questions:
                support_props.add(render_prop(inst_prop(question.pattern)))

        for node in claim.children:  # every experiment and dead_end, tree order
            node_attacks = 0
            node_supports = 0
            for cell in node.cells:
                leaf = next(lf for lf in cd.leaves if lf.cell is cell)
                # (a) exception of an instantiated rule -> undercut
                attack = None
                for rule_name, pattern in policy.exceptions:
                    inst = next(
                        (i for i in cd.instantiations if i.rule.name == rule_name), None
                    )
                    if inst is None:
                        continue
                    if match_prop(pattern, leaf.prop, {}):
                        qs = [
                            qn
                            for qn in inst.rule.questions
                            if prop_vars(qn.pattern) == prop_vars(pattern)
                        ]
                        if len(qs) != 1:
                            raise ElabError(
                                f"{cell.loc}: exception {render_prop(pattern)} of rule "
                                f"{rule_name} attaches to no unique critical question"
                            )
                        attack = Attack(
                            attacker="d_" + cell.id[len("cell_") :],
                            kind="undercut",
                            challenges=f"{qs[0].name}({inst.arg})",
                            target=f"{inst.arg}.rule",
                            source_node=node.id,
                            policy_basis=f"exception {rule_name} : {render_prop(pattern)}",
                            leaf=leaf.lid,
                        )
                        break
                # (b) declared contrary of a discharge leaf's proposition -> undermine
                if attack is None:
                    for inst, entry, dleaf in discharge_records:
                        for p1, p2 in policy.contraries:
                            b1: dict[str, str] = {}
                            if match_prop(p2, leaf.prop, b1) and match_prop(
                                p1, dleaf.prop, b1
                            ):
                                attack = Attack(
                                    attacker="d_" + cell.id[len("cell_") :],
                                    kind="undermine",
                                    challenges=dleaf.lid,
                                    target=f"{inst.arg}.{entry['question']}.leaf",
                                    source_node=node.id,
                                    policy_basis=f"contrary {render_prop(p1)} {render_prop(p2)}",
                                    leaf=leaf.lid,
                                )
                                break
                        if attack is not None:
                            break
                if attack is not None:
                    node_attacks += 1
                    cd.attacks.append(attack)
                    prov6.append(
                        {
                            "source-node": node.id,
                            "role": "attack",
                            "attack": {
                                "kind": attack.kind,
                                "attacker": attack.attacker,
                                "target": attack.target,
                            },
                            "policy-basis": attack.policy_basis,
                        }
                    )
                elif node.kind == "dead_end":
                    if render_prop(leaf.prop) in support_props:
                        # (c) answers a premise or question in context -> support
                        node_supports += 1
                        prov6.append(
                            {"source-node": node.id, "role": "support", "leaf": leaf.lid}
                        )
            # (d) no lowering: a dead end that only documents unmet questions
            # routes to the task-4 hole, never to an attack (spec §7).
            if (
                node.kind == "dead_end"
                and not node.cells
                and node_attacks == 0
                and node_supports == 0
            ):
                prov6.append({"source-node": node.id, "role": "none", "note": NONE_NOTE})

    # ---- Task 5: strict-backend / theory / certificate selection -----------
    # N/A for this all-defeasible source (T1); logged as not-applicable.
    provenance = {
        "format": PROVENANCE_FORMAT,
        "policy": src.policy_id,
        "source": "source.yaml",
        "task-1-formalization": prov1,
        "task-2-leaf-extraction": prov2,
        "task-3-scheme-selection": prov3,
        "task-4-question-accounting": prov4,
        "task-5-strict-selection": dict(TASK5_ENTRY),
        "task-6-attack-extraction": prov6,
    }
    return derivations, provenance


# --------------------------------------------------------------------------
# Emission (pinned layout: bundles/README.md §4.3)
# --------------------------------------------------------------------------


def section(title: str) -> str:
    head = f"# --- {title} "
    return head + "-" * max(0, 80 - len(head))


def render_lara(src: Source, derivations: list[ClaimDerivation]) -> str:
    blocks: list[str] = [
        "\n".join(
            [
                "# emitted.lara -- machine-produced by the untrusted M4b elaborator.",
                "# Derived from source.yaml (ara-mini-trace@1) and the trusted policy",
                f"# {src.policy_id} (referenced by id; defined in the policy, never here),",
                "# per the bundle format contract, section 4; every derivation",
                "# is logged in provenance.json. Do not hand-edit.",
            ]
        ),
        "\n".join(
            [
                f"artifact {src.artifact_id} at {src.digest}",
                f"policy {src.policy_id}",
                "use backends [nd@1]",
            ]
        ),
    ]
    for cd in derivations:
        blocks.append(section(cd.node.id))
        blocks.append(
            "\n".join(
                [
                    f"claim {cd.cid}",
                    f"  nl      = {json.dumps(cd.nl, ensure_ascii=True)}",
                    f"  formal  = {render_prop(cd.formal)}",
                    f"  binding = {{ author = {cd.author}, audit-status = {cd.audit_status} }}",
                ]
            )
        )
        for lf in cd.leaves:
            blocks.append(
                "\n".join(
                    [
                        f"leaf {lf.lid} : {render_prop(lf.prop)}",
                        f"  kind       = {lf.kind}",
                        f"  provenance = {lf.provenance}",
                        f"  refs       = [{', '.join(lf.refs)}]",
                    ]
                )
            )
        for inst in cd.instantiations:
            if not inst.emitted:
                continue
            args = ", ".join(v for _, v in inst.substitution)
            lines = [f"arg {inst.arg} : supports({cd.cid}) by {inst.rule.name}({args})"]
            width = max((len(q.name) for q in inst.rule.questions), default=0) + 1
            for entry in inst.discharges:
                lines.append(
                    f"  discharge {entry['question'].ljust(width)}with {entry['with']}"
                )
            blocks.append("\n".join(lines))
    attacks = [a for cd in derivations for a in cd.attacks]
    if attacks:
        blocks.append(section("typed attacks (task 6)"))
        for a in attacks:
            blocks.append(
                "\n".join(
                    [
                        f"# {a.source_node}",
                        f"arg {a.attacker} : challenges({a.challenges}) by leaf({a.leaf})",
                        f"{a.kind} {a.attacker} {a.target}",
                    ]
                )
            )
    blocks.append(section("status queries"))
    blocks.append("\n".join(f"status {cd.cid}" for cd in derivations))
    return "\n\n".join(blocks) + "\n"


def render_provenance(provenance: dict) -> str:
    return json.dumps(provenance, sort_keys=True, indent=2, ensure_ascii=True) + "\n"


# --------------------------------------------------------------------------
# Transactional bundle write (T9)
# --------------------------------------------------------------------------


def write_bundle(bundle_dir: str, files: dict[str, bytes]) -> None:
    """Stage all artifacts in a temp dir inside the bundle, then rename into
    place only on full success. Raises on any failure; the caller cleans up."""
    stage = tempfile.mkdtemp(prefix=".elaborate-stage-", dir=bundle_dir)
    try:
        for name, data in files.items():
            with open(os.path.join(stage, name), "wb") as fh:
                fh.write(data)
        for name in files:
            os.replace(os.path.join(stage, name), os.path.join(bundle_dir, name))
    finally:
        shutil.rmtree(stage, ignore_errors=True)


def cleanup_targets(bundle_dir: str) -> None:
    """A failed run leaves no partial or stale B1 artifacts (README §2/T9)."""
    for name in ("emitted.lara", "provenance.json"):
        try:
            os.remove(os.path.join(bundle_dir, name))
        except OSError:
            pass
    for name in os.listdir(bundle_dir) if os.path.isdir(bundle_dir) else []:
        if name.endswith(".policy.lara") or name.startswith(".elaborate-stage-"):
            shutil.rmtree(os.path.join(bundle_dir, name), ignore_errors=True)
            try:
                os.remove(os.path.join(bundle_dir, name))
            except OSError:
                pass


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def run(bundle_dir: str) -> list[str]:
    if not os.path.isdir(bundle_dir):
        raise ElabError(f"{bundle_dir}: not a directory")
    src = load_source(bundle_dir)

    # Trusted input: load the referenced policy READ-ONLY, by id (1A/§4.0).
    policy_rel = os.path.join(POLICY_REL, f"{src.policy_id}.policy.lara")
    policy_path = os.path.join(REPO_ROOT, policy_rel)
    policy_bytes, policy_text = _read_utf8(
        policy_path,
        policy_rel,
        f"trusted policy {src.policy_id!r}",
    )
    policy = parse_policy(policy_text, policy_rel)
    if policy.pid != src.policy_id:
        raise ElabError(
            f"policy id mismatch: source references {src.policy_id!r} but "
            f"{policy_rel} declares {policy.pid!r}"
        )

    derivations, provenance = derive(src, policy)
    files = {
        f"{src.policy_id}.policy.lara": policy_bytes,  # byte-for-byte copy (1A)
        "emitted.lara": render_lara(src, derivations).encode("utf-8"),
        "provenance.json": render_provenance(provenance).encode("utf-8"),
    }
    write_bundle(bundle_dir, files)
    return sorted(files)


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: elaborate.py <bundle-dir>", file=sys.stderr)
        return 2
    bundle_dir = argv[1]
    try:
        written = run(bundle_dir)
    except ElabError as e:
        cleanup_targets(bundle_dir)
        print(f"elaborate: error: {e}", file=sys.stderr)
        return 2
    except OSError as e:
        cleanup_targets(bundle_dir)
        print(f"elaborate: error: {e}", file=sys.stderr)
        return 2
    for name in written:
        print(f"wrote {os.path.join(bundle_dir, name)}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
