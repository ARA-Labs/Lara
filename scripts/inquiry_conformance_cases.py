"""Generated inquiry contracts: parsed-tree mutations, independently expected outcomes."""
from copy import deepcopy
from dataclasses import dataclass
from pathlib import Path

from evidence_measured import canonical, parse, wire

FIXTURES = Path(__file__).resolve().parents[1] / "fixtures/process/inquiry"


@dataclass(frozen=True)
class Case:
    name: str
    document: bytes
    code: int
    stdout: bytes


def block(tree, name):
    matches = [x for x in tree if isinstance(x, list) and x and x[0] == name]
    assert len(matches) == 1, (name, matches)
    return matches[0]


def fixture(name):
    return parse((FIXTURES / f"{name}.sexp").read_bytes())


def error(kind, detail):
    return canonical(["inquiry-error", "1", [], [kind, detail]])


def limit(counter, actual, cap):
    return canonical(["inquiry-error", "1", [], ["limit", ["counter", counter],
                      ["actual", str(actual)], ["cap", str(cap)]]])


def setcap(tree, counter, value):
    block(block(tree, "inquiry-limits"), counter)[1] = str(value)


def roomy(tree):
    for counter in block(tree, "inquiry-limits")[1:]:
        counter[1] = str(10**18)
    block(block(tree[2], "limits"), "completions")[1] = str(10**18)
    return tree


def blank():
    tree = fixture("limit-sources-at-cap")
    block(tree, "slots")[:] = ["slots"]
    block(tree[2], "queries")[:] = ["queries"]
    return roomy(tree)


def binary_slots(count):
    slot = fixture("limit-sources-at-cap")[4][1]
    result = []
    for index in range(count):
        item = deepcopy(slot)
        item[1][1] = str(index)
        result.append(item)
    return result


def generated_cases():
    cases = []

    def add(name, tree, code, output):
        cases.append(Case(name, canonical(tree), code, output))

    malformed = error("malformed", "malformed inquiry-input")
    base = blank()
    add("empty-output", base, 0, b"")
    for name, mutate in [
        ("section-order", lambda t: t.__setitem__(slice(4, 6), [t[5], t[4]])),
        ("section-missing", lambda t: t.pop(6)),
        ("section-extra", lambda t: t.append(["requests"])),
        ("request-arity", lambda t: block(t, "requests").append(["status", "short"])),
        ("unknown-name", lambda t: block(t, "requests").append(["status", "unknown", "absent"])),
        ("duplicate-name", lambda t: block(block(t[2], "names"), "claim").extend(["same", "same"])),
        ("negative-natural", lambda t: setcap(t, "pairs", "-1")),
        ("leading-zero-natural", lambda t: setcap(t, "pairs", "01")),
        ("unknown-constructor", lambda t: block(t, "requests").append(["unknown", "label"])),
    ]:
        tree = deepcopy(base)
        mutate(tree)
        add(name, tree, 2, malformed)
    tree = deepcopy(base)
    tree[1] = "2"
    add("wrong-version", tree, 2, error("version", "inquiry-input supports version 1 only, found 2"))
    add("wrong-envelope", ["other", "1"], 2, error("malformed", "expected an inquiry-input document"))

    # Shared whole-document counters precede labels, references and dispatch.
    tree = fixture("unresolved-claim-impact")
    for cap in (17, 18):
        changed = deepcopy(tree)
        setcap(changed, "pairs", cap)
        add(f"missing-impact-binding-{cap}", changed, 1 if cap == 17 else 2,
            limit("pairs", 18, 17) if cap == 17 else error("malformed", "unresolved claim in impact request"))
        block(changed[2], "queries").append(["verdict", block(changed, "requests")[1][1], ["predictable"]])
        add(f"cross-list-label-{cap}", changed, 1 if cap == 17 else 2,
            limit("pairs", 18, 17) if cap == 17 else error("malformed", "duplicate result labels"))
    changed = deepcopy(tree)
    request = block(changed, "requests")[1]
    block(changed, "requests").insert(1, ["sensitivity", "bad-reference",
        ["reference", ["ref-history", []], ["ref-choices", [[["slot-id", str(2**128)], ["choice-id", "0"]]]]],
        ["observable", ["status-obs", request[-1][1]]]])
    setcap(changed, "pairs", 4096)
    add("reference-before-impact-binding", changed, 2, error("malformed", "unresolved or out-of-family source reference"))
    block(changed[2], "queries").append(["verdict", request[1], ["predictable"]])
    add("labels-before-reference-and-binding", changed, 2, error("malformed", "duplicate result labels"))
    ref = fixture("reference-sensitivity")
    block(block(ref, "requests")[1][2], "ref-choices")[1][0][0][1] = str(2**128)
    add("invalid-reference", ref, 2, error("malformed", "unresolved or out-of-family source reference"))

    minimal = roomy(fixture("minimal-conditions"))
    target = deepcopy(block(minimal, "requests")[1][2])
    catalog = [["literal", ["slot-eq", ["slot-id", str(i)], ["choice-id", "0"]]] for i in range(128)]
    for repeats in (1, 2):
        tree = deepcopy(minimal)
        # Repeated authored literals must be deduplicated before exponentiation.
        block(tree, "assumption-catalog")[:] = ["assumption-catalog"] + catalog + catalog
        block(tree, "requests")[:] = ["requests"] + [["minimal-assumptions", "duplicate", target]] * repeats
        setcap(tree, "subsets", 1)
        setcap(tree, "pairs", 0)
        add(f"huge-dedup-catalog-{repeats}", tree, 1, limit("subsets", repeats * 2**128, 1))
    tree = deepcopy(minimal)
    block(tree, "requests")[:] = ["requests", ["minimal-assumptions", "subsets", target],
        ["impact", "endpoints", tree[3], tree[3], ["queries"]]]
    setcap(tree, "sources", 8)
    setcap(tree, "subsets", 0)
    setcap(tree, "declarations", 0)
    setcap(tree, "pairs", 0)
    add("endpoint-sources-before-subsets", tree, 1, limit("sources", 10, 8))

    # A single status request costs one pair even without any bound source claim.
    tree = blank()
    block(block(tree[2], "names"), "claim").append("c")
    block(tree, "requests").extend([["status", "first", "c"], ["status", "second", "c"]])
    setcap(tree, "pairs", 1)
    add("shared-pairs-exhaustion", tree, 1, limit("pairs", 2, 1))
    block(tree, "requests")[:] = ["requests"] + [["status", f"r{i}", "c"] for i in range(4097)]
    setcap(tree, "pairs", 10**18)
    add("ceiling-pairs", tree, 1, limit("pairs", 4097, 4096))
    tree = deepcopy(minimal)
    block(tree, "assumption-catalog")[:] = ["assumption-catalog"] + catalog[:13]
    add("ceiling-subsets", tree, 1, limit("subsets", 8192, 4096))
    tree = blank()
    block(tree, "slots").extend(binary_slots(14))
    add("ceiling-sources", tree, 1, limit("sources", 10001, 10000))
    tree = blank()
    block(tree, "slots").extend(binary_slots(13))
    # Count authored declarations in the serialized program list, not a golden.
    program = tree[3][2][0]
    items = program[2]
    values = []
    while items[0] == "cons":
        values.append(items[1])
        items = items[2]
    assert items == ["nil"] and len(values) == 6, "program constructor changed"
    declarations, count = values[5][2], 0
    while declarations[0] == "cons":
        count += 1
        declarations = declarations[2]
    assert declarations == ["nil"] and count > 1
    add("ceiling-declarations", tree, 1, limit("declarations", 8192 * count, 10000))
    tree = blank()
    block(block(tree[2], "names"), "event").extend([f"e{i}" for i in range(7)])
    block(block(tree[2], "names"), "actor").append("a")
    block(block(tree[2], "names"), "data").append("d")
    block(tree[2], "universe").extend([["event", f"e{i}", ["access", "a", "d", "evaluation"]] for i in range(7)])
    # Every executable prefix is compatible: sum P(7,k) = 13700, including
    # the root. Seven events already exceed the fixed history ceiling.
    add("ceiling-histories", tree, 1, limit("histories", 13700, 10000))
    block(block(tree[2], "names"), "event").extend(["e7", "e8"])
    block(tree[2], "universe").extend([["event", f"e{i}", ["access", "a", "d", "evaluation"]] for i in (7, 8)])
    block(block(tree[2], "limits"), "events")[1] = str(10**18)
    add("ceiling-events", tree, 1, limit("histories", 9, 8))
    # A small repeated catalog independently pins the retained authored list
    # and the deduplicated subset charge (three entries, two distinct literals).
    tree = blank()
    block(block(tree[2], "names"), "claim").append("c")
    small_catalog = [catalog[0], catalog[1], catalog[0]]
    block(tree, "assumption-catalog").extend(small_catalog)
    small_target = ["target", ["status-target", "c", ["published", "justified"]]]
    block(tree, "requests").append(["minimal-assumptions", "small", small_target])
    setcap(tree, "subsets", 4)
    add("dedup-catalog-at-cap", tree, 0, canonical(["inquiry-result", "1", "small",
        ["assumptions-body", ["assumption-result", small_target, small_catalog, "1", []]]]))
    setcap(tree, "subsets", 3)
    add("dedup-catalog-over-cap", tree, 1, limit("subsets", 4, 3))
    tree = fixture("p0-verdict")
    block(block(tree[2], "limits"), "events")[1] = "0"
    setcap(tree, "source-bytes", 0)
    add("events-before-bytes", tree, 1, limit("histories", 3, 0))
    tree = blank()
    raw = canonical(tree) + b";" + b"x" * 1048576
    cases.append(Case("ceiling-source-bytes", raw, 1, limit("source-bytes", len(raw), 1048576)))

    # The wrapper deliberately accepts bare profile lists and denominator zero;
    # the embedded process profile deliberately does not.
    tree = fixture("fixed-witness")
    block(block(tree, "requests")[1][-1], "guarantee")[3] = "0"
    # A zero denominator denotes level zero: the positive attained guarantee
    # fails in both rows (the second row already failed in the authored case).
    expected = parse((FIXTURES / "fixed-witness.expected").read_bytes())
    expected[3][1][1][0][-1] = ["false"]
    add("wrapper-zero-denominator", tree, 0, canonical(expected))
    tree = fixture("p0-embedded-audit")
    profile = block(tree[2], "queries")[1][-1]
    block(profile, "guarantee")[3] = "0"
    add("embedded-zero-denominator", tree, 2, malformed)

    certificate_cases(cases)
    syntax_cases(cases)
    return cases


def certificate_cases(cases):
    original = fixture("verified-certificate")
    original[2][-1] = ["queries"]
    request = block(original, "requests")[1]
    request[1] = "verification"

    def mutate_snapshot(c):
        c[4] = [["probe", ["failed", "probe"]]]

    def mutate_identity(c):
        c[6][-1] = "forged-digest"

    def mutate_report(c):
        c[8][1] = "false"

    def mutate_transition(c):
        c[10][1] = "rejected-to-rejected"

    def mutate_blocked(c):
        c[14] = [["atom", "forged"]]

    def mutate_rows(c):
        c[11][0][4] = "false"

    def mutate_partition(c):
        c[12] = []

    def mutate_graph(c):
        c[16].append("forged")

    def mutate_locality(c):
        c[19][0][1] = "true"

    def mutate_reads(c):
        c[20] = []

    mutations = [("snapshots", "mismatched-snapshots", mutate_snapshot),
        ("identities", "mismatched-identities", mutate_identity),
        ("reports", "outcome-mismatch", mutate_report),
        ("transition", "outcome-mismatch", mutate_transition),
        ("blocked", "outcome-mismatch", mutate_blocked),
        ("rows", "status-mismatch", mutate_rows),
        ("partition", "invalid-supports", mutate_partition),
        ("graph", "invalid-graph", mutate_graph),
        ("locality", "false-locality", mutate_locality),
        ("reads", "false-read-evidence", mutate_reads)]
    for index, (name, fault, change) in enumerate(mutations):
        for precedence in ((False, True) if index + 1 < len(mutations) else (False,)):
            tree = deepcopy(original)
            certificate = block(tree, "requests")[1][-1]
            change(certificate)
            if precedence:
                for _, _, later in mutations[index+1:]:
                    later(certificate)
            output = canonical(["inquiry-result", "1", "verification",
                ["verification-body", ["invalid-certificate", [fault]]]])
            cases.append(Case(f"certificate-{name}" + ("-precedence" if precedence else ""), canonical(tree), 0, output))
    # Keep every required (side,key), but falsify a closed, well-shaped value.
    # A conflicting duplicate must fail even when its correct triple remains.
    for name, duplicate in (("wrong-value", False), ("conflicting-duplicate", True)):
        tree = deepcopy(original)
        reads = block(tree, "requests")[1][-1][20]
        bool_reads = [entry for entry in reads if entry[3][0] == "v-bool"]
        assert bool_reads, "authored certificate lacks boolean read evidence"
        actual = bool_reads[0]
        assert actual[:1] == ["reads"] and actual[1][0] == "side"
        assert actual[3][1] in ("true", "false"), "boolean read constructor changed"
        wrong = deepcopy(actual)
        wrong[3][1] = "false" if actual[3][1] == "true" else "true"
        if duplicate:
            reads.append(wrong)
        else:
            actual[:] = wrong
        cases.append(Case(f"certificate-reads-{name}", canonical(tree), 0,
            canonical(["inquiry-result", "1", "verification",
                ["verification-body", ["invalid-certificate", ["false-read-evidence"]]]])))
    # Reads are a set of keys with universally checked values, not an ordered list.
    for name, change in [("reordered", lambda c: c[20].reverse()),
                          ("duplicated", lambda c: c[20].append(deepcopy(c[20][0]))),
                          ("opaque-input", lambda c: c.__setitem__(1, deepcopy(c[2])))]:
        tree = deepcopy(original)
        change(block(tree, "requests")[1][-1])
        cases.append(Case(f"certificate-valid-{name}", canonical(tree), 0,
            canonical(["inquiry-result", "1", "verification", ["verification-body", ["verified"]]])))


def syntax_cases(cases):
    for name, raw, detail in [
        ("empty-file", b"", "line 1, column 1: unexpected end of input"),
        ("unclosed-list", b"(", "line 1, column 2: unclosed list"),
        ("trailing-form", b"() ()", "line 1, column 4: expected a single S-expression, found more input"),
        ("backslash", b"\\", "line 1, column 1: unexpected character '\\'"),
        ("unicode-bare", "α".encode(), "line 1, column 1: unexpected character 'α'"),
        ("control-bare", b"\x01", "line 1, column 1: unexpected character '\x01'"),
        ("quoted-unicode-prefix", '"α" α'.encode(), "line 1, column 5: expected a single S-expression, found more input"),
        ("invalid-unicode-escape", '"α\\α"'.encode(), "line 1, column 3: invalid escape sequence \\α"),
    ]:
        cases.append(Case(name, raw, 2, error("syntax", detail)))
    cases.append(Case("reader-depth-at-boundary", b"(" * 10001 + b")" * 10001, 2,
                      error("malformed", "expected an inquiry-input document")))
    cases.append(Case("reader-depth-over-boundary", b"(" * 10002 + b")" * 10002, 2,
        error("syntax", "line 1, column 10002: maximum S-expression nesting depth exceeded (10000)")))

    # Unicode labels and escaped payloads preserve exact LF and UTF-8 bytes.
    tree = blank()
    block(tree[2], "queries").append(["verdict", 'α\\"\n\x01', ["predictable"]])
    output = canonical(["inquiry-result", "1", 'α\\"\n\x01',
        ["history-verdict", ["history-count", "1"], ["answer", 'α\\"\n\x01', "certainTrue", ["completions", "1"]]]])
    cases.append(Case("unicode-escaped-label", canonical(tree), 0, output))
