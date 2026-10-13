"""Decode captured wire answers and describe their finite diagnostic scope.

The real consumer remains a separate executable check. These projections only
read public result fields; they do not implement inquiry analyses or create
oracle answers. Construction-only information always has its own annotation.
"""
from __future__ import annotations

from collections import Counter, defaultdict

from evidence_measured import canonical, parse, wire
from inquiry_evaluation_manifest import digest, json_bytes, require

DRIVERS = ("native", "lean")
TRANSITIONS = ("accepted-to-accepted", "accepted-to-rejected",
               "rejected-to-accepted", "rejected-to-rejected")


def protocol(output, code):
    """The read-only conformance envelope and atomic refusal checks."""
    require(code in (0, 1, 2), f"unexpected exit: {code}")
    if not output:
        require(code == 0, "empty refusal")
        return []
    require(output.endswith(b"\n"), "missing final LF")
    lines = output.split(b"\n")[:-1]
    require(all(lines), "blank output line")
    forms = [parse(line) for line in lines]
    require(all(canonical(form) == line + b"\n" for form, line in zip(forms, lines)),
            "noncanonical wire bytes")
    if code == 0:
        require(all(isinstance(f, list) and f[:2] == ["inquiry-result", "1"] and len(f) == 4
                    and isinstance(f[2], str) and isinstance(f[3], list) and f[3]
                    and isinstance(f[3][0], str)
                    for f in forms), "wrong result envelope")
        for form in forms:
            body = form[3]
            if body[0] == "impact-body":
                require(len(body) == 2 and isinstance(body[1], list) and len(body[1]) == 5
                        and body[1][0] == "impact-result" and isinstance(body[1][1], list)
                        and len(body[1][1]) == 2 and body[1][1][0] == "transition"
                        and isinstance(body[1][1][1], str) and body[1][1][1] in TRANSITIONS,
                        "malformed impact transition")
    else:
        require(len(forms) == 1 and forms[0][:3] == ["inquiry-error", "1", []]
                and len(forms[0]) == 4, "partial results or multiple refusals")
        refusal = forms[0][3]
        require(isinstance(refusal, list) and refusal, "missing refusal kind")
        require(isinstance(refusal[0], str), "malformed refusal kind")
        require(code == (1 if refusal[0] in ("limit", "unsupported") else 2), "wrong refusal exit")
        if refusal[0] == "limit":
            require(len(refusal) == 4 and refusal[1][:1] == ["counter"] and len(refusal[1]) == 2 and refusal[1][1] in
                    ("histories", "sources", "source-bytes", "declarations", "search-steps", "pairs", "subsets")
                    and refusal[2][:1] == ["actual"] and refusal[3][:1] == ["cap"]
                    and len(refusal[2]) == len(refusal[3]) == 2
                    and all(isinstance(x, str) and x.isascii() and x.isdecimal() and str(int(x)) == x
                            for x in (refusal[2][1], refusal[3][1]))
                    and int(refusal[2][1]) > int(refusal[3][1]), "malformed counter refusal")
    return forms


def expected_forms(oracle):
    expected = oracle["expected"]
    if "results" in expected:
        return expected["results"]
    # Refusal fixtures may give the one parsed envelope explicitly.
    return [expected["refusal"]]


def option(value):
    require(isinstance(value, list) and len(value) <= 1, "invalid wire option")
    return value[0] if value else None


def boolean(value):
    require(value in ("true", "false"), "invalid wire boolean")
    return value == "true"


def buckets(rows):
    counts = Counter(wire(r[3][0]) for r in rows if r[3])
    return [{"rejection": parse(k), "row_count": v} for k, v in sorted(counts.items())]


def assignment(completion):
    return [[s[1], s[2][1]] for s in completion[2]]


def completion_key(completion):
    return wire([completion[1], assignment(completion)])


def request_catalog(document, label, fallback):
    # Catalog ownership is the document block, not the minimal request target.
    for block in document:
        if isinstance(block, list) and block and block[0] == "assumption-catalog":
            return block[1:]
    return fallback


def bound_certificate_evidence(document, forms, impact_label, annotations):
    """Join captured verification to exactly the submitted impact inputs.

    These are certificate fields validated by a captured verifier answer, not
    new checker telemetry. Matching also requires the ordered query list after
    resolving its existing claim bindings to atoms at the decode boundary.
    """
    requests = next((b[1:] for b in document if isinstance(b, list) and b and b[0] == "requests"), [])
    impact = next((r for r in requests if r[:2] == ["impact", impact_label]), None)
    if impact is None:
        return []
    bindings = next((b[1] for b in document if isinstance(b, list) and b and b[0] == "bindings"), [])
    atoms = {b[1]: b[3] for b in bindings if b[:1] == ["claim-binding"] and len(b) == 4}
    try:
        queries = [atoms[name] for name in impact[4][1:]]
    except KeyError:
        return []
    verified_labels = {f[2] for f in forms if f[:2] == ["inquiry-result", "1"]
                       and f[3] == ["verification-body", ["verified"]]}
    evidence = []
    for request in requests:
        if request[0] != "verify-impact" or request[1] not in verified_labels or len(request) != 5:
            continue
        cert = request[4]
        if (request[2:4] != impact[2:4] or not isinstance(cert, list) or len(cert) != 21 or
                cert[0] != "impact-certificate" or cert[1:3] != impact[2:4] or cert[3] != queries):
            continue
        reports = cert[8:10]
        require(all(isinstance(r, list) and len(r) == 8 and r[0] == "endpoint-report" for r in reports),
                "malformed submitted certificate endpoint reports")
        rejections = [option(r[2]) for r in reports]
        evidence.append({"verification_request": request[1], "certificate_sha256": digest(canonical(cert)),
                         "submitted_endpoint_reports": reports,
                         "submitted_endpoint_rejections": rejections,
                         "endpoint_accepted": [boolean(r[1]) for r in reports],
                         "reports_match_independent_annotations": annotations is not None and rejections == annotations,
                         "basis": "submitted certificate fields; validated by the captured verified result for the same ordered inputs and queries"})
    return evidence


def rejected_endpoint_comparison(transition, annotations, evidence):
    applicable = transition == "rejected-to-rejected"
    matching = [e for e in evidence if e["reports_match_independent_annotations"] and
                e["endpoint_accepted"] == [False, False] and all(r is not None for r in e["submitted_endpoint_rejections"])]
    known = applicable and bool(matching)
    return {"applicable": applicable, "comparison": (
                "equal" if matching[0]["submitted_endpoint_rejections"][0] == matching[0]["submitted_endpoint_rejections"][1]
                else "different") if known else ("unknown" if applicable else "inapplicable"),
            "exact_payload_equality": matching[0]["submitted_endpoint_rejections"][0] ==
                matching[0]["submitted_endpoint_rejections"][1] if known else None,
            "independent_annotation_available": annotations is not None,
            "bound_verification_available": bool(matching),
            "basis": "exact submitted certificate rejection payloads plus successful bound verification and matching independent annotations"}


def diagnostics(forms, document, oracle, case):
    """Each record is scoped to one captured request; aggregates deduplicate it."""
    records, snapshot = [], []
    family_status, family_audit = [], []
    spec = oracle["semantic_specification"]
    original_requests = next((b[1:] for b in document if isinstance(b, list) and b and b[0] == "requests"), [])
    process_document = next((b for b in document if isinstance(b, list) and b and b[0] == "process-input"), [])
    embedded_queries = next((b[1:] for b in process_document if isinstance(b, list) and b and b[0] == "queries"), [])
    for form in forms:
        if form[0] != "inquiry-result":
            continue
        label, body = form[2:]
        item = {"request": label, "body_kind": body[0], "denominator_scope": "this captured request"}
        original_request = next((r for r in original_requests if len(r) > 1 and r[1] == label), None)
        if original_request is None and body[0] == "history-verdict":
            original_request = next((q for q in embedded_queries if len(q) > 1 and q[1] == label), None)
        item["original_request_ast"] = original_request
        result = body[1]
        if body[0] in ("status-body", "audit-body"):
            rows = result[1]
            item.update(total_rows=int(result[2]), accepted_rows=int(result[3]),
                        rejected_rows=int(result[4]), exact_rejection_buckets=buckets(rows),
                        rows=[{"history": r[1], "assignment": r[2],
                               "rejection": option(r[3]),
                               "public_status" if body[0] == "status-body" else "fixed_witness_audit":
                               option(r[4])} for r in rows])
            if body[0] == "status-body":
                item["whole_status_stable"] = boolean(result[5])
                accepted = [option(r[4]) for r in rows if not r[3]]
                item["accepted_status_stable"] = bool(accepted) and all(s == accepted[0] for s in accepted)
                family_status.extend(rows)
                snapshot.extend({"request": label, "history": r[1], "assignment": r[2],
                                 "public_status": r[4][0]} for r in rows if r[4])
            else:
                item["declared_fixed_witness_input"] = {
                    "basis": "original input declaration; not runtime audit component telemetry",
                    "claim": original_request[2] if original_request is not None else None,
                    "submitted_witness": original_request[3] if original_request is not None else None,
                    "profile": original_request[4] if original_request is not None else None,
                    "independent_component_annotation_available": "audit_components" in spec}
                item["universal_fixed_witness_audit"] = boolean(result[5])
                item["true_rows"] = sum(r[4] == ["true"] for r in rows)
                item["false_rows"] = sum(r[4] == ["false"] for r in rows)
                item["audit_value_denominator"] = sum(bool(r[4]) for r in rows)
                family_audit.extend(rows)
        elif body[0] == "stability-body":
            item.update(observable=result[1], total_rows=int(result[2]), accepted_rows=int(result[3]),
                        rejected_rows=int(result[4]), whole_outcome_stable=boolean(result[5]),
                        accepted_only_stable=boolean(result[6]))
        elif body[0] in ("sensitivity-body", "slots-sensitive-body"):
            reference = result[2]
            differing = result[5]
            same_history = [r for r in differing if r[1][1] == reference[1]]
            minima = result[6]
            item.update(observable=result[1], reference=reference, total_rows=int(result[3]),
                        total_flips=int(result[4]), differing_rows=differing,
                        same_history_flips=len(same_history),
                        same_history_denominator="differing rows in this request",
                        nonempty_minimal_slot_sets=[s for s in minima if s],
                        minimal_cardinalities=[len(s) for s in minima if s],
                        first_declaration_order_realizers=result[7])
            # Membership is visible when the same capture includes family rows.
            available = [r for f in forms if f[0] == "inquiry-result" and f[3][0] in
                         ("status-body", "audit-body") for r in f[3][1][1]]
            item["reference_membership_from_captured_family"] = (
                any(r[1] == reference[1] and r[2] == assignment(reference) for r in available)
                if available else None)
            item["reference_membership_annotation"] = {
                "basis": "independently reviewed finite construction; not a runtime flag",
                "value": any(r.get("history") == reference[1] and
                             [[int(a[0][1]), int(a[1][1])] for a in assignment(reference)] == r.get("choices")
                             for r in spec.get("rows", []) if "history" in r) if
                any("history" in r for r in spec.get("rows", [])) else None}
        elif body[0] == "assumptions-body":
            captured_catalog = result[2]
            # The public result retains the original catalog. The enumeration
            # uses structural retain-last deduplication, which is a projection
            # of that field, not an instrumented enumeration count.
            catalog = [literal for index, literal in enumerate(captured_catalog)
                       if literal not in captured_catalog[index + 1:]]
            raw_catalog = request_catalog(document, label, case["catalog"])
            minima = result[4]
            item.update(target=result[1], catalog_before_dedup=raw_catalog,
                        catalog_before_count=len(raw_catalog), captured_catalog=captured_catalog,
                        catalog_after_dedup=catalog,
                        catalog_after_count=len(catalog), total_rows=int(result[3]),
                        subsets_examined={"value": 2 ** len(catalog),
                                          "basis": "derived finite catalog power-set size; not runtime telemetry"},
                        minimal_sets=[{"literals": m[1], "surviving_rows": len(m[2]),
                                       "surviving_completions": m[2], "deletions":
                                       [{"literal": d[1], "surviving_rows": len(d[2]),
                                         "surviving_completions": d[2], "countercompletion": option(d[3])}
                                        for d in m[3]]} for m in minima])
        elif body[0] == "impact-body":
            rows = result[2]
            transition = result[1][1]
            item.update(acceptance_class=transition, changed_queries=result[3], unchanged_queries=result[4],
                        query_denominator=len(rows), queries=[])
            for row in rows:
                before, after = option(row[2]), option(row[3])
                locality = boolean(row[5])
                status_comparison_applicable = (transition == "accepted-to-accepted" and
                                               before is not None and after is not None)
                equal = before == after if status_comparison_applicable else None
                equal_blocking = (status_comparison_applicable and
                                  (before[0] == "evidence-blocked") == (after[0] == "evidence-blocked"))
                certified = locality and equal_blocking
                item["queries"].append({"query": row[1], "before_public_status": before,
                                        "after_public_status": after, "changed": boolean(row[4]),
                                        "full_status_comparison_applicable": status_comparison_applicable,
                                        "actually_equal_full_status": equal,
                                        "grounded_locality": locality,
                                        "certified_unchanged": certified, "equal_blocking": equal_blocking,
                                        "blocked_conditional_change": bool(before and after and
                                            before[0] == after[0] == "evidence-blocked" and before != after),
                                        "locality_counterexample": certified and equal is False})
                for endpoint, status in (("before", before), ("after", after)):
                    if status is not None:
                        snapshot.append({"request": label, "query": row[1], "endpoint": endpoint,
                                         "public_status": status})
            annotations = spec.get("rejections")
            certificate_evidence = bound_certificate_evidence(document, forms, label, annotations)
            item["rejection_annotations"] = {
                "basis": "independent reviewed endpoint annotation; impact wire omits exact payloads",
                "annotation_available": "rejections" in spec,
                "before": spec.get("rejections", [None, None])[0],
                "after": spec.get("rejections", [None, None])[1],
                "verified_by_captured_endpoint_certificate": any(
                    e["reports_match_independent_annotations"] for e in certificate_evidence),
                "bound_certificate_evidence": certificate_evidence,
            }
            item["rejected_endpoint_comparison"] = rejected_endpoint_comparison(transition, annotations, certificate_evidence)
        elif body[0] == "verification-body":
            item["verification"] = result
        elif body[0] == "history-verdict":
            item["history_verdict"] = body[1:]
        item["captured_body_sha256"] = digest(canonical(body))
        records.append(item)
    audit_by_row = {wire([r[1], r[2]]): option(r[4]) for r in family_audit}
    groups = defaultdict(list)
    for r in family_status:
        if r[4]:
            key = wire([r[1], r[2]])
            if key in audit_by_row:
                groups[wire(r[4][0])].append({"history": r[1], "assignment": r[2], "audit": audit_by_row[key]})
    contrasts = [{"public_status": parse(k), "rows": values} for k, values in groups.items()
                 if len({wire(v["audit"]) if isinstance(v["audit"], list) else str(v["audit"]) for v in values}) > 1]
    # Join actual status rows to reviewed construction rows by their complete
    # history and assignment. This exposes annotation differences without
    # treating capture binding or literal truth tables as driver telemetry.
    annotated_status_groups = defaultdict(list)
    for r in family_status:
        if not r[4]:
            continue
        for index, annotation in enumerate(spec.get("rows", [])):
            if annotation.get("history") == r[1] and annotation.get("choices") == [
                    [int(a[0][1]), int(a[1][1])] for a in r[2]]:
                truth = next((t["values"] for t in spec.get("assumption_truth_table", []) if t["row"] == index), None)
                components = next((t for t in spec.get("audit_components", []) if t["row"] == index), {})
                bindings = {k: v for k, v in components.items() if "capture" in k or "binding" in k}
                annotated_status_groups[wire(r[4][0])].append({"construction_row": index,
                    "assumption_values": truth, "capture_and_binding_annotations": bindings})
    annotation_contrasts = [{"public_status": parse(k), "rows": values}
        for k, values in annotated_status_groups.items() if
        len({json_bytes({key: v[key] for key in ("assumption_values", "capture_and_binding_annotations")})
             for v in values}) > 1]
    annotations = {key: spec[key] for key in ("bindings", "kind_metadata", "admitted_assumptions",
                   "audit_profile", "coverage_annotation", "audit_components", "annotation_boundary",
                   "catalog_subsets", "assumption_truth_table") if key in spec}
    input_annotations = {b[0]: b for b in document if isinstance(b, list) and b and b[0] in
                         ("bindings", "kind-metadata", "admitted-assumptions", "assumption-catalog")}
    process = next((b for b in document if isinstance(b, list) and b and b[0] == "process-input"), None)
    if process is not None:
        input_annotations["process_input"] = process
        input_annotations["reader"] = next((b for b in process if isinstance(b, list) and b and b[0] == "reader"), None)
    return {"requests": records, "snapshot_only": {
                "basis": "public statuses from this exact capture", "rows": snapshot,
                "visible_fields": ["public_status", "row_or_endpoint_identity"],
                "public_status_row_count": len(snapshot),
                "captured_request_count": len(records),
                "captured_diagnostic_body_kinds": sorted({r["body_kind"] for r in records}),
                "omitted_diagnostics": ["family rejection and stability", "fixed-witness audit",
                    "sensitivity", "assumptions", "dependency and source-transition diagnostics"],
                "agent_performance_measured": False},
            "same_full_status_different_audit": contrasts,
            "same_full_status_different_assumptions_or_capture_annotations": {
                "basis": "captured full statuses joined to independent construction annotations",
                "groups": annotation_contrasts},
            "construction_annotations": {"basis": "independently reviewed construction; not runtime telemetry",
                                          "values": annotations,
                                          "independent_audit_components_available": "audit_components" in spec},
            "declared_input_annotations": {
                "basis": "original declared configuration and reader coverage; not inferred completeness or grade telemetry",
                "values": input_annotations}}


def score_case(case, oracle, document, captures):
    result = {"case_id": case["case_id"], "stratum": case["stratum"],
              "input_sha256": case["input_sha256"], "source_ancestry": case["source_ancestry"],
              "original_input_bytes": len(document), "expected_logical_counters": case["expected_counters"],
              "effective_declared_limits": case["effective_declared_limits"],
              "oracle": {"expected": oracle["expected"], "review_provenance": oracle["review_provenance"]},
              "drivers": {}}
    forms_by_driver = {}
    for name in DRIVERS:
        if name not in captures:
            result["drivers"][name] = {"invoked": False, "oracle_agreement": False,
                                         "consumer_accepted": False}
            continue
        record, stdout, stderr = captures[name]
        item = {"invoked": True, "invocation": record, "protocol_valid": False,
                "oracle_agreement": False, "consumer_accepted": record.get("consumer", {}).get("accepted", False),
                "decoded_results": None, "actual_counter_refusal": None}
        try:
            require(not record.get("driver_failure", record["failure"]),
                    f"driver infrastructure failure: {record.get('driver_failure', record['failure'])}")
            forms = protocol(stdout, record["exit_code"])
            item["protocol_valid"] = True
            item["decoded_results"] = forms
            forms_by_driver[name] = forms
            actual_kind = "results" if record["exit_code"] == 0 else forms[0][3][0]
            item["result_kind"] = actual_kind
            item["oracle_agreement"] = (forms == expected_forms(oracle) and
                record["exit_code"] == oracle["expected"]["exit_code"] and
                actual_kind == oracle["expected"]["result_kind"] and not stderr)
            if actual_kind == "limit":
                refusal = forms[0][3]
                item["actual_counter_refusal"] = {"counter": refusal[1][1], "actual": int(refusal[2][1]), "cap": int(refusal[3][1])}
            item["diagnostics"] = diagnostics(forms, parse(document), oracle, case)
        except (ValueError, TypeError, IndexError, KeyError, UnicodeError, RecursionError) as exc:
            item["decode_error"] = str(exc)
            item["decode_error_kind"] = type(exc).__name__
            item["oracle_agreement"] = False
        result["drivers"][name] = item
    result["driver_agreement"] = (len(forms_by_driver) == 2 and
                                   forms_by_driver["native"] == forms_by_driver["lean"] and
                                   captures["native"][0]["exit_code"] == captures["lean"][0]["exit_code"])
    result["locality_sound"] = all(not q["locality_counterexample"]
        for d in result["drivers"].values() for r in d.get("diagnostics", {}).get("requests", [])
        if r["body_kind"] == "impact-body" for q in r["queries"])
    return result


def ratio(numerator, denominator, scope):
    return {"numerator": numerator, "denominator": denominator, "scope": scope,
            "fraction": numerator / denominator if denominator else None}


def process_counts(records, *, consumer=False):
    denominator = len(records)
    failures = [r.get("failure") if consumer else r.get("driver_failure", r.get("failure")) for r in records]
    if consumer:
        failures = [failure or (None if r.get("accepted") else "consumer-refusal-or-noisy-output")
                    for r, failure in zip(records, failures)]
    return {"invocation_attempt_denominator": denominator,
            "scope": "actual recorded process attempts, including spawn failures; no missing invocations",
            "process_started_count": sum(r.get("process_started", r.get("exit_code") is not None) for r in records),
            "timeouts": ratio(sum(bool(r.get("timeout")) for r in records), denominator, "recorded invocation attempts"),
            "all_signaled_processes": ratio(sum(r.get("signal") is not None for r in records), denominator,
                                           "recorded invocation attempts; includes timeout-induced kills"),
            "independent_signal_failures": ratio(sum(f == "signal" for f in failures), denominator,
                                                 "recorded invocation attempts; excludes timeout-induced kills"),
            "spawn_failures": ratio(sum(r.get("spawn_failure") is not None for r in records), denominator,
                                    "recorded invocation attempts"),
            "completed_without_infrastructure_failure": ratio(sum(f is None and r.get("exit_code") is not None
                for r, f in zip(records, failures)), denominator, "recorded invocation attempts"),
            "primary_failure_counts": dict(Counter(f for f in failures if f is not None))}


def summary(results, manifest, run):
    by_hash = defaultdict(list)
    for row in results:
        by_hash[row["input_sha256"]].append(row)
    correctness = {}
    validated_correctness = {}
    for scope in ("all", "development_controls", "authored_controls", "generated_variants", "new_inputs"):
        selected = {h: [r for r in rows if scope == "all" or r["stratum"] == scope or
                       (scope == "new_inputs" and r["stratum"] != "development_controls")]
                    for h, rows in by_hash.items()}
        selected = {h: rows for h, rows in selected.items() if rows}
        correctness[scope] = {d: ratio(sum(all(r["drivers"][d]["oracle_agreement"] for r in rows)
                for rows in selected.values()), len(selected), "unique input hashes; every duplicate capture must agree")
                for d in DRIVERS}
        correctness[scope]["documents"] = sum(len(rows) for rows in selected.values())
        validated_correctness[scope] = {d: ratio(sum(all(
            r["drivers"][d]["oracle_agreement"] and r["drivers"][d]["consumer_accepted"] and
            r["drivers"][d].get("protocol_valid", False) for r in rows) for rows in selected.values()),
            len(selected), "unique input hashes; every duplicate capture must match the oracle and pass protocol and consumer checks")
            for d in DRIVERS}
        validated_correctness[scope]["documents"] = sum(len(rows) for rows in selected.values())
    totals = {}
    diagnostic_strata = {}
    for driver in DRIVERS:
        projections = {}
        request_count = 0
        for row in results:
            for request in row["drivers"][driver].get("diagnostics", {}).get("requests", []):
                request_count += 1
                projections.setdefault(request["captured_body_sha256"], request)
        requests = list(projections.values())
        impacts = [r for r in requests if r["body_kind"] == "impact-body"]
        aa = [q for r in impacts if r["acceptance_class"] == "accepted-to-accepted" for q in r["queries"]]
        comparable = [q for q in aa if q["full_status_comparison_applicable"]]
        certified = [q for q in aa if q["certified_unchanged"]]
        grounded_local = [q for q in aa if q["grounded_locality"]]
        transitions = Counter(r["acceptance_class"] for r in impacts)
        # Equal public bodies can come from different endpoint pairs and review
        # contexts. Rejection-payload evidence therefore has its own contextual
        # denominator, rather than inheriting public-body-only deduplication.
        rejected_contexts = {}
        rejected_request_count = 0
        for row in results:
            for request in row["drivers"][driver].get("diagnostics", {}).get("requests", []):
                if request.get("acceptance_class") == "rejected-to-rejected":
                    rejected_request_count += 1
                    context = {"input_sha256": row["input_sha256"],
                               "captured_body_sha256": request["captured_body_sha256"],
                               "rejection_annotations": request["rejection_annotations"]}
                    rejected_contexts.setdefault(digest(json_bytes(context)), request["rejected_endpoint_comparison"])
        rejected_pairs = list(rejected_contexts.values())
        driver_records = [row["drivers"][driver]["invocation"] for row in results if row["drivers"][driver]["invoked"]]
        consumer_records = [r["consumer"] for r in driver_records if "consumer" in r]
        totals[driver] = {"denominator_scope": "deduplicated captured request bodies; correlated variants remain descriptive",
            "captured_requests": request_count, "unique_request_body_projections": len(requests),
            "acceptance_classes": {t: transitions[t] for t in TRANSITIONS},
            "acceptance_class_denominator": len(impacts),
            "rejected_endpoint_comparison_counts": {key: sum(r["comparison"] == key for r in rejected_pairs)
                for key in ("equal", "different", "unknown")},
            "rejected_endpoint_comparison_denominator": len(rejected_pairs),
            "rejected_endpoint_captured_request_denominator": rejected_request_count,
            "rejected_endpoint_comparison_scope": "unique input hash and captured request projection with its bound verification and annotation context",
            "accepted_to_accepted_query_denominator": len(aa),
            "full_status_applicable_query_denominator": len(comparable),
            "certified_unchanged": ratio(len(certified), len(aa), "accepted-to-accepted query rows"),
            "actually_unchanged": ratio(sum(q["actually_equal_full_status"] is True for q in comparable),
                len(comparable), "accepted-to-accepted query rows with both public statuses present"),
            "grounded_locality": ratio(len(grounded_local), len(aa), "accepted-to-accepted query rows"),
            "equal_blocking_when_grounded_local": ratio(sum(q["equal_blocking"] for q in grounded_local),
                len(grounded_local), "query rows satisfying grounded locality"),
            "grounded_locality_with_changed_blocking": sum(not q["equal_blocking"] for q in grounded_local),
            "certified_counterexamples": sum(q["locality_counterexample"] for q in aa),
            "blocked_conditional_changes": sum(q["blocked_conditional_change"] for q in aa),
            "changed_full_status": sum(q["actually_equal_full_status"] is False for q in comparable),
            "unchanged_full_status": sum(q["actually_equal_full_status"] is True for q in comparable),
            "consumer_accepted": ratio(sum(r["drivers"][driver]["consumer_accepted"] for r in results), len(results), "manifest documents"),
            "driver_processes": process_counts(driver_records),
            "consumer_processes": process_counts(consumer_records, consumer=True),
            "operation_counts": dict(Counter(r["drivers"][driver].get("result_kind", "not-completed") for r in results)),
            "infrastructure_failures": dict(Counter(r["drivers"][driver].get("invocation", {}).get("failure")
                for r in results if r["drivers"][driver].get("invocation", {}).get("failure")))}
        diagnostic_strata[driver] = {}
        for stratum in ("development_controls", "authored_controls", "generated_variants"):
            selected_rows = [r for r in results if r["stratum"] == stratum]
            selected_requests = [request for row in selected_rows for request in
                row["drivers"][driver].get("diagnostics", {}).get("requests", [])]
            projected = {}
            for request in selected_requests:
                projected.setdefault(request["captured_body_sha256"], request)
            impacts_in_stratum = [r for r in projected.values() if r["body_kind"] == "impact-body"]
            class_counts = Counter(r["acceptance_class"] for r in impacts_in_stratum)
            diagnostic_strata[driver][stratum] = {
                "manifest_documents": len(selected_rows),
                "unique_input_hashes": len({r["input_sha256"] for r in selected_rows}),
                "captured_request_denominator": len(selected_requests),
                "unique_request_body_projection_denominator": len(projected),
                "acceptance_classes": {t: class_counts[t] for t in TRANSITIONS},
                "acceptance_class_denominator": len(impacts_in_stratum),
                "scope": "deduplicated captured request bodies within this stratum; descriptive correlated projections"}
    complete = run["completion"] == "COMPLETE" and not run["missing_invocations"]
    passed = complete and all(r["locality_sound"] and all(r["drivers"][d]["oracle_agreement"] and
               r["drivers"][d]["consumer_accepted"] for d in DRIVERS) for r in results)
    return {"schema": "inquiry-p8-summary", "schema_version": 1,
            "run_id": run["run_id"], "completion": run["completion"], "passed": passed,
            "document_partition": manifest["expected_partition"], "unique_inputs": len(by_hash),
            "duplicate_content_groups": manifest["duplicate_content_groups"],
            "variant_disclosure": "Generated variants are correlated with their seeds. Repeated requests do not add semantic evidence.",
            "oracle_correctness": correctness, "validated_correctness": validated_correctness,
            "drivers": totals, "diagnostic_strata": diagnostic_strata,
            "driver_agreement": ratio(sum(r["driver_agreement"] for r in results), len(results), "manifest documents"),
            "missing_invocations": run["missing_invocations"],
            "unattached_capture_paths": run.get("unattached_capture_paths", []),
            "aggregate_elapsed_ms": run["aggregate_elapsed_ms"],
            "claims_excluded": ["speedup", "confidence interval", "asymptotic performance", "agent success"]}


def report_bytes(results, report):
    lines = ["case\tstratum\tdriver\tinput_bytes\texpected_counters_json\tresult_kind\toracle_agreement\tconsumer_accepted\telapsed_ms\tfailure"]
    for row in results:
        for driver in DRIVERS:
            item = row["drivers"][driver]
            invocation = item.get("invocation", {})
            fields = [row["case_id"], row["stratum"], driver, str(row["original_input_bytes"]),
                      json_bytes(row["expected_logical_counters"]).decode().strip(),
                      item.get("result_kind", "not-completed"), str(item["oracle_agreement"]).lower(),
                      str(item["consumer_accepted"]).lower(), str(invocation.get("elapsed_ms", "")),
                      invocation.get("failure") or ""]
            lines.append("\t".join(fields))
    return {"results.jsonl": b"".join(json_bytes(r) for r in results),
            "summary.json": json_bytes(report), "summary.tsv": ("\n".join(lines) + "\n").encode()}
