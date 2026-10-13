"""Read-only freeze validation for the bounded inquiry measurement.

This module reads annotations and digests. It never constructs an expected
answer and never imports an inquiry implementation or fixture generator.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT_COMMIT = "95f63bf"
# Protocol status for an item whose approval lives only in the correction receipt.
RECEIPT_APPROVAL = "requires-correction-receipt"


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=False) + "\n").encode("utf-8")


def read_json(path):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate JSON key {key}: {path}")
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def safe_path(root, relative):
    path = Path(relative)
    require(not path.is_absolute() and ".." not in path.parts,
            f"unsafe evidence path: {relative}")
    result = root / path
    require(not any(p.is_symlink() for p in [result, *result.parents]
                    if p != root.parent), f"symlink evidence: {result}")
    return result


def checked(root, relative, expected, inventory):
    path = safe_path(root, relative)
    data = path.read_bytes()
    require(digest(data) == expected, f"hash mismatch: {path}")
    inventory[relative] = expected
    return data


def semantic_digest(oracle):
    return digest(json_bytes({"expected": oracle["expected"],
                              "semantic_specification": oracle["semantic_specification"]}))


def approved_protocol_identity(protocol):
    """Retain all approved fields except the enumerated freeze receipt metadata."""
    identity = {k: v for k, v in protocol.items() if k not in ('freeze', 'correction_approval')}
    identity['freeze'] = {k: v for k, v in protocol['freeze'].items()
                          if k not in ('state', 'manifest_sha256')}
    identity['correction_approval'] = {k: v for k, v in protocol.get('correction_approval', {}).items()
                                      if k not in ('state', 'path', 'sha256')}
    return identity


def require_receipt_approvals(protocol, receipt):
    """Require the receipt to approve every protocol item that defers to it.

    The approved protocol is frozen byte for byte, so an amendment or data
    policy awaiting the researcher cannot record its own approval. It is
    marked RECEIPT_APPROVAL instead, and the receipt binds its exact meaning.
    """
    entries = receipt.get("approved_amendments", [])
    require(isinstance(entries, list) and
            all(isinstance(e, dict) and isinstance(e.get("id"), str) for e in entries),
            "correction receipt approved_amendments is not a list of objects with string ids")
    ids = [e.get("id") for e in entries]
    require(len(ids) == len(set(ids)), "correction receipt repeats an amendment id")
    approved = dict(zip(ids, entries))
    stated = lambda text: isinstance(text, str) and bool(text.strip())
    for amendment in protocol.get("amendments", []):
        if amendment.get("status") == RECEIPT_APPROVAL:
            entry = approved.get(amendment["id"], {})
            require(stated(entry.get("approval_text")) and entry.get("interpretation_sha256")
                    == digest(amendment["interpretation"].encode("utf-8")),
                    f"correction receipt does not approve amendment: {amendment['id']}")
        else:
            require(amendment.get("provenance") == "user" and stated(amendment.get("approval_text")),
                    f"amendment lacks researcher approval: {amendment.get('id')}")
    if "data_policy" in protocol:
        policy = protocol["data_policy"]
        require(isinstance(policy, dict) and policy.get("state") == RECEIPT_APPROVAL and
                receipt.get("data_policy_sha256") == digest(json_bytes(policy)),
                "correction receipt does not approve the data policy")


def load_suite(manifest_path):
    """Validate all frozen suite bytes before any driver is selected or spawned."""
    manifest_path = manifest_path.resolve()
    base = manifest_path.parent
    protocol = read_json(base / "protocol.json")
    require(protocol["schema"] == "inquiry-p8-protocol" and protocol["schema_version"] == 1,
            "unsupported protocol schema")
    require(protocol["recipes"]["version"] in ("inquiry-p8-recipes@1", "inquiry-p8-recipes@2-candidate"), "unsupported recipe version")
    require(protocol["freeze"]["state"] == "frozen", "protocol is not frozen")
    inventory = {"protocol.json": digest((base / "protocol.json").read_bytes())}
    checked(base, manifest_path.name, protocol["freeze"]["manifest_sha256"], inventory)
    if protocol["recipes"]["version"] != "inquiry-p8-recipes@1":
        approval = protocol.get("correction_approval", {})
        require(approval.get("state") == "approved", "corrected protocol lacks researcher approval")
        receipt = read_json(safe_path(base, approval["path"]))
        checked(base, approval["path"], approval["sha256"], inventory)
        require(receipt.get("status") == "APPROVED" and receipt.get("provenance") == "user"
                and bool(receipt.get("researcher")), "correction receipt lacks researcher approval")
        snapshot = read_json(safe_path(base, receipt["candidate_protocol_path"]))
        checked(base, receipt["candidate_protocol_path"], receipt["candidate_protocol_sha256"], inventory)
        # Reviews and authoring bindings are complete before approval. Only the
        # freeze state/hash and researcher receipt linkage may change afterward.
        require(approved_protocol_identity(snapshot) == approved_protocol_identity(protocol),
                "approved candidate protocol changed")
        require(receipt.get("metadata_only_freeze_authorized") is True and
                re.fullmatch(r"[0-9a-f]{40}", receipt.get("reviewed_candidate_commit", "")),
                "correction approval does not bind committed candidate/freeze scope")
    manifest = read_json(manifest_path)
    if protocol["recipes"]["version"] != "inquiry-p8-recipes@1":
        candidate_manifest = read_json(safe_path(base, receipt["candidate_manifest_path"]))
        checked(base, receipt["candidate_manifest_path"], receipt["candidate_manifest_sha256"], inventory)
        stable_manifest = lambda m: {k: v for k, v in m.items() if k != "state"}
        require(stable_manifest(candidate_manifest) == stable_manifest(manifest),
                "approved candidate inputs, annotations, reviews or construction changed")
        require_receipt_approvals(protocol, receipt)
    require(manifest["schema"] == "inquiry-p8-manifest" and manifest["schema_version"] == 1,
            "unsupported manifest schema")
    require(manifest["state"] == "frozen", "manifest is not frozen")
    require(manifest["code_commit"] == protocol["code_commit"], "code pin mismatch")
    budget = protocol["budget"]
    require((budget["max_documents"], budget["max_driver_invocations"],
             budget["invocations_per_driver_per_document"], budget["driver_timeout_seconds"],
             budget["aggregate_deadline_seconds"], budget["cpu_allocation"], budget["repeats"])
            == (96, 192, 1, 10, 2700, 1, 0), "unapproved measurement budget")
    cases = manifest["cases"]
    partition = dict(Counter(c["stratum"] for c in cases), total=len(cases))
    require(partition == manifest["expected_partition"] == protocol["partition"]
            == {"development_controls": 16, "authored_controls": 16,
                "generated_variants": 64, "total": 96}, "incomplete or changed partition")
    ids = [c["case_id"] for c in cases]
    require(len(ids) == len(set(ids)) and all(re.fullmatch(r"[A-Za-z0-9_-]+", x) for x in ids),
            "duplicate or unsafe case ID")
    for item in protocol["freeze"]["supporting_artifacts"]:
        checked(base, item["path"], item["sha256"], inventory)
    for name in ("independent_review", "quality_review"):
        item = manifest[name]
        checked(base, item["path"], item["sha256"], inventory)
        require(read_json(base / item["path"])["status"] == "PASS", f"{name} did not pass")
    review = read_json(base / manifest["independent_review"]["path"])
    require(not review["driver_outputs_used"] and not review["analysis_implementation_imported"],
            "review independence is not established")
    evidence = {e["case_id"]: e for e in review["case_evidence"] + review["development_control_evidence"]}
    require(set(evidence) == set(ids), "review does not cover the partition")
    oracles = {}
    groups = defaultdict(list)
    for case in cases:
        for key in manifest["case_fields_required"]:
            require(key in case, f"missing {key}: {case['case_id']}")
        name = case["case_id"]
        checked(base, case["input_path"], case["input_sha256"], inventory)
        checked(base, case["oracle_path"], case["oracle_sha256"], inventory)
        oracle = read_json(base / case["oracle_path"])
        require(oracle["case_id"] == name, f"wrong oracle identity: {name}")
        provenance = oracle["review_provenance"]
        require(provenance == case["review_provenance"], f"provenance mismatch: {name}")
        require(provenance["status"] == ("disclosed-development-control" if
                case["stratum"] == "development_controls" else "independently-reviewed"),
                f"unreviewed case: {name}")
        require(provenance["reviewed_input_sha256"] == case["input_sha256"]
                == evidence[name]["input_sha256"], f"reviewed input mismatch: {name}")
        require(provenance["semantic_content_sha256"] == semantic_digest(oracle)
                == evidence[name]["semantic_content_sha256"], f"reviewed meaning mismatch: {name}")
        require(provenance["review_sha256"] == manifest["independent_review"]["sha256"] and
                provenance["quality_review_sha256"] == manifest["quality_review"]["sha256"],
                f"review receipt mismatch: {name}")
        require(not provenance["driver_output_used"] and not provenance["analysis_implementation_imported"],
                f"oracle independence mismatch: {name}")
        if protocol["recipes"]["version"] != "inquiry-p8-recipes@1":
            require(case["authored_semantic_content_sha256"] == semantic_digest(oracle),
                    f"approved candidate meaning mismatch: {name}")
        require(oracle["expected"]["result_kind"] == case["expected_result_kind"],
                f"expected kind mismatch: {name}")
        cert = oracle["semantic_specification"].get("certificate_provenance")
        if cert:
            checked(base, cert["artifact_path"], cert["artifact_sha256"], inventory)
        oracles[name] = oracle
        groups[case["input_sha256"]].append(name)
    duplicates = [{"input_sha256": h, "case_ids": names} for h, names in groups.items() if len(names) > 1]
    require(duplicates == manifest["duplicate_content_groups"] and len(groups) == manifest["unique_input_count"],
            "duplicate disclosure mismatch")
    return base, protocol, manifest, oracles, inventory


def git(*args, cwd=ROOT):
    result = subprocess.run(["git", *args], cwd=cwd, capture_output=True, timeout=60)
    require(result.returncode == 0, f"git preflight failed: {args}: {result.stderr.decode(errors='replace')}")
    return result.stdout


def tracked_blobs(commit, path):
    records = []
    for raw in git("ls-tree", "-rz", commit, "--", path).split(b"\0"):
        if raw:
            header, name = raw.split(b"\t", 1)
            mode, kind, object_id = header.decode().split()
            records.append((mode, kind, object_id, name.decode("utf-8")))
    return records


def current_blob(mode, path):
    p = ROOT / path
    if mode == "120000":
        require(p.is_symlink(), f"changed symlink: {path}")
        return os.readlink(p).encode("utf-8")
    require(p.is_file() and not p.is_symlink(), f"missing or replaced code/input file: {path}")
    return p.read_bytes()


def repository_preflight(protocol, suite_base, suite_inventory, input_commit_pin=None):
    """Check committed identities and current bytes, ignoring unrelated work."""
    commit = protocol["code_commit"]
    for path, object_id in protocol["code_paths"].items():
        require(git("rev-parse", f"{commit}:{path}").decode().strip() == object_id,
                f"code Git object mismatch: {path}")
        for mode, kind, oid, filename in tracked_blobs(commit, path):
            if kind == "blob":
                require(current_blob(mode, filename) == git("cat-file", "blob", oid),
                        f"runtime code changed: {filename}")
        require(not git("ls-files", "--others", "--exclude-standard", "--", path).strip(),
                f"untracked runtime code in {path}")
        require(not git("diff", "--name-only", commit, "--", path).strip(),
                f"runtime path differs from pinned commit: {path}")
    corrected = protocol["recipes"]["version"] != "inquiry-p8-recipes@1"
    require(not corrected or input_commit_pin is not None, "corrected suite requires explicit --input-commit")
    require(not corrected or re.fullmatch(r"[0-9a-f]{40}", input_commit_pin), "corrected suite requires a full committed input identity")
    require(corrected or input_commit_pin in (None, INPUT_COMMIT) or
            git("rev-parse", input_commit_pin) == git("rev-parse", INPUT_COMMIT),
            "original suite input pin cannot change")
    input_commit = git("rev-parse", input_commit_pin or INPUT_COMMIT).decode().strip()
    if corrected:
        approval = read_json(suite_base / protocol["correction_approval"]["path"])
        candidate_commit = approval["reviewed_candidate_commit"]
        git("merge-base", "--is-ancestor", candidate_commit, input_commit)
        relative = suite_base.relative_to(ROOT).as_posix()
        for name, key in (("protocol.json", "candidate_protocol_sha256"),
                          ("MANIFEST.json", "candidate_manifest_sha256")):
            require(digest(git("show", f"{candidate_commit}:{relative}/{name}")) == approval[key],
                    "approved candidate commit/hash mismatch: " + name)
    relative_base = suite_base.relative_to(ROOT)
    for path in suite_inventory:
        relative = (relative_base / path).as_posix()
        require(git("show", f"{input_commit}:{relative}") == (suite_base / path).read_bytes(),
                f"input freeze commit mismatch: {relative}")
    recipe = protocol["recipes"]
    helper_inventory = {}
    for path, expected in [(recipe["generator_path"], recipe["generator_sha256"]),
                           (recipe.get("independent_audit_tool_path", "evaluation/inquiry-p8/review/independent_finite_audit.py"),
                            recipe["independent_audit_tool_sha256"]),
                           (recipe["certificate_producer_path"], recipe["certificate_producer_sha256"])]:
        checked(ROOT, path, expected, helper_inventory)
    quality = read_json(suite_base / "quality-review.json")
    for path_key, hash_key in (("generator_path", "generator_sha256"),
                               ("audit_tool_path", "audit_tool_sha256"),
                               ("boundary_test_path", "boundary_test_sha256")):
        checked(ROOT, quality[path_key], quality[hash_key], helper_inventory)
    for item in protocol["legacy_inputs"]["trees"]:
        require(git("rev-parse", f"{commit}:{item['path']}").decode().strip() == item["git_tree"],
                f"legacy tree object changed: {item['path']}")
        records = []
        for mode, kind, oid, filename in tracked_blobs(commit, item["path"]):
            if kind == "blob":
                data = current_blob(mode, filename)
                require(data == git("cat-file", "blob", oid), f"legacy input changed: {filename}")
                records.append({"path": filename, "sha256": digest(data)})
        require(len(records) == item["tracked_file_count"] and
                digest(json_bytes(sorted(records, key=lambda r: r["path"]))) == item["file_inventory_sha256"],
                f"legacy inventory mismatch: {item['path']}")
        for link in item["gitlinks"]:
            checkout = ROOT / link["path"]
            require(git("rev-parse", "HEAD", cwd=checkout).decode().strip() == link["git_commit"] and
                    git("rev-parse", "HEAD^{tree}", cwd=checkout).decode().strip() == link["git_tree"] and
                    not git("status", "--porcelain", cwd=checkout).strip(), f"legacy gitlink changed: {link['path']}")
    for tag, oid in protocol["legacy_inputs"]["freeze_tags"].items():
        require(git("rev-parse", tag).decode().strip() == oid, f"legacy freeze tag changed: {tag}")
    # The approval plan is checked by Git blob identity; reading its contents is
    # unnecessary for measurement and would couple this runner to a living plan.
    approval = protocol["approval"]
    require(git("rev-parse", f"{approval['approval_commit']}:{approval['plan_path']}").decode().strip()
            == approval["plan_git_blob"], "approval plan identity changed")
    for item in recipe.get("additional_helpers", []):
        checked(ROOT, item["path"], item["sha256"], helper_inventory)
    return input_commit, helper_inventory
