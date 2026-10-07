#!/usr/bin/env python3
"""Standing tests for the additive measured-input helpers and corpus.

Pure stdlib and no compiler: the wire printer/parser, the observed-class
classifier, corpus-manifest validation, the corpus-identity and tree digests,
and the independent re-verification of an accepted report.  A synthetic package
is built in a temporary directory with digests computed by ``hashlib`` directly,
so the verification code is tested against bytes rather than against itself.
"""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT_PATH = Path(__file__).with_name("evidence_measured.py")
SPEC = importlib.util.spec_from_file_location("evidence_measured", SCRIPT_PATH)
assert SPEC is not None and SPEC.loader is not None
em = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(em)

HARNESS_PATH = Path(__file__).with_name("evidence-measure.py")
HARNESS_SPEC = importlib.util.spec_from_file_location("evidence_measure", HARNESS_PATH)
assert HARNESS_SPEC is not None and HARNESS_SPEC.loader is not None
harness = importlib.util.module_from_spec(HARNESS_SPEC)
HARNESS_SPEC.loader.exec_module(harness)


def sha(raw: bytes) -> str:
    return "sha256:" + hashlib.sha256(raw).hexdigest()


class WireTest(unittest.TestCase):
    def test_round_trip_preserves_structure_and_quotes(self) -> None:
        value = ["lara-evidence-report", "1",
                 ["versions", "lara-syntax@0.11", "lara-evidence@0.1"],
                 ["declared"], ["leaf", "a b", "line\nbreak", 'q"uote']]
        self.assertEqual(em.parse(em.canonical(value)), value)

    def test_bare_and_quoted_atoms_match_the_haskeLL_printer(self) -> None:
        self.assertEqual(em.wire("forward-1631"), "forward-1631")
        self.assertEqual(em.wire(""), '""')
        self.assertEqual(em.wire("two words"), '"two words"')
        self.assertEqual(em.wire("a\nb"), '"a\\nb"')
        self.assertEqual(em.wire('a"b'), '"a\\"b"')

    def test_trailing_input_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            em.parse("(a) (b)")

    def test_field_requires_exactly_one(self) -> None:
        self.assertEqual(em.field([["x", "1"]], "x"), ["1"])
        with self.assertRaises(ValueError):
            em.field([["x", "1"], ["x", "2"]], "x")
        with self.assertRaises(ValueError):
            em.field([], "x")


class ClassifyTest(unittest.TestCase):
    def test_accepted(self) -> None:
        self.assertEqual(em.classify(0, b"(report)\n", "")["class"], "accepted")

    def test_package_invalid_exits_two(self) -> None:
        observed = em.classify(2, b"", "lara: package invalid: object SHA256 mismatch\n")
        self.assertEqual(observed["class"], "invalid")
        self.assertEqual(observed["reason"], "object SHA256 mismatch")

    def test_admission_rejection_is_the_policy_class(self) -> None:
        stderr = ("lara: leaf 'drop': kind=certified, provenance=checker(csv-row, 1) "
                  "matched admission row (certified, checker(csv-row, 1)) = reject (R8)\n")
        observed = em.classify(1, b"", stderr)
        self.assertEqual(observed["class"], "policy")
        self.assertEqual(observed["leaf"], "drop")

    def test_located_evidence_classes_and_reasons(self) -> None:
        cases = {
            "binding": "object does not resolve an existing leaf reference",
            "capture": "object SHA256 mismatch",
            "extraction": "extracted proposition mismatch",
        }
        for stage, reason in cases.items():
            stderr = f"lara: leaf 'drop': certified evidence {stage}: {reason} (R8)\n"
            observed = em.classify(1, b"", stderr)
            self.assertEqual(observed["class"], stage)
            self.assertEqual(observed["leaf"], "drop")
            self.assertEqual(observed["reason"], reason)
            self.assertEqual(observed["object"], "-")

    def test_exit_one_without_r8_is_not_an_evidence_class(self) -> None:
        self.assertEqual(em.classify(1, b"", "lara: verdict reject\n")["class"], "core-reject")

    def test_refusal_with_stdout_cannot_count_as_a_matching_rejection(self) -> None:
        diagnostic = "lara: leaf 'drop': certified evidence capture: object SHA256 mismatch (R8)\n"
        self.assertEqual(em.classify(1, b"partial success report\n", diagnostic)["class"], "error")


class CorpusTest(unittest.TestCase):

    def test_rejected_row_with_a_partition_is_refused(self) -> None:
        header = "\t".join(em.CORPUS_COLUMNS)
        row = "\t".join(["bad", "fixtures/evidence/quarantined", "-", "capture", "drop",
                         "object SHA256 mismatch", "drop", "-", "-"])
        with self.assertRaises(ValueError):
            em.parse_corpus(header + "\n" + row + "\n")

    def test_accepted_row_without_assurance_is_refused(self) -> None:
        header = "\t".join(em.CORPUS_COLUMNS)
        row = "\t".join(["bad", "fixtures/evidence/quarantined", "-", "accepted", "-",
                         "-", "drop", "-", "-"])
        with self.assertRaises(ValueError):
            em.parse_corpus(header + "\n" + row + "\n")

    def test_unknown_class_is_refused(self) -> None:
        header = "\t".join(em.CORPUS_COLUMNS)
        row = "\t".join(["bad", "fixtures/evidence/quarantined", "-", "nonsense", "-",
                         "-", "-", "-", "-"])
        with self.assertRaises(ValueError):
            em.parse_corpus(header + "\n" + row + "\n")


class DigestTest(unittest.TestCase):
    def test_tree_digest_is_order_independent_and_content_sensitive(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "b").mkdir()
            (root / "a.txt").write_bytes(b"one\n")
            (root / "b" / "c.txt").write_bytes(b"two\n")
            first = em.tree_digest(root)
            self.assertEqual(first, em.tree_digest(root))
            (root / "a.txt").write_bytes(b"one!\n")
            self.assertNotEqual(first, em.tree_digest(root))

    def test_tree_digest_refuses_symlinks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "real").write_bytes(b"x")
            (root / "link").symlink_to(root / "real")
            with self.assertRaises(ValueError):
                em.tree_digest(root)


class AcceptedReportTest(unittest.TestCase):
    """The independent re-verification is tested against hand-built bytes."""

    def build_package(self, root: Path) -> dict:
        paper = b"# paper\n"
        source = (
            'artifact a at sha256:x\n'
            'policy p\n'
            'use backends [ord@1, insp@1]\n'
            'leaf drop : evidence(7)\n'
            '  kind = certified\n'
            '  provenance = checker(csv-row, 1)\n'
            '  refs = [evidence/measurements.csv]\n'
            '  extract = (csv-row 1 measurements (key id drop) (select (value decimal)) (predicate evidence))\n'
        ).encode("utf-8")
        policy = b"policy p\ntheory sha256:z = []\ntheory sha256:a = []\nadmission { (certified, checker(csv-row, 1)) = admit }\nevidence-checkers = (checkers (csv-row 1))\n"
        measurements = b"id,value\ndrop,7\n"
        (root / "evidence").mkdir()
        (root / "PAPER.md").write_bytes(paper)
        (root / "artifact.lara").write_bytes(source)
        (root / "surface-policy.policy.lara").write_bytes(policy)
        (root / "evidence/measurements.csv").write_bytes(measurements)
        manifest = ["lara-evidence", "1", ["paper", "paper"], ["source", "source"], ["policy", "policy"],
                    ["objects",
                     ["object", "paper", "PAPER.md", str(len(paper)), sha(paper)],
                     ["object", "source", "artifact.lara", str(len(source)), sha(source)],
                     ["object", "policy", "surface-policy.policy.lara", str(len(policy)), sha(policy)],
                     ["object", "measurements", "evidence/measurements.csv", str(len(measurements)), sha(measurements)]]]
        (root / em.EVIDENCE_MANIFEST).write_bytes(em.canonical(manifest))
        return {"manifest": manifest, "source": source,
                "objects": manifest[-1][1:], "measurements": measurements}

    def build_report(self, package: dict, manifest_path: Path) -> bytes:
        request = ["csv-row", "1", "measurements", ["key", "id", "drop"],
                   ["select", ["value", "decimal"]], ["predicate", "evidence"]]
        dependency = ["dependencies", ["leaf", "drop", ["objects", ["object", "measurements",
                      "evidence/measurements.csv", str(len(package["measurements"])),
                      sha(package["measurements"])]]]]
        replay = ["leaf", "drop", request, ["deps", ["object", "measurements",
                  "evidence/measurements.csv", str(len(package["measurements"])),
                  sha(package["measurements"])]]]
        core_replay = ["replay-id", ["core", em.CORE_VERSION], ["policy", "p"],
                       ["backends", ["backend", "ord", "1"], ["backend", "insp", "1"]],
                       ["theories", "sha256:a", "sha256:z"], ["artifact", "sha256:x"]]
        envelope = ["lara-evidence-report", "1",
                    ["versions", "lara-syntax@0.11", "lara-evidence@0.1"],
                    ["assurance", "evidence-checked"],
                    ["manifest", sha(manifest_path.read_bytes())],
                    ["source", sha(package["source"])],
                    ["policy", "package", sha((manifest_path.parent / "surface-policy.policy.lara").read_bytes())],
                    ["checked", "drop"],
                    ["declared"],
                    ["replays", replay],
                    ["dependency-report-digest", sha(em.canonical(dependency))],
                    ["captured", *package["objects"]],
                    ["core-replay", core_replay],
                    ["core-verdict", ["verdict", core_replay, "accept"]]]
        envelope.append(["evidence-digest", sha(em.canonical(envelope))])
        return em.canonical(envelope)

    def test_verification_accepts_a_correct_report(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            stdout = self.build_report(package, root / em.EVIDENCE_MANIFEST)
            info = em.read_accepted_report(root, None, stdout)
            self.assertEqual(info["checked"], ["drop"])
            self.assertEqual(info["declared"], [])
            self.assertEqual(info["assurance"], "evidence-checked")
            self.assertEqual(info["core-outcome"], "accept")
            self.assertTrue(all(info["verified"].values()), info["verified"])

    def test_verification_rejects_a_moved_evidence_digest(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            stdout = self.build_report(package, root / em.EVIDENCE_MANIFEST)
            value = em.parse(stdout)
            for item in value:
                if isinstance(item, list) and item and item[0] == "evidence-digest":
                    item[1] = "sha256:" + "0" * 64
            info = em.read_accepted_report(root, None, em.canonical(value))
            self.assertFalse(info["verified"]["evidence-digest"])
            self.assertTrue(info["verified"]["dependency-report-digest"])

    def test_verification_rejects_a_swapped_source(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            stdout = self.build_report(package, root / em.EVIDENCE_MANIFEST)
            (root / "artifact.lara").write_bytes(package["source"] + b"\n")
            info = em.read_accepted_report(root, None, stdout)
            self.assertFalse(info["verified"]["source-sha256"])

    def test_self_consistent_digest_cannot_bless_a_rejected_core_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            envelope = em.parse(self.build_report(package, root / em.EVIDENCE_MANIFEST))
            next(item for item in envelope if isinstance(item, list) and item[0] == "core-verdict")[1][2] = "reject"
            envelope.pop()
            envelope.append(["evidence-digest", sha(em.canonical(envelope))])
            info = em.read_accepted_report(root, None, em.canonical(envelope))
            self.assertTrue(info["verified"]["evidence-digest"])
            self.assertFalse(info["verified"]["core-accept"])

    def test_self_consistent_digest_cannot_bless_an_unrelated_core_replay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            envelope = em.parse(self.build_report(package, root / em.EVIDENCE_MANIFEST))
            next(item for item in envelope if isinstance(item, list) and item[0] == "core-verdict")[1][1] = "unrelated-replay"
            envelope.pop()
            envelope.append(["evidence-digest", sha(em.canonical(envelope))])
            info = em.read_accepted_report(root, None, em.canonical(envelope))
            self.assertTrue(info["verified"]["evidence-digest"])
            self.assertFalse(info["verified"]["core-replay"])

    def test_self_consistent_report_cannot_bless_a_wrong_input_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            package = self.build_package(root)
            report = self.build_report(package, root / em.EVIDENCE_MANIFEST)
            changes = [
                ("shape", None, "lara-core@0.3+test"),
                ("core", 1, ["core", "lara-core@0.2"]),
                ("policy", 2, ["policy", "unrelated"]),
                ("backends", 3, ["backends", ["backend", "insp", "1"], ["backend", "ord", "1"]]),
                ("theories", 4, ["theories", "sha256:z", "sha256:a"]),
                ("artifact", 5, ["artifact", "sha256:unrelated"]),
            ]
            for component, position, replacement in changes:
                with self.subTest(component=component):
                    envelope = em.parse(report)
                    replay = em.field(envelope, "core-replay")[0]
                    if position is None:
                        replay = replacement
                    else:
                        replay[position] = replacement
                    next(item for item in envelope if isinstance(item, list) and item[0] == "core-replay")[1] = replay
                    next(item for item in envelope if isinstance(item, list) and item[0] == "core-verdict")[1][1] = replay
                    envelope.pop()
                    envelope.append(["evidence-digest", sha(em.canonical(envelope))])
                    info = em.read_accepted_report(root, None, em.canonical(envelope))
                    self.assertTrue(info["verified"]["evidence-digest"])
                    self.assertFalse(info["verified"]["core-replay"])


class HarnessRenderTest(unittest.TestCase):
    """The harness's pure rendering, aggregation and argument handling."""

    def record(self, **overrides) -> dict:
        base = {
            "input": "case", "root": "fixtures/evidence/quarantined", "policy": "-",
            "input-digest": "sha256:t", "policy-digest": "-",
            "expected": "accepted", "expected-exit": 0, "actual": "accepted", "exit": 0,
            "stage": "-", "leaf": "-", "object": "-", "reason": "-",
            "stdout-sha256": "sha256:s", "stderr-sha256": "sha256:e",
            "versions": ["lara-syntax@0.11", "lara-evidence@0.1"],
            "assurance": "evidence-checked", "checked": ["drop"], "declared": [],
            "manifest-sha256": "sha256:m", "source-sha256": "sha256:src",
            "policy-origin": "package", "policy-sha256": "sha256:p",
            "core-replay": "lara-core@0.3+test", "core-outcome": "accept",
            "dependency-report-digest": "sha256:d", "evidence-digest": "sha256:v",
            "verified": {"report-canonical": True}, "class-match": True,
        }
        base.update(overrides)
        return base


    def test_aggregate_counts_classes_and_partitions(self) -> None:
        records = [
            self.record(),
            self.record(input="b", checked=["d", "e"], declared=["f"]),
            self.record(input="c", expected="capture", actual="capture", assurance=None,
                        checked=None, declared=None, **{"class-match": False}),
        ]
        result = harness.aggregate(records)
        self.assertEqual(result["count"], 3)
        self.assertEqual(result["class-match-rate"], {"matched": 2, "total": 3})
        self.assertEqual(result["class-accuracy"]["accepted"], {"matched": 2, "total": 2})
        self.assertEqual(result["class-accuracy"]["capture"], {"matched": 0, "total": 1})
        self.assertEqual(result["checked-leaves"], 3)
        self.assertEqual(result["declared-leaves"], 1)
        self.assertEqual(result["assurances"], {"evidence-checked": 2})

    def report(self) -> dict:
        return {
            "format": "lara-evidence-measure-report@1",
            "environment": {"git-rev": "original-machine"},
            "records": [self.record()],
            "aggregate": {"class-match-rate": {"matched": 1, "total": 1}},
        }

    def test_freeze_comparison_ignores_machine_environment_on_both_sides(self) -> None:
        frozen = self.report()
        observed = copy.deepcopy(frozen)
        observed["environment"] = {"git-rev": "another-machine"}
        self.assertEqual(harness.snapshot_errors(
            frozen, observed, harness.render_tsv(frozen["records"])), [])

    def test_freeze_comparison_rejects_changed_evidence_identity(self) -> None:
        frozen = self.report()
        observed = copy.deepcopy(frozen)
        observed["records"][0]["evidence-digest"] = "sha256:changed"
        errors = harness.snapshot_errors(frozen, observed, harness.render_tsv(frozen["records"]))
        self.assertIn("block 'records' differs from the frozen snapshot", errors)

    def test_freeze_comparison_rejects_stale_tsv(self) -> None:
        report = self.report()
        tsv = harness.render_tsv(report["records"]).replace("accepted", "capture")
        self.assertIn("TSV differs from the frozen snapshot",
                      harness.snapshot_errors(report, report, tsv))

    def test_freeze_cannot_bless_a_recorded_mismatch(self) -> None:
        report = self.report()
        report["records"][0]["class-match"] = False
        report["aggregate"]["class-match-rate"]["matched"] = 0
        self.assertIn("observed inputs do not all match their declared class",
                      harness.snapshot_errors(report, report, harness.render_tsv(report["records"])))

    def test_failed_environment_probe_does_not_fabricate_metadata(self) -> None:
        with self.assertRaises(SystemExit):
            harness.probe(sys.executable, "-c", "raise SystemExit(7)")

    def test_identical_verifier_policy_cannot_change_core_or_capture_identity(self) -> None:
        base = self.record(**{"core-verdict": ["verdict", "replay", "accept"],
                              "replays": ["leaf"], "captured": ["object"]})
        override = copy.deepcopy(base)
        override["evidence-digest"] = "sha256:verifier"
        self.assertTrue(harness.identical_policy_invariant(base, override))
        for field in ("core-replay", "core-verdict", "replays",
                      "dependency-report-digest", "captured", "policy-sha256"):
            changed = copy.deepcopy(override)
            changed[field] = None
            with self.subTest(field=field):
                self.assertFalse(harness.identical_policy_invariant(base, changed))
        override["evidence-digest"] = base["evidence-digest"]
        self.assertFalse(harness.identical_policy_invariant(base, override))


if __name__ == "__main__":
    unittest.main(verbosity=2)
