"""Tests for elaborator/elaborate.py (stdlib unittest only, zero added deps).

One test per spec-§11 task (T10) pinning the trace -> .lara derivation against
the committed walking-skeleton source, plus the malformed-source negatives
pinning the 6A input-validation contract and the T9 transactional contract.

Invocation (from the repo root):

    uv run --no-project python -m unittest discover -s elaborator -v

Each test drives the real CLI end to end (`uv run --no-project
elaborator/elaborate.py <bundle-dir>`) against a temp bundle copy, so the PEP
723 header (pinned PyYAML, requires-python) is honored exactly as in CI.
"""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
SCRIPT = REPO / "elaborator" / "elaborate.py"
SKELETON = REPO / "bundles" / "walking-skeleton"
UV = shutil.which("uv") or str(Path.home() / ".local/bin/uv")

ARTIFACTS = ("emitted.lara", "empirical-v1.policy.lara", "provenance.json")


def make_bundle(dest: Path, source_text: str | None = None) -> Path:
    """Create a temp bundle dir holding only source.yaml (default: the
    committed walking-skeleton source)."""
    dest.mkdir(parents=True, exist_ok=True)
    if source_text is None:
        source_text = (SKELETON / "source.yaml").read_text(encoding="utf-8")
    (dest / "source.yaml").write_text(source_text, encoding="utf-8")
    return dest


def run_elaborator(
    bundle: Path, script: Path = SCRIPT
) -> subprocess.CompletedProcess:
    return subprocess.run(
        [UV, "run", "--no-project", str(script), str(bundle)],
        capture_output=True,
        text=True,
    )


class SuccessRun(unittest.TestCase):
    """One shared elaborator run over the committed source; each test pins one
    §11 task's derivation (emitted bytes and/or provenance entries)."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="elaborate-test-"))
        cls.bundle = make_bundle(cls.tmp / "bundle")
        cls.result = run_elaborator(cls.bundle)
        assert cls.result.returncode == 0, cls.result.stderr
        cls.emitted = (cls.bundle / "emitted.lara").read_text(encoding="utf-8")
        cls.prov = json.loads((cls.bundle / "provenance.json").read_text(encoding="utf-8"))

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_run_layout_and_canonicalization(self):
        self.assertEqual(self.result.returncode, 0, self.result.stderr)
        # Exactly the three B1 artifacts appear beside source.yaml.
        self.assertEqual(
            sorted(p.name for p in self.bundle.iterdir()),
            sorted(["source.yaml", *ARTIFACTS]),
        )
        # C1: one trailing LF; C2: canonical JSON; 1A: byte-identical policy.
        self.assertTrue(self.emitted.endswith("\n") and not self.emitted.endswith("\n\n"))
        raw_prov = (self.bundle / "provenance.json").read_text(encoding="utf-8")
        self.assertEqual(
            raw_prov,
            json.dumps(self.prov, sort_keys=True, indent=2, ensure_ascii=True) + "\n",
        )
        self.assertEqual(
            (self.bundle / "empirical-v1.policy.lara").read_bytes(),
            (REPO / "examples/E1/empirical-v1.policy.lara").read_bytes(),
        )
        self.assertEqual(self.prov["format"], "lara-elaborator-provenance@1")
        self.assertEqual(self.prov["policy"], "empirical-v1")
        self.assertEqual(self.prov["source"], "source.yaml")

    def test_task1_formalization(self):
        # Each claim node emits one claim declaration with derived formal and
        # binding; nl is the source text verbatim; ids claim_<X> -> c_<X>.
        self.assertIn(
            'claim c_ow\n'
            '  nl      = "KV-cache quantization improves decode latency on the '
            'openweb text distribution."\n'
            '  formal  = improves(kv_quant, latency, openweb)\n'
            '  binding = { author = alice, audit-status = reviewed }',
            self.emitted,
        )
        # reviewed: false -> unreviewed.
        self.assertIn("binding = { author = carol, audit-status = unreviewed }", self.emitted)
        entries = self.prov["task-1-formalization"]
        self.assertEqual([e["source-node"] for e in entries], ["claim_ow", "claim_cp", "claim_me"])
        self.assertEqual([e["claim"] for e in entries], ["c_ow", "c_cp", "c_me"])
        self.assertEqual(entries[0]["formal"], "improves(kv_quant, latency, openweb)")
        self.assertEqual(
            entries[0]["binding"], {"author": "alice", "audit-status": "reviewed"}
        )

    def test_task2_leaf_extraction(self):
        entries = self.prov["task-2-leaf-extraction"]
        # Every evidence cell of the trace emits exactly one leaf.
        self.assertEqual(len(entries), 12)
        self.assertEqual(
            [e["leaf"] for e in entries],
            [
                "e_ow_mean", "e_ow_rand", "e_ow_gen", "e_ow_power",
                "e_cp_mean", "e_cp_rand", "e_cp_power", "e_cp_gen",
                "e_cp_shift", "e_cp_genfail", "e_me_mean", "e_me_rand",
            ],
        )
        by_cell = {e["source-cell"]: e for e in entries}
        # Topic -> proposition, with experiment binding: a dead-end-nested
        # cell binds the claim's unique supporting experiment.
        self.assertEqual(by_cell["cell_ow_power"]["proposition"], "powered(exp_ow)")
        self.assertEqual(
            by_cell["cell_ow_mean"]["proposition"],
            "reports(exp_ow, effect(kv_quant, latency, openweb, positive))",
        )
        self.assertEqual(
            by_cell["cell_cp_genfail"]["proposition"],
            "not_generalizes(kv_quant, latency, python_code)",
        )
        # recorded -> kind/provenance mapping.
        self.assertEqual(
            (by_cell["cell_ow_mean"]["kind"], by_cell["cell_ow_mean"]["provenance"]),
            ("observed", "ai-executed"),
        )
        self.assertEqual(
            (by_cell["cell_ow_rand"]["kind"], by_cell["cell_ow_rand"]["provenance"]),
            ("attested", "user"),
        )
        # Duplicate-report situation: >1 ref logs the locations, else null.
        self.assertEqual(
            by_cell["cell_ow_mean"]["duplicate-report"],
            {"locations": ["evidence/ow_table1.csv#row=mean", "paper.md#abstract"]},
        )
        self.assertIsNone(by_cell["cell_cp_mean"]["duplicate-report"])
        for e in entries:
            self.assertEqual(e["grain"], "result-cell")
        # The leaves appear in emitted.lara in the same tree-walk order.
        positions = [self.emitted.index(f"leaf {e['leaf']} :") for e in entries]
        self.assertEqual(positions, sorted(positions))

    def test_task3_scheme_selection(self):
        # Selected by premise/conclusion shape from the trusted policy; the
        # source never names a rule.
        self.assertNotIn("controlled_experiment", (SKELETON / "source.yaml").read_text())
        self.assertIn(
            "arg a_ow : supports(c_ow) by "
            "controlled_experiment(kv_quant, latency, openweb, exp_ow)",
            self.emitted,
        )
        entries = self.prov["task-3-scheme-selection"]
        self.assertEqual([e["source-node"] for e in entries], ["exp_ow", "exp_cp", "exp_me"])
        self.assertEqual([e["arg"] for e in entries], ["a_ow", "a_cp", "a_me"])
        for e, dist, exp in zip(entries, ["openweb", "python_code", "mobile_edge"],
                                ["exp_ow", "exp_cp", "exp_me"]):
            self.assertEqual(e["rule"], "controlled_experiment")
            self.assertEqual(
                e["substitution"],
                [["M", "kv_quant"], ["Q", "latency"], ["D", dist], ["Exp", exp]],
            )
        self.assertEqual(entries[0]["premise-leaves"], ["e_ow_mean"])

    def test_task4_question_accounting(self):
        # Discharges in policy question order; the dead end's power cell
        # discharges adequate_power of a_ow.
        self.assertIn(
            "arg a_ow : supports(c_ow) by controlled_experiment(kv_quant, latency, openweb, exp_ow)\n"
            "  discharge randomization     with e_ow_rand\n"
            "  discharge adequate_power    with e_ow_power\n"
            "  discharge external_validity with e_ow_gen",
            self.emitted,
        )
        entries = self.prov["task-4-question-accounting"]
        self.assertEqual(len(entries), 9)
        discharges = [e for e in entries if e["decision"] == "discharge"]
        holes = [e for e in entries if e["decision"] == "hole"]
        # c_me: randomization answered, power and external validity are holes;
        # the incomplete argument is NOT emitted (hole -> gap lowering).
        self.assertEqual([h["question"] for h in holes], ["adequate_power", "external_validity"])
        for h in holes:
            self.assertEqual(h["claim"], "c_me")
            self.assertEqual(h["source-node"], "dd_me_pool")
            self.assertEqual(h["lowered"], "gap")
            self.assertIn("PEIncompleteArgument", h["reason"])
        self.assertNotIn("arg a_me", self.emitted)
        me_discharge = next(e for e in discharges if e["arg"] == "a_me")
        self.assertEqual(
            (me_discharge["question"], me_discharge["with"], me_discharge["source-cell"]),
            ("randomization", "e_me_rand", "cell_me_rand"),
        )

    def test_task5_strict_selection_not_applicable(self):
        self.assertEqual(
            self.prov["task-5-strict-selection"],
            {
                "status": "not-applicable",
                "reason": "defeasible source; Lara.Syntax forces assurance = none (T1); "
                "no strict instance is certified",
            },
        )
        # No assurance/certificate surface is emitted for this source.
        self.assertNotIn("assurance", self.emitted)

    def test_task6_attack_extraction(self):
        # Undercut from the distribution-shift dead end (policy exception),
        # undermine from the robustness experiment (declared contrary).
        self.assertIn(
            "arg d_cp_shift : challenges(external_validity(a_cp)) by leaf(e_cp_shift)\n"
            "undercut d_cp_shift a_cp.rule",
            self.emitted,
        )
        self.assertIn(
            "arg d_cp_genfail : challenges(e_cp_gen) by leaf(e_cp_genfail)\n"
            "undermine d_cp_genfail a_cp.external_validity.leaf",
            self.emitted,
        )
        # Attack blocks appear in source tree order, after all claim contexts,
        # and attack-source leaves are not re-emitted there.
        self.assertLess(self.emitted.index("status c_ow") , len(self.emitted))
        attack_section = self.emitted.index("# --- typed attacks")
        status_section = self.emitted.index("# --- status queries")
        self.assertLess(self.emitted.index("claim c_me"), attack_section)
        self.assertLess(attack_section, status_section)
        self.assertLess(
            self.emitted.index("undercut d_cp_shift"),
            self.emitted.index("undermine d_cp_genfail"),
        )
        self.assertEqual(self.emitted.count("leaf e_cp_shift :"), 1)
        self.assertEqual(self.emitted.count("leaf e_cp_genfail :"), 1)
        entries = self.prov["task-6-attack-extraction"]
        self.assertEqual(
            [(e["source-node"], e["role"]) for e in entries],
            [
                ("dd_ow_power", "support"),
                ("dd_cp_shift", "attack"),
                ("exp_cp_robust", "attack"),
                ("dd_me_pool", "none"),
            ],
        )
        self.assertEqual(entries[0]["leaf"], "e_ow_power")
        self.assertEqual(
            entries[1]["attack"],
            {"kind": "undercut", "attacker": "d_cp_shift", "target": "a_cp.rule"},
        )
        self.assertEqual(
            entries[1]["policy-basis"],
            "exception controlled_experiment : distribution_shift(M, Q, D)",
        )
        self.assertEqual(
            entries[2]["attack"],
            {"kind": "undermine", "attacker": "d_cp_genfail",
             "target": "a_cp.external_validity.leaf"},
        )
        self.assertEqual(
            entries[2]["policy-basis"],
            "contrary generalizes(M, Q, D) not_generalizes(M, Q, D)",
        )
        self.assertIn("task-4 hole", entries[3]["note"])

    def test_determinism_byte_identical_reemission(self):
        before = {a: (self.bundle / a).read_bytes() for a in ARTIFACTS}
        second = run_elaborator(self.bundle)
        self.assertEqual(second.returncode, 0, second.stderr)
        for a in ARTIFACTS:
            self.assertEqual((self.bundle / a).read_bytes(), before[a], a)


class MalformedSources(unittest.TestCase):
    """6A: a malformed source exits nonzero with a located stderr message and
    emits no .lara (and no partial/stale artifacts, T9)."""

    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="elaborate-neg-"))

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def assert_clean_failure(
        self,
        bundle: Path,
        result: subprocess.CompletedProcess,
        *needles: str,
        location: str = "source.yaml",
    ):
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertIn(location, result.stderr)
        for needle in needles:
            self.assertIn(needle, result.stderr)
        # No .lara emitted; no B1 artifacts at all; no staging leftovers.
        self.assertEqual(list(bundle.glob("*.lara")), [])
        self.assertEqual(list(bundle.glob(".elaborate-stage-*")), [])
        self.assertEqual([p.name for p in bundle.iterdir()], ["source.yaml"])

    def check_rejected(
        self,
        source_text: str,
        *needles: str,
        seed_outputs: bool = False,
    ):
        bundle = make_bundle(self.tmp / "bundle", None if seed_outputs else source_text)
        if seed_outputs:
            good = run_elaborator(bundle)
            self.assertEqual(good.returncode, 0, good.stderr)
            (bundle / "source.yaml").write_text(source_text, encoding="utf-8")
        result = run_elaborator(bundle)
        self.assert_clean_failure(bundle, result, *needles)

    def test_rejects_non_lara_artifact_digests_and_removes_stale_outputs(self):
        replacements = {
            "missing separator": 'digest: "sha256x"',
            "empty body": 'digest: "sha256:"',
            "whitespace": 'digest: "sha256:bad body"',
            "multiline": r'digest: "sha256:bad\nbody"',
        }
        for label, replacement in replacements.items():
            with self.subTest(label=label):
                bundle = make_bundle(self.tmp / f"digest-{label.replace(' ', '-')}")
                good = run_elaborator(bundle)
                self.assertEqual(good.returncode, 0, good.stderr)
                source_path = bundle / "source.yaml"
                source = source_path.read_text(encoding="utf-8")
                source_path.write_text(
                    source.replace(
                        'digest: "sha256:5ca1e..."',
                        replacement,
                        1,
                    ),
                    encoding="utf-8",
                )

                bad = run_elaborator(bundle)

                self.assert_clean_failure(
                    bundle,
                    bad,
                    "meta.artifact.digest",
                    "Lara digest",
                )

    def test_optional_collections_require_lists_when_present(self):
        claim = """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: claim_a
    type: claim
    text: "M improves q on d."
    subject: {method: m, quality: q, distribution: d}
    stance: improvement
    author: alice
    reviewed: true
    children: %s
"""
        experiment = """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: claim_a
    type: claim
    text: "M improves q on d."
    subject: {method: m, quality: q, distribution: d}
    stance: improvement
    author: alice
    reviewed: true
    children:
      - id: exp_a
        type: experiment
        title: "experiment"
        summary: "summary"
        evidence_cells: %s
"""
        cases = (
            ("children", "false", claim, True),
            ("children", "{not: a-list}", claim, False),
            ("evidence_cells", "false", experiment, False),
            ("evidence_cells", "{not: a-list}", experiment, False),
        )
        for field, value, template, seed_outputs in cases:
            with self.subTest(field=field, value=value):
                self.check_rejected(
                    template % value,
                    "claim_a" if field == "children" else "exp_a",
                    f"'{field}' must be a list",
                    seed_outputs=seed_outputs,
                )

    def test_invalid_utf8_source_removes_stale_outputs(self):
        bundle = make_bundle(self.tmp / "invalid-utf8")
        good = run_elaborator(bundle)
        self.assertEqual(good.returncode, 0, good.stderr)
        (bundle / "source.yaml").write_bytes(b"\xffnot UTF-8")

        bad = run_elaborator(bundle)

        self.assert_clean_failure(bundle, bad, "invalid UTF-8", "source")

    def test_invalid_utf8_trusted_policy_is_a_located_cli_error(self):
        temp_repo = self.tmp / "policy-repo"
        temp_script = temp_repo / "elaborator" / "elaborate.py"
        temp_script.parent.mkdir(parents=True)
        shutil.copy2(SCRIPT, temp_script)
        policy_path = temp_repo / "examples" / "E1" / "empirical-v1.policy.lara"
        policy_path.parent.mkdir(parents=True)
        policy_path.write_bytes(b"\xffnot UTF-8")
        bundle = make_bundle(temp_repo / "bundle")

        result = run_elaborator(bundle, temp_script)

        self.assert_clean_failure(
            bundle,
            result,
            "invalid UTF-8",
            "trusted policy",
            location="examples/E1/empirical-v1.policy.lara",
        )

    def test_unparseable_yaml(self):
        self.check_rejected("meta: [unclosed\n", "line")

    def test_missing_node_field(self):
        self.check_rejected(
            """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: claim_a
    type: claim
    subject: {method: m, quality: q, distribution: d}
    stance: improvement
    author: alice
    reviewed: true
""",
            "claim_a",
            "'text'",
        )

    def test_unknown_node_kind(self):
        self.check_rejected(
            """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: hypothesis_a
    type: hypothesis
""",
            "hypothesis_a",
            "unknown node kind",
        )

    def test_dead_end_cell_without_unique_supporting_experiment(self):
        # A dead-end-nested cell with zero candidate supporting experiments in
        # its claim context is malformed (README §4.2 task 2).
        self.check_rejected(
            """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: claim_a
    type: claim
    text: "M improves q on d."
    subject: {method: m, quality: q, distribution: d}
    stance: improvement
    author: alice
    reviewed: true
    children:
      - id: dd_a
        type: dead_end
        title: "abandoned power analysis"
        narrative: "never rerun"
        evidence_cells:
          - id: cell_a_power
            topic: power
            what: "power analysis"
            recorded: paper-text
            refs: [paper.md#sec=1]
""",
            "cell_a_power",
            "unique supporting experiment",
        )

    def test_rejects_cell_id_without_cell_prefix(self):
        # Cell ids derive to leaves by slicing a fixed "cell_" prefix
        # (README §4 task 2: cell_<Y> -> e_<Y>). A valid-atom id lacking the
        # prefix must be rejected at 6A, mirroring the claim_/exp_ guards,
        # rather than silently slicing past the string end into a collision.
        self.check_rejected(
            """\
meta:
  format: ara-mini-trace@1
  artifact: {id: x, digest: "sha256:x"}
  policy: empirical-v1
tree:
  - id: claim_a
    type: claim
    text: "M improves q on d."
    subject: {method: m, quality: q, distribution: d}
    stance: improvement
    author: alice
    reviewed: true
    children:
      - id: exp_a
        type: experiment
        title: "experiment"
        summary: "summary"
        evidence_cells:
          - id: a_mean
            topic: positive-effect-report
            what: "mean latency improved"
            recorded: run-output
            refs: [paper.md#sec=1]
""",
            "a_mean",
            "cell id must start with 'cell_'",
        )

    def test_failed_run_removes_stale_artifacts(self):
        # T9: pre-existing B1 artifacts from an earlier good run must not
        # survive a failed run (nothing stale left to be mistaken for fresh).
        bundle = make_bundle(self.tmp / "bundle")
        good = run_elaborator(bundle)
        self.assertEqual(good.returncode, 0, good.stderr)
        self.assertTrue((bundle / "emitted.lara").exists())
        # Corrupt the source and re-run.
        (bundle / "source.yaml").write_text("meta: [unclosed\n", encoding="utf-8")
        bad = run_elaborator(bundle)
        self.assertNotEqual(bad.returncode, 0)
        for name in ARTIFACTS:
            self.assertFalse((bundle / name).exists(), f"stale {name} survived")
        self.assertEqual(list(bundle.glob(".elaborate-stage-*")), [])
        self.assertEqual([p.name for p in bundle.iterdir()], ["source.yaml"])


if __name__ == "__main__":
    unittest.main()
