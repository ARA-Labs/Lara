#!/usr/bin/env python3
"""OS process and immutable-evidence boundaries for inquiry measurement.

All executables in these tests are temporary fake OS programs. No production
inquiry driver or real consumer is invoked. The fake-process fixture replaces
repository preflight because the corrected runtime differs from the original
pin. Frozen suite validation, committed input bytes, helper hashes and the
production budget remain checked. A separate test uses real repository
preflight and proves that it rejects the changed runtime before any driver call.
"""
from __future__ import annotations

import argparse
import copy
import importlib.util
import json
import os
import shutil
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from evidence_measured import canonical
from inquiry_evaluation_manifest import INPUT_COMMIT, digest, json_bytes, load_suite
from inquiry_evaluation_report import diagnostics, process_counts, protocol, score_case, summary

spec = importlib.util.spec_from_file_location("inquiry_evaluate", ROOT / "scripts/inquiry-evaluate.py")
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
MANIFEST = ROOT / "evaluation/inquiry-p8/MANIFEST.json"
OBSERVATIONS = []


def fake(path, body):
    path.write_text("#!/usr/bin/env python3\n" + body)
    path.chmod(0o755)
    return path


def fake_repository_preflight(protocol, suite_base, suite_inventory):
    """Only fake OS fixtures skip runtime/legacy/approval repository checks.

    load_suite remains unchanged, including budgets, partitions and hashes.
    Retain committed suite identity and all original helper byte identities.
    There is no production CLI option that enables this fixture adapter.
    """
    commit = runner.git("rev-parse", INPUT_COMMIT).decode().strip()
    for path in suite_inventory:
        relative = (suite_base.relative_to(ROOT) / path).as_posix()
        runner.require(runner.git("show", f"{commit}:{relative}") == (suite_base / path).read_bytes(),
                       f"fake fixture input freeze mismatch: {relative}")
    recipe = protocol["recipes"]
    quality = runner.read_json(suite_base / "quality-review.json")
    inventory = {}
    helpers = [(recipe["generator_path"], recipe["generator_sha256"]),
               ("evaluation/inquiry-p8/review/independent_finite_audit.py", recipe["independent_audit_tool_sha256"]),
               (recipe["certificate_producer_path"], recipe["certificate_producer_sha256"])]
    helpers.extend((quality[path_key], quality[hash_key]) for path_key, hash_key in (
        ("generator_path", "generator_sha256"), ("audit_tool_path", "audit_tool_sha256"),
        ("boundary_test_path", "boundary_test_sha256")))
    for path, expected in helpers:
        runner.checked(ROOT, path, expected, inventory)
    return commit, inventory


class Boundaries(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="inquiry-runner-boundaries-")
        cls.directory = Path(cls.temporary.name)
        cls.base, cls.protocol, cls.manifest, cls.oracles, cls.inventory = load_suite(MANIFEST)
        cls.real_repository_preflight = staticmethod(runner.repository_preflight)
        adapter = patch.object(runner, "repository_preflight", side_effect=fake_repository_preflight)
        adapter.start()
        cls.addClassCleanup(adapter.stop)
        timeout = fake(cls.directory / "fake-timeout", "import sys,time\nprint('partial stdout',flush=True)\nprint('partial stderr',file=sys.stderr,flush=True)\ntime.sleep(60)\n")
        consumer = fake(cls.directory / "fake-consumer", "raise SystemExit(0)\n")
        cls.saved = cls.directory / "saved"
        args = argparse.Namespace(manifest=str(MANIFEST), native=str(timeout), lean=str(timeout),
                                  consumer=str(consumer), out=str(cls.saved))
        # Uses the disclosed fake fixture adapter and production ten-second timeout.
        cls.exit = runner.measure(args)
        cls.saved_run = json.loads((cls.saved / "run.json").read_text())
        timeout.unlink()
        consumer.unlink()
        OBSERVATIONS.append({"probe": "production-budget runner with first fake OS driver timeout",
            "repository_preflight": "fake-process fixture adapter; original runtime pin deliberately skipped",
            "exit_code": cls.exit, "completion": cls.saved_run["completion"],
            "invocations": len(cls.saved_run["invocations"]),
            "missing_invocations": len(cls.saved_run["missing_invocations"]),
            "invocation": cls.saved_run["invocations"][0], "production_driver_invocations": 0})

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def test_timeout_retains_partial_streams_and_stops(self):
        self.assertEqual(self.exit, 1)
        self.assertEqual(self.saved_run["completion"], "INCOMPLETE")
        self.assertEqual(len(self.saved_run["invocations"]), 1)
        self.assertEqual(len(self.saved_run["missing_invocations"]), 191)
        invocation = self.saved_run["invocations"][0]
        self.assertTrue(invocation["timeout"])
        self.assertEqual(invocation["signal"], 9)
        self.assertEqual((self.saved / invocation["stdout_path"]).read_bytes(), b"partial stdout\n")
        self.assertEqual((self.saved / invocation["stderr_path"]).read_bytes(), b"partial stderr\n")

    def test_real_signal_retained(self):
        directory = self.directory / "signal"
        directory.mkdir()
        (directory / "raw").mkdir()
        program = fake(directory / "fake", "import os,signal\nprint('signal prefix',flush=True)\nos.kill(os.getpid(),signal.SIGTERM)\n")
        record = runner.invoke([program], directory, "signal.native", time.monotonic() + 10)
        self.assertEqual(record["exit_code"], -15)
        self.assertEqual(record["signal"], 15)
        self.assertEqual(record["failure"], "signal")
        self.assertEqual((directory / record["stdout_path"]).read_bytes(), b"signal prefix\n")
        OBSERVATIONS.append({"probe": "real OS signal", "invocation": record})

    def test_deadline_and_spawn_failure(self):
        directory = self.directory / "deadline"
        directory.mkdir()
        (directory / "raw").mkdir()
        record = runner.invoke(["/missing-inquiry-probe"], directory, "deadline.native", time.monotonic() - 1)
        self.assertEqual(record["failure"], "aggregate-deadline")
        self.assertIsNone(record["spawn_failure"])
        spawn = runner.invoke(["/missing-inquiry-probe"], directory, "spawn.native", time.monotonic() + 10)
        self.assertEqual(spawn["failure"], "spawn-failure")
        self.assertTrue(spawn["spawn_failure"])
        OBSERVATIONS.append({"probe": "deadline before spawn and missing process", "deadline": record, "spawn": spawn})

    def test_capture_only_replay_after_original_binaries_removed(self):
        out = self.directory / "replay"
        with patch.object(runner.subprocess, "run", side_effect=AssertionError("replay spawned")), \
             patch.object(runner.subprocess, "Popen", side_effect=AssertionError("replay spawned")):
            code = runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(self.saved), out=str(out)))
        self.assertEqual(code, 1)
        for relative in ["run.json", "run.sha256", "results.jsonl", "summary.json", "summary.tsv"]:
            self.assertEqual((out / relative).read_bytes(), (self.saved / relative).read_bytes())
        OBSERVATIONS.append({"probe": "portable partial capture-only replay", "exit_code": code,
                             "subprocesses": 0, "deterministic_hashes": self.saved_run["deterministic_report_hashes"]})

    def test_complete_fake_capture_and_replay_keep_all_reports_identical(self):
        # A complete production partition is necessary to exercise COMPLETE
        # replay. These fake programs print frozen ASTs as explicit test data;
        # neither production driver nor the real consumer is invoked here.
        program = fake(self.directory / "fake-complete", "import json,sys\nfrom pathlib import Path\n"
            + "sys.path.insert(0," + repr(str(ROOT / "scripts")) + ")\n"
            + "from evidence_measured import canonical\n"
            + "source=Path(sys.argv[-1])\n"
            + "oracle=json.loads((source.parent.parent/'oracles'/(source.stem+'.json')).read_text())\n"
            + "sys.stdout.buffer.write(b''.join(canonical(f) for f in oracle['expected']['results']))\n")
        consumer = fake(self.directory / "fake-complete-consumer", "raise SystemExit(0)\n")
        saved, replay = self.directory / "complete", self.directory / "complete-replay"
        code = runner.measure(argparse.Namespace(manifest=str(MANIFEST), native=str(program), lean=str(program),
                        consumer=str(consumer), out=str(saved)))
        self.assertEqual(code, 0)
        run = json.loads((saved / "run.json").read_text())
        self.assertEqual(len(run["invocations"]), 192)
        self.assertEqual(run["missing_invocations"], [])
        self.assertEqual(len(run["pair_checkpoints"]), 96)
        self.assertTrue(all(checkpoint["passed"] for checkpoint in run["pair_checkpoints"]))
        self.assertIsNone(run["semantic_discrepancy"])
        self.assertEqual(run["allocated_cpus"], [min(run["affinity_before"])])
        program.unlink()
        consumer.unlink()
        with patch.object(runner.subprocess, "run", side_effect=AssertionError("replay spawned")), \
             patch.object(runner.subprocess, "Popen", side_effect=AssertionError("replay spawned")):
            self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved), out=str(replay))), 0)
        for relative in ["run.json", "run.sha256", "results.jsonl", "summary.json", "summary.tsv"]:
            self.assertEqual((saved / relative).read_bytes(), (replay / relative).read_bytes())
        OBSERVATIONS.append({"probe": "complete fake-capture replay", "exit_code": code,
            "invocations": len(run["invocations"]), "production_driver_invocations": 0,
            "real_consumer_invocations": 0, "replay_subprocesses": 0,
            "deterministic_hashes": run["deterministic_report_hashes"],
            "basis": "fake executables print frozen ASTs as explicit test data, not oracle population"})

    def test_tampering_and_missing_captures_refused(self):
        paths = ["run.json", self.saved_run["invocations"][0]["stdout_path"],
                 self.saved_run["invocations"][0]["stderr_path"],
                 "evidence/suite/" + self.manifest["cases"][0]["input_path"],
                 self.saved_run["binaries"]["native"]["saved_path"]]
        for relative in paths:
            with self.subTest(relative=relative):
                destination = self.directory / ("tamper-" + str(paths.index(relative)))
                shutil.copytree(self.saved, destination)
                path = destination / relative
                path.chmod(0o644)
                path.write_bytes(path.read_bytes() + b" ")
                with self.assertRaises((ValueError, json.JSONDecodeError)):
                    runner.validate_saved(destination, MANIFEST)
        missing = self.directory / "missing-capture"
        shutil.copytree(self.saved, missing)
        (missing / self.saved_run["invocations"][0]["stdout_path"]).unlink()
        with self.assertRaises(OSError):
            runner.validate_saved(missing, MANIFEST)
        OBSERVATIONS.append({"probe": "tamper and missing capture rejection", "tampered_fields": paths,
                             "all_rejected": True})

    def test_output_reuse_refused_without_writes(self):
        out = self.directory / "existing-empty"
        out.mkdir()
        with self.assertRaisesRegex(ValueError, "output already exists") as empty_error:
            runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(self.saved), out=str(out)))
        self.assertEqual(list(out.iterdir()), [])
        before = (self.saved / "run.json").read_bytes()
        with self.assertRaisesRegex(ValueError, "output already exists") as populated_error:
            runner.measure(argparse.Namespace(manifest=str(MANIFEST), out=str(self.saved)))
        self.assertEqual((self.saved / "run.json").read_bytes(), before)
        OBSERVATIONS.append({"probe": "existing empty and populated output refusal", "unchanged": True,
                             "empty_refusal": str(empty_error.exception),
                             "populated_refusal": str(populated_error.exception)})

    def test_missing_and_hash_mismatch_preflight_before_driver(self):
        bad_suite = self.directory / "bad-suite"
        shutil.copytree(self.base, bad_suite)
        (bad_suite / self.manifest["cases"][0]["input_path"]).write_bytes(b"tampered\n")
        output = self.directory / "bad-output"
        with patch.object(runner, "invoke", side_effect=AssertionError("preflight spawned driver")):
            with self.assertRaisesRegex(ValueError, "hash mismatch") as hash_error:
                runner.measure(argparse.Namespace(manifest=str(bad_suite / "MANIFEST.json"),
                    native="/missing-probe", lean="/missing-probe", consumer="/missing-probe", out=str(output)))
            with self.assertRaises((ValueError, OSError)) as missing_error:
                runner.measure(argparse.Namespace(manifest=str(MANIFEST), native="/missing-probe",
                    lean="/missing-probe", consumer="/missing-probe", out=str(output)))
        self.assertIn("/missing-probe", str(missing_error.exception))
        self.assertFalse(output.exists())
        OBSERVATIONS.append({"probe": "hash mismatch and missing executable preflight", "driver_invocations": 0,
                             "output_created": False, "hash_refusal": str(hash_error.exception),
                             "missing_executable_refusal": str(missing_error.exception)})

    def test_original_production_pin_rejects_changed_runtime_before_driver(self):
        output = self.directory / "original-pin-rejected"
        with patch.object(runner, "repository_preflight", side_effect=self.real_repository_preflight), \
             patch.object(runner, "executable", side_effect=AssertionError("resolved executable after runtime mismatch")), \
             patch.object(runner, "invoke", side_effect=AssertionError("preflight spawned driver")):
            with self.assertRaisesRegex(ValueError, "runtime code changed|runtime path differs") as error:
                runner.measure(argparse.Namespace(manifest=str(MANIFEST), native="/missing-probe",
                    lean="/missing-probe", consumer="/missing-probe", out=str(output)))
        self.assertFalse(output.exists())
        OBSERVATIONS.append({"probe": "real original-pin production preflight rejection",
            "driver_invocations": 0, "output_created": False, "refusal": str(error.exception),
            "repository_preflight": "unmodified production function"})

    def test_both_drivers_same_wrong_answer_fail_independent_oracle(self):
        case = self.manifest["cases"][0]
        oracle = copy.deepcopy(self.oracles[case["case_id"]])
        actual = self.oracles[case["case_id"]]["expected"]["results"]
        oracle["expected"]["results"][0][2] = "intentionally-wrong-oracle-label"
        output = b"".join(canonical(f) for f in actual)
        record = {"exit_code": 0, "failure": None, "consumer": {"accepted": True}}
        result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                            {d: (record, output, b"") for d in ("native", "lean")})
        self.assertTrue(result["driver_agreement"])
        self.assertFalse(result["drivers"]["native"]["oracle_agreement"])
        self.assertFalse(result["drivers"]["lean"]["oracle_agreement"])
        OBSERVATIONS.append({"probe": "intentionally wrong oracle despite driver agreement", "driver_agreement": True,
                             "native_oracle_agreement": False, "lean_oracle_agreement": False,
                             "basis": "frozen AST used as explicit fake-capture test data, not oracle population"})

    def pair_programs(self, name, native_output, lean_output, consumer_body="raise SystemExit(0)\n"):
        calls = self.directory / (name + "-calls.jsonl")
        prefix = ("import json,sys\nfrom pathlib import Path\n"
                  + "with Path(" + repr(str(calls)) + ").open('a') as log:\n"
                  + " log.write(json.dumps(sys.argv)+'\\n')\n")
        native = fake(self.directory / (name + "-native"), prefix + "sys.stdout.buffer.write(" + repr(native_output) + ")\n")
        lean = fake(self.directory / (name + "-lean"), prefix + "sys.stdout.buffer.write(" + repr(lean_output) + ")\n")
        consumer = fake(self.directory / (name + "-consumer"), prefix + consumer_body)
        args = argparse.Namespace(manifest=str(MANIFEST), native=str(native), lean=str(lean),
                                  consumer=str(consumer), out=str(self.directory / name))
        return args, calls

    def assert_pair_stop(self, args, calls, code, *, reason="semantic-discrepancy"):
        saved = Path(args.out)
        run = json.loads((saved / "run.json").read_text())
        self.assertEqual(code, 1)
        self.assertTrue(run["sealed"])
        self.assertEqual(run["completion"], "INCOMPLETE")
        self.assertEqual(run["stop_reason"], reason)
        self.assertEqual(len(run["invocations"]), 2)
        self.assertEqual(len(run["missing_invocations"]), 190)
        logged = [json.loads(line) for line in calls.read_text().splitlines()]
        self.assertEqual(len(logged), 4)
        self.assertEqual(sum(command[1:3] == ["consume", "accepted"] for command in logged), 2)
        self.assertEqual([Path(command[-1]).name for command in logged if command[1:3] != ["consume", "accepted"]],
                         ["source-rejections.sexp"] * 2)
        for record in run["invocations"]:
            self.assertEqual(record["exit_code"], 0)
            self.assertIsNone(record["failure"])
            self.assertIsNone(record["driver_failure"])
            for entry in (record, record["consumer"]):
                for stream in ("stdout", "stderr"):
                    data = (saved / entry[stream + "_path"]).read_bytes()
                    self.assertEqual(digest(data), run["artifacts"][entry[stream + "_path"]])
        checkpoint = run["semantic_discrepancy"]
        self.assertEqual(run["pair_checkpoints"], [checkpoint])
        self.assertFalse(checkpoint["passed"])
        self.assertEqual(checkpoint["case_id"], "source-rejections")
        replay = self.directory / (saved.name + "-replay")
        with patch.object(runner.subprocess, "run", side_effect=AssertionError("replay spawned")), \
             patch.object(runner.subprocess, "Popen", side_effect=AssertionError("replay spawned")):
            self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved), out=str(replay))), 1)
        for path in ("run.json", "run.sha256", "results.jsonl", "summary.json", "summary.tsv"):
            self.assertEqual((saved / path).read_bytes(), (replay / path).read_bytes())
        OBSERVATIONS.append({"probe": saved.name, "exit_code": code, "completion": run["completion"],
            "stop_reason": reason, "semantic_discrepancy": checkpoint, "driver_invocations": 2,
            "consumer_invocations": 2, "missing_invocations": 190, "next_case_invoked": False,
            "production_driver_invocations": 0, "real_consumer_invocations": 0, "replay_subprocesses": 0,
            "raw_captures_preserved": True, "byte_identical_replay": True,
            "repository_preflight": "fake-process fixture adapter"})
        return run

    def first_case_output(self, *, wrong=False):
        forms = copy.deepcopy(self.oracles[self.manifest["cases"][0]["case_id"]]["expected"]["results"])
        if wrong:
            forms[0][2] = "intentionally-wrong-driver-label"
        return b"".join(canonical(f) for f in forms)

    def test_same_valid_wrong_first_pair_stops_before_next_case(self):
        output = self.first_case_output(wrong=True)
        args, calls = self.pair_programs("same-valid-wrong-first-pair", output, output)
        run = self.assert_pair_stop(args, calls, runner.measure(args))
        predicates = run["semantic_discrepancy"]["required_predicates"]
        self.assertTrue(predicates["driver_agreement"])
        self.assertTrue(predicates["locality_sound"])
        for driver in ("native", "lean"):
            self.assertTrue(predicates[driver + ".protocol_valid"])
            self.assertTrue(predicates[driver + ".consumer_accepted"])
            self.assertFalse(predicates[driver + ".oracle_agreement"])
        # Rehashing metadata cannot substitute an ungrounded semantic verdict.
        tampered = self.directory / "tampered-semantic-checkpoint"
        shutil.copytree(Path(args.out), tampered)
        run["pair_checkpoints"][0]["required_predicates"]["driver_agreement"] = False
        runner.publish_status(tampered, run)
        with self.assertRaisesRegex(ValueError, "semantic checkpoint replay mismatch"):
            runner.validate_saved(tampered, MANIFEST)

    def test_one_driver_disagreement_stops_with_independent_predicates(self):
        args, calls = self.pair_programs("one-driver-disagreement", self.first_case_output(), self.first_case_output(wrong=True))
        run = self.assert_pair_stop(args, calls, runner.measure(args))
        predicates = run["semantic_discrepancy"]["required_predicates"]
        self.assertFalse(predicates["driver_agreement"])
        self.assertTrue(predicates["native.oracle_agreement"])
        self.assertFalse(predicates["lean.oracle_agreement"])
        for driver in ("native", "lean"):
            self.assertTrue(predicates[driver + ".protocol_valid"])
            self.assertTrue(predicates[driver + ".consumer_accepted"])

    def test_protocol_failure_stops_after_both_completed_consumers(self):
        args, calls = self.pair_programs("invalid-protocol-pair", b"invalid protocol\n", b"invalid protocol\n")
        run = self.assert_pair_stop(args, calls, runner.measure(args))
        predicates = run["semantic_discrepancy"]["required_predicates"]
        for driver in ("native", "lean"):
            self.assertFalse(predicates[driver + ".protocol_valid"])
            self.assertTrue(predicates[driver + ".consumer_accepted"])

    def test_locality_counterexample_is_a_separate_failed_requirement(self):
        body = ["impact-body", ["impact-result", ["transition", "accepted-to-accepted"],
            [["query-impact", ["atom", "t"], [["evidence-blocked", "defeated"]],
              [["evidence-blocked", "justified"]], "true", "true"]], [["atom", "t"]], []]]
        output = canonical(["inquiry-result", "1", "fake-locality-counterexample", body])
        args, calls = self.pair_programs("locality-counterexample-pair", output, output)
        run = self.assert_pair_stop(args, calls, runner.measure(args))
        predicates = run["semantic_discrepancy"]["required_predicates"]
        self.assertFalse(predicates["locality_sound"])
        self.assertTrue(predicates["driver_agreement"])
        for driver in ("native", "lean"):
            self.assertTrue(predicates[driver + ".protocol_valid"])
            self.assertTrue(predicates[driver + ".consumer_accepted"])

    def test_completed_consumer_refusal_or_noise_is_semantic_not_driver_failure(self):
        for name, body in (("refusal", "raise SystemExit(1)\n"), ("stdout", "print('unexpected noise')\n"),
                           ("stderr", "print('unexpected noise',file=sys.stderr)\n")):
            with self.subTest(name=name):
                args, calls = self.pair_programs("consumer-" + name + "-pair", self.first_case_output(), self.first_case_output(), body)
                run = self.assert_pair_stop(args, calls, runner.measure(args))
                predicates = run["semantic_discrepancy"]["required_predicates"]
                self.assertTrue(predicates["driver_agreement"])
                for driver in ("native", "lean"):
                    self.assertTrue(predicates[driver + ".oracle_agreement"])
                    self.assertTrue(predicates[driver + ".protocol_valid"])
                    self.assertFalse(predicates[driver + ".consumer_accepted"])
                    self.assertIsNone(run["invocations"][0]["consumer"]["failure"])

    def test_consumer_signal_still_stops_early_as_infrastructure_failure(self):
        args, calls = self.pair_programs("consumer-signal", self.first_case_output(), self.first_case_output(),
                                       "import os,signal\nos.kill(os.getpid(),signal.SIGTERM)\n")
        self.assertEqual(runner.measure(args), 1)
        run = json.loads((Path(args.out) / "run.json").read_text())
        self.assertEqual(run["stop_reason"], "signal")
        self.assertTrue(run["sealed"])
        self.assertEqual(len(run["invocations"]), 1)
        self.assertEqual(len(run["missing_invocations"]), 191)
        self.assertEqual(len(calls.read_text().splitlines()), 2)
        self.assertIsNone(run["invocations"][0]["failure"])
        self.assertIsNone(run["invocations"][0]["driver_failure"])
        self.assertEqual(run["invocations"][0]["consumer"]["signal"], 15)
        self.assertEqual(run["pair_checkpoints"], [])
        self.assertIsNone(run["semantic_discrepancy"])

    def test_interruption_between_pair_scoring_and_checkpoint_publication_keeps_discrepancy(self):
        output = self.first_case_output(wrong=True)
        args, calls = self.pair_programs("interrupted-semantic-checkpoint", output, output)
        original_publish = runner.publish_status
        interrupted = []
        def interrupt_checkpoint(directory, run):
            if not interrupted and (run.get("active_operation") or {}).get("stage") == "pair-checkpoint":
                interrupted.append(True)
                raise KeyboardInterrupt("test-only interrupt before semantic checkpoint publication")
            return original_publish(directory, run)
        with patch.object(runner, "publish_status", side_effect=interrupt_checkpoint):
            code = runner.measure(args)
        run = self.assert_pair_stop(args, calls, code, reason="interrupted")
        self.assertEqual(interrupted, [True])
        self.assertEqual(run["failed_or_interrupted_operation"], {"case_id": "source-rejections", "stage": "pair-checkpoint"})

    def test_report_recovery_keeps_semantic_discrepancy_separate(self):
        output = self.first_case_output(wrong=True)
        for name, exception, reason in (("io", OSError("test-only semantic report IO failure"), "evidence-io-failure"),
                                        ("deadline", runner.AggregateDeadline("test-only semantic publication deadline"), "aggregate-deadline")):
            with self.subTest(name=name):
                args, calls = self.pair_programs("semantic-report-recovery-" + name, output, output)
                original_seal = runner.seal
                def fail_after_seal(*values):
                    original_seal(*values)
                    raise exception
                with patch.object(runner, "seal", side_effect=fail_after_seal):
                    code = runner.measure(args)
                run = self.assert_pair_stop(args, calls, code, reason=reason)
                self.assertEqual(run["recovery"]["driver_retries"], 0)
                self.assertEqual(run["recovery"]["consumer_retries"], 0)
                self.assertEqual(len(run["recovery"]["prior_report_artifacts"]), 3)

    def test_consumer_failure_keeps_driver_oracle_field_independent(self):
        case = self.manifest["cases"][0]
        oracle = self.oracles[case["case_id"]]
        output = b"".join(canonical(f) for f in oracle["expected"]["results"])
        record = {"exit_code": 0, "failure": "consumer-failure", "driver_failure": None,
                  "consumer": {"accepted": False}}
        result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                            {"native": (record, output, b"")})
        self.assertTrue(result["drivers"]["native"]["oracle_agreement"])
        self.assertFalse(result["drivers"]["native"]["consumer_accepted"])

    def test_atomic_limit_refusal_enforced(self):
        refusal = ["inquiry-error", "1", [], ["limit", ["counter", "pairs"], ["actual", "5"], ["cap", "4"]]]
        self.assertEqual(protocol(canonical(refusal), 1), [refusal])
        with self.assertRaises(ValueError):
            protocol(canonical(refusal), 0)
        with self.assertRaises(ValueError):
            protocol(canonical(refusal) * 2, 1)
        wrong = copy.deepcopy(refusal)
        wrong[3][2][1] = "4"
        with self.assertRaises(ValueError):
            protocol(canonical(wrong), 1)

    def test_public_status_absence_is_an_accepted_value(self):
        body = ["status-body", ["family-status-result", [["family-row", [], [], [], []]], "1", "1", "0", "true"]]
        info = diagnostics([["inquiry-result", "1", "absent", body]], [],
                           {"semantic_specification": {}}, {"catalog": []})
        self.assertTrue(info["requests"][0]["accepted_status_stable"])
        self.assertEqual(info["requests"][0]["rows"][0]["public_status"], None)
        self.assertEqual(info["snapshot_only"]["rows"], [])

    def test_catalog_original_and_retain_last_projection_are_distinct(self):
        first = ["literal", ["slot-eq", ["slot-id", "0"], ["choice-id", "0"]]]
        second = ["literal", ["slot-ne", ["slot-id", "1"], ["choice-id", "1"]]]
        catalog = [first, second, first]
        body = ["assumptions-body", ["assumption-result", ["target", ["audit-target", "c", "w", []]], catalog, "1", []]]
        info = diagnostics([["inquiry-result", "1", "catalog", body]], [["assumption-catalog", *catalog]],
                           {"semantic_specification": {}}, {"catalog": catalog})["requests"][0]
        self.assertEqual(info["captured_catalog"], catalog)
        self.assertEqual(info["catalog_before_count"], 3)
        self.assertEqual(info["catalog_after_dedup"], [second, first])
        self.assertEqual(info["subsets_examined"]["value"], 4)

    def test_grounded_locality_needs_equal_blocking_for_full_status(self):
        def projected(before, after):
            body = ["impact-body", ["impact-result", ["transition", "accepted-to-accepted"],
                [["query-impact", ["atom", "t"], [before], [after], "true", "true"]], [["atom", "t"]], []]]
            return diagnostics([["inquiry-result", "1", "locality", body]], [],
                {"semantic_specification": {}}, {"catalog": []})["requests"][0]["queries"][0]
        blocking_change = projected(["published", "justified"], ["evidence-blocked", "justified"])
        self.assertTrue(blocking_change["grounded_locality"])
        self.assertFalse(blocking_change["certified_unchanged"])
        self.assertFalse(blocking_change["locality_counterexample"])
        conditional_change = projected(["evidence-blocked", "defeated"], ["evidence-blocked", "justified"])
        self.assertTrue(conditional_change["certified_unchanged"])
        self.assertTrue(conditional_change["locality_counterexample"])

    def test_rejected_pair_compares_exact_bound_payloads_not_null_statuses(self):
        case = next(c for c in self.manifest["cases"] if c["case_id"] == "T04")
        original = self.oracles["T04"]
        from evidence_measured import parse
        document = parse((self.base / case["input_path"]).read_bytes())
        def projection(doc, forms, annotations):
            return diagnostics(forms, doc, {"semantic_specification": {"rejections": annotations}}, case)["requests"][0]
        same = projection(document, original["expected"]["results"], original["semantic_specification"]["rejections"])
        self.assertIsNone(same["queries"][0]["actually_equal_full_status"])
        self.assertFalse(same["queries"][0]["full_status_comparison_applicable"])
        self.assertEqual(same["rejected_endpoint_comparison"]["comparison"], "equal")
        unknown = projection(document, original["expected"]["results"][:1], original["semantic_specification"]["rejections"])
        self.assertEqual(unknown["rejected_endpoint_comparison"]["comparison"], "unknown")
        unrelated = copy.deepcopy(document)
        requests = next(b for b in unrelated if isinstance(b, list) and b and b[0] == "requests")
        requests[2][2] = ["unrelated-source"]
        unrelated_info = projection(unrelated, original["expected"]["results"], original["semantic_specification"]["rejections"])
        self.assertEqual(unrelated_info["rejected_endpoint_comparison"]["comparison"], "unknown")
        self.assertFalse(unrelated_info["rejection_annotations"]["verified_by_captured_endpoint_certificate"])
        # Explicit fake certificate/capture data exercises the different-payload
        # join; it does not claim that the real verifier accepted modified bytes.
        different = copy.deepcopy(document)
        requests = next(b for b in different if isinstance(b, list) and b and b[0] == "requests")
        cert = requests[2][4]
        after_rejection = copy.deepcopy(cert[9][2][0])
        after_rejection[-1][-1][-1][-1] = "other"
        cert[9][2] = [after_rejection]
        annotated = [original["semantic_specification"]["rejections"][0], after_rejection]
        different_info = projection(different, original["expected"]["results"], annotated)
        self.assertEqual(different_info["rejected_endpoint_comparison"]["comparison"], "different")
        unannotated = diagnostics(original["expected"]["results"], document,
            {"semantic_specification": {}}, case)["requests"][0]
        self.assertEqual(unannotated["rejected_endpoint_comparison"]["comparison"], "unknown")

    def test_process_flag_counts_do_not_hide_timeout_kills(self):
        records = [{"timeout": True, "signal": 9, "spawn_failure": None, "failure": "timeout", "exit_code": -9},
                   {"timeout": False, "signal": 15, "spawn_failure": None, "failure": "signal", "exit_code": -15},
                   {"timeout": False, "signal": None, "spawn_failure": "missing", "failure": "spawn-failure", "exit_code": None}]
        for consumer in (False, True):
            counts = process_counts(records, consumer=consumer)
            self.assertEqual(counts["invocation_attempt_denominator"], 3)
            self.assertEqual(counts["timeouts"]["numerator"], 1)
            self.assertEqual(counts["all_signaled_processes"]["numerator"], 2)
            self.assertEqual(counts["independent_signal_failures"]["numerator"], 1)
            self.assertEqual(counts["spawn_failures"]["numerator"], 1)
            self.assertEqual(counts["completed_without_infrastructure_failure"]["numerator"], 0)

    def test_declared_development_audit_profiles_and_embedded_queries_preserved(self):
        from evidence_measured import parse
        for name in ("fixed-witness", "hypothetical-audit", "forged-observed"):
            case = next(c for c in self.manifest["cases"] if c["case_id"] == name)
            oracle = self.oracles[name]
            info = diagnostics(oracle["expected"]["results"], parse((self.base / case["input_path"]).read_bytes()), oracle, case)
            request = next(r for r in info["requests"] if r["body_kind"] == "audit-body")
            self.assertEqual(request["declared_fixed_witness_input"]["profile"], request["original_request_ast"][4])
            self.assertFalse(request["declared_fixed_witness_input"]["independent_component_annotation_available"])
            self.assertIn("bindings", info["declared_input_annotations"]["values"])
            self.assertIn("process_input", info["declared_input_annotations"]["values"])
        case = next(c for c in self.manifest["cases"] if c["case_id"] == "verified-certificate")
        oracle = self.oracles[case["case_id"]]
        info = diagnostics(oracle["expected"]["results"], parse((self.base / case["input_path"]).read_bytes()), oracle, case)
        self.assertEqual(info["requests"][0]["original_request_ast"][:2], ["verdict", "v0"])

    def test_recoverable_report_write_failure_preserves_raw_and_seals_incomplete(self):
        program = fake(self.directory / "fake-write-failure", "import os,signal\nprint('immutable raw prefix',flush=True)\nos.kill(os.getpid(),signal.SIGTERM)\n")
        consumer = fake(self.directory / "fake-write-failure-consumer", "raise SystemExit(0)\n")
        saved = self.directory / "write-failure"
        original_write = runner.write_new
        failures = []
        def fail_once(path, data):
            if path.name == "summary.json" and not failures:
                failures.append("one-shot summary publication failure")
                raise OSError(failures[-1])
            return original_write(path, data)
        with patch.object(runner, "write_new", side_effect=fail_once):
            code = runner.measure(argparse.Namespace(manifest=str(MANIFEST), native=str(program), lean=str(program),
                consumer=str(consumer), out=str(saved)))
        self.assertEqual(code, 1)
        run = json.loads((saved / "run.json").read_text())
        self.assertTrue(run["sealed"])
        self.assertEqual(run["completion"], "INCOMPLETE")
        self.assertEqual(run["stop_reason"], "evidence-io-failure")
        self.assertEqual(len(run["invocations"]), 1)
        self.assertEqual(len(run["missing_invocations"]), 191)
        self.assertEqual(run["recovery"]["driver_retries"], 0)
        raw = saved / run["invocations"][0]["stdout_path"]
        self.assertEqual(raw.read_bytes(), b"immutable raw prefix\n")
        self.assertEqual(digest(raw.read_bytes()), run["invocations"][0]["stdout_sha256"])
        self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved),
            out=str(self.directory / "write-failure-replay"))), 1)
        OBSERVATIONS.append({"probe": "recoverable one-shot report IO failure", "exit_code": code,
            "completion": run["completion"], "stop_reason": run["stop_reason"], "sealed": run["sealed"],
            "driver_invocations": 1, "driver_retries": 0, "production_driver_invocations": 0,
            "stdout_sha256": run["invocations"][0]["stdout_sha256"], "raw_prefix_preserved": True})

    def test_rejected_comparison_summary_keeps_certificate_context(self):
        rows = []
        for name in ("impact-rejected", "T04"):
            case = next(c for c in self.manifest["cases"] if c["case_id"] == name)
            oracle = self.oracles[name]
            stdout = b"".join(canonical(f) for f in oracle["expected"]["results"])
            record = {"exit_code": 0, "failure": None, "consumer": {"accepted": True}}
            rows.append(score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                                  {driver: (record, stdout, b"") for driver in ("native", "lean")}))
        info = summary(rows, self.manifest, {"run_id": "test-only", "completion": "INCOMPLETE",
            "missing_invocations": [{"case_id": "not-part-of-this-test", "driver": "native"}], "aggregate_elapsed_ms": 0})
        for driver in ("native", "lean"):
            self.assertEqual(info["drivers"][driver]["rejected_endpoint_comparison_counts"],
                             {"equal": 1, "different": 0, "unknown": 1})
            self.assertEqual(info["drivers"][driver]["rejected_endpoint_comparison_denominator"], 2)

    def test_nullable_accepted_status_and_consumer_validation_have_explicit_scopes(self):
        case = next(c for c in self.manifest["cases"] if c["case_id"] == "T01")
        oracle = copy.deepcopy(self.oracles["T01"])
        forms = copy.deepcopy(oracle["expected"]["results"])
        forms[0][3][1][2][0][2] = []
        forms[0][3][1][2][0][3] = []
        stdout = b"".join(canonical(f) for f in forms)
        record = {"exit_code": 0, "failure": None, "consumer": {"accepted": True}}
        result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                           {driver: (record, stdout, b"") for driver in ("native", "lean")})
        info = summary([result], self.manifest, {"run_id": "test-only", "completion": "INCOMPLETE",
            "missing_invocations": [], "aggregate_elapsed_ms": 0})
        self.assertEqual(info["drivers"]["native"]["full_status_applicable_query_denominator"], 0)
        self.assertIsNone(info["drivers"]["native"]["actually_unchanged"]["fraction"])
        valid_stdout = b"".join(canonical(f) for f in oracle["expected"]["results"])
        record = {"exit_code": 0, "driver_failure": None, "failure": "consumer-failure", "consumer": {"accepted": False}}
        result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                           {driver: (record, valid_stdout, b"") for driver in ("native", "lean")})
        info = summary([result], self.manifest, {"run_id": "test-only", "completion": "INCOMPLETE",
            "missing_invocations": [], "aggregate_elapsed_ms": 0})
        self.assertEqual(info["oracle_correctness"]["all"]["native"]["numerator"], 1)
        self.assertEqual(info["validated_correctness"]["all"]["native"]["numerator"], 0)

    def test_unattached_capture_retains_original_operation_and_checkpoint(self):
        program = fake(self.directory / "fake-unattached", "import os,signal\nprint('unattached raw prefix',flush=True)\nos.kill(os.getpid(),signal.SIGTERM)\n")
        consumer = fake(self.directory / "fake-unattached-consumer", "raise SystemExit(0)\n")
        saved = self.directory / "unattached"
        original_invoke = runner.invoke
        checkpoints = []
        def fail_attachment(*args, **kwargs):
            checkpoints.append(json.loads((saved / "run.json").read_text()))
            original_invoke(*args, **kwargs)
            raise OSError("one-shot record attachment failure")
        with patch.object(runner, "invoke", side_effect=fail_attachment):
            code = runner.measure(argparse.Namespace(manifest=str(MANIFEST), native=str(program), lean=str(program),
                consumer=str(consumer), out=str(saved)))
        self.assertEqual(code, 1)
        self.assertEqual(checkpoints[0]["completion"], "INCOMPLETE")
        self.assertEqual(len(checkpoints[0]["missing_invocations"]), 192)
        run = json.loads((saved / "run.json").read_text())
        self.assertEqual(run["completion"], "INCOMPLETE")
        self.assertEqual(run["invocations"], [])
        self.assertEqual(len(run["unattached_capture_paths"]), 2)
        self.assertEqual(run["failed_or_interrupted_operation"]["command"][0], str(program))
        self.assertEqual(run["failed_or_interrupted_operation"]["stage"], "driver")
        raw = saved / "raw/source-rejections.native.stdout"
        self.assertEqual(raw.read_bytes(), b"unattached raw prefix\n")
        self.assertEqual(digest(raw.read_bytes()), run["artifacts"]["raw/source-rejections.native.stdout"])
        self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved),
            out=str(self.directory / "unattached-replay"))), 1)
        OBSERVATIONS.append({"probe": "unattached capture IO failure", "exit_code": code,
            "completion": run["completion"], "failed_operation": run["failed_or_interrupted_operation"],
            "unattached_paths": run["unattached_capture_paths"], "production_driver_invocations": 0,
            "stdout_sha256": run["artifacts"]["raw/source-rejections.native.stdout"]})

    def test_publication_deadline_cannot_rescue_incomplete_status(self):
        program = fake(self.directory / "fake-publication-deadline", "import os,signal\nprint('deadline prefix',flush=True)\nos.kill(os.getpid(),signal.SIGTERM)\n")
        consumer = fake(self.directory / "fake-publication-deadline-consumer", "raise SystemExit(0)\n")
        saved = self.directory / "publication-deadline"
        original_seal = runner.seal
        def late_publication(*args, **kwargs):
            original_seal(*args, **kwargs)
            raise runner.AggregateDeadline("test-only publication deadline boundary")
        with patch.object(runner, "seal", side_effect=late_publication):
            code = runner.measure(argparse.Namespace(manifest=str(MANIFEST), native=str(program), lean=str(program),
                consumer=str(consumer), out=str(saved)))
        self.assertEqual(code, 1)
        run = json.loads((saved / "run.json").read_text())
        self.assertEqual(run["completion"], "INCOMPLETE")
        self.assertEqual(run["stop_reason"], "aggregate-deadline")
        self.assertTrue(run["sealed"])
        self.assertEqual(len(run["invocations"]), 1)
        self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved),
            out=str(self.directory / "publication-deadline-replay"))), 1)

    def test_excessive_output_nesting_is_a_retained_decode_failure(self):
        case = self.manifest["cases"][0]
        oracle = self.oracles[case["case_id"]]
        output = b"(" * 1100 + b"x" + b")" * 1100 + b"\n"
        record = {"exit_code": 0, "failure": None, "consumer": {"accepted": False}}
        result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                            {driver: (record, output, b"") for driver in ("native", "lean")})
        for driver in ("native", "lean"):
            self.assertFalse(result["drivers"][driver]["protocol_valid"])
            self.assertFalse(result["drivers"][driver]["oracle_agreement"])
            self.assertFalse(result["drivers"][driver]["consumer_accepted"])
            self.assertEqual(result["drivers"][driver]["decode_error_kind"], "RecursionError")

    def test_malformed_key_and_natural_shapes_are_decode_failures(self):
        case = self.manifest["cases"][0]
        oracle = self.oracles[case["case_id"]]
        for code, output in ((1, b"(inquiry-error 1 () (limit (counter pairs) (actual (1)) (cap 0)))\n"),
                             (1, b"(inquiry-error 1 () (limit (counter pairs) (actual 1) (cap (0))))\n"),
                             (2, b"(inquiry-error 1 () ((unknown) detail))\n"),
                             (0, b"(inquiry-result 1 (label) (wrong body))\n"),
                             (0, b"(inquiry-result 1 label ((wrong) body))\n"),
                             (0, b"(inquiry-result 1 label ())\n"),
                             (0, b"(inquiry-result 1 label wrong)\n"),
                             (0, b"(inquiry-result 1 label (impact-body (impact-result (transition (bad)) () () ())))\n")):
            with self.subTest(output=output):
                record = {"exit_code": code, "failure": None, "consumer": {"accepted": False}}
                with self.assertRaises(ValueError):
                    protocol(output, code)
                result = score_case(case, oracle, (self.base / case["input_path"]).read_bytes(),
                    {driver: (record, output, b"") for driver in ("native", "lean")})
                for driver in ("native", "lean"):
                    self.assertFalse(result["drivers"][driver]["protocol_valid"])
                    self.assertFalse(result["drivers"][driver]["oracle_agreement"])
                    self.assertEqual(result["drivers"][driver]["decode_error_kind"], "ValueError")
                report = summary([result], self.manifest, {"completion": "INCOMPLETE", "missing_invocations": [],
                    "run_id": "test-only-malformed-refusal", "aggregate_elapsed_ms": 0})
                self.assertFalse(report["passed"])

    def test_deep_malformed_fake_process_seals_incomplete_and_replays(self):
        program = fake(self.directory / "fake-deep-output", "import sys\nsys.stdout.buffer.write(b'('*1100+b'x'+b')'*1100+b'\\n')\n")
        consumer = fake(self.directory / "fake-deep-consumer", "raise SystemExit(1)\n")
        saved = self.directory / "deep-output"
        code = runner.measure(argparse.Namespace(manifest=str(MANIFEST), native=str(program), lean=str(program),
            consumer=str(consumer), out=str(saved)))
        self.assertEqual(code, 1)
        run = json.loads((saved / "run.json").read_text())
        self.assertTrue(run["sealed"])
        self.assertEqual(run["completion"], "INCOMPLETE")
        self.assertEqual(run["stop_reason"], "semantic-discrepancy")
        self.assertEqual(len(run["invocations"]), 2)
        self.assertEqual(len(run["missing_invocations"]), 190)
        output = b"(" * 1100 + b"x" + b")" * 1100 + b"\n"
        self.assertEqual((saved / run["invocations"][0]["stdout_path"]).read_bytes(), output)
        result = json.loads((saved / "results.jsonl").read_text().splitlines()[0])
        self.assertFalse(result["drivers"]["native"]["protocol_valid"])
        self.assertFalse(result["drivers"]["native"]["oracle_agreement"])
        self.assertEqual(result["drivers"]["native"]["decode_error_kind"], "RecursionError")
        replay = self.directory / "deep-output-replay"
        with patch.object(runner.subprocess, "run", side_effect=AssertionError("replay spawned")), \
             patch.object(runner.subprocess, "Popen", side_effect=AssertionError("replay spawned")):
            self.assertEqual(runner.replay(argparse.Namespace(manifest=str(MANIFEST), replay=str(saved), out=str(replay))), 1)
        for path in ("run.json", "results.jsonl", "summary.json", "summary.tsv"):
            self.assertEqual((replay / path).read_bytes(), (saved / path).read_bytes())
        OBSERVATIONS.append({"probe": "excessively nested malformed fake process output", "exit_code": code,
            "completion": run["completion"], "sealed": run["sealed"], "decode_error_kind": "RecursionError",
            "oracle_agreement": False, "protocol_valid": False, "driver_invocations": 2,
            "missing_invocations": 190, "production_driver_invocations": 0, "replay_subprocesses": 0,
            "stdout_bytes": len(output), "stdout_sha256": digest(output), "raw_output_preserved": True})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence", type=Path)
    args, rest = parser.parse_known_args()
    program = unittest.main(argv=[sys.argv[0], *rest], exit=False)
    if args.evidence:
        args.evidence.write_bytes(json_bytes({"schema": "inquiry-p8-runner-probes", "schema_version": 1,
            "production_driver_invocations": 0, "real_consumer_invocations": 0,
            "fake_process_repository_preflight": "fixture adapter; committed suite/helper bytes and unchanged load_suite validation",
            "production_repository_preflight": "unmodified rejection test only; changed runtime rejected before driver",
            "tests_run": program.result.testsRun,
            "passed": program.result.wasSuccessful(), "observations": OBSERVATIONS}))
    raise SystemExit(0 if program.result.wasSuccessful() else 1)
