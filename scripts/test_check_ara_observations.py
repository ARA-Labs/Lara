import contextlib
import copy
import importlib.util
import io
import json
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

import yaml


SCRIPT = Path(__file__).with_name("check_ara_observations.py")


def load_checker():
    spec = importlib.util.spec_from_file_location("check_ara_observations", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def digest(record):
    identity = {key: value for key, value in record.items()
                if key not in ("promoted", "promoted_to", "crystallized_via", "stale")}
    return hashlib.sha256(json.dumps(identity, ensure_ascii=False, sort_keys=True,
                                     separators=(",", ":"), default=str).encode()).hexdigest()


class ObservationLookupTests(unittest.TestCase):
    def setUp(self):
        self.checker = load_checker()
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / "ara/staging").mkdir(parents=True)
        (self.root / "ara/trace").mkdir()
        self.rows = [
            {"id": old, "timestamp": time, "bound_to": [node], "content": content}
            for old, time, node, content in (
                ("O176", "early", "N326", "identity"),
                ("O177", "early", "N327", "derivation"),
                ("O176", "late", "N334_cli", "process"),
                ("O177", "late", "N334_gate", "decoder"),
            )
        ]
        self.rows.append({"id": "O189", "timestamp": "now", "bound_to": [], "content": "unique"})
        self.registry = {"schema_version": 1, "aliases": [
            {"canonical_id": new, "historical_id": row["id"],
             "timestamp": row["timestamp"], "bound_to": row["bound_to"],
             "record_sha256": digest(row)}
            for new, row in zip(("O190", "O191", "O192", "O193"), self.rows)
        ], "references": []}
        self.registry["aliases"][0]["prior_ids"] = ["O174"]
        self.registry["aliases"][1]["prior_ids"] = ["O175"]

    def tearDown(self):
        self.temp.cleanup()

    def write_inputs(self):
        (self.root / "ara/staging/observations.yaml").write_text(yaml.safe_dump({"observations": self.rows}))
        (self.root / "ara/staging/observation_aliases.yaml").write_text(yaml.safe_dump(self.registry))

    def load(self):
        self.write_inputs()
        return self.checker.load_observations(self.root)

    def add_reference(self, identifier="O176", canonical="O192", kind="lookup"):
        text = f"staged {identifier}\n"
        path = self.root / "ara/trace/note.md"
        path.write_text(text)
        target = next(alias for alias in self.registry["aliases"] if alias["canonical_id"] == canonical)
        self.registry["references"].append({
            "path": "ara/trace/note.md", "line": 1,
            "line_sha256": hashlib.sha256(text.rstrip("\n").encode()).hexdigest(),
            "kind": kind, "reason": "historical context",
            "bindings": ([] if kind == "aggregate" else [{
                "historical_id": identifier, "canonical_id": canonical,
                "record_sha256": target["record_sha256"],
            }]),
        })

    def test_unique_canonical_ids_distinguish_all_four_records(self):
        index = self.load()
        self.assertEqual([index.lookup(i)["content"] for i in ("O190", "O191", "O192", "O193")],
                         ["identity", "derivation", "process", "decoder"])
        self.assertEqual(index.lookup("O189")["content"], "unique")

    def test_bare_duplicate_lookup_fails_closed(self):
        index = self.load()
        for identifier in ("O176", "O177"):
            with self.subTest(identifier=identifier), self.assertRaisesRegex(ValueError, "ambiguous"):
                index.lookup(identifier)

    def test_unregistered_duplicate_fails_closed(self):
        self.registry["aliases"].pop()
        with self.assertRaisesRegex(ValueError, "unregistered duplicate"):
            self.load()

    def test_future_duplicate_even_of_unique_id_is_rejected(self):
        self.rows.append(copy.deepcopy(self.rows[-1]))
        with self.assertRaisesRegex(ValueError, "unregistered duplicate"):
            self.load()

    def test_wrong_occurrence_binding_is_rejected(self):
        self.registry["aliases"][0]["bound_to"] = ["N334_cli"]
        with self.assertRaisesRegex(ValueError, "occurrence"):
            self.load()

    def test_changed_record_is_rejected(self):
        self.rows[0]["content"] = "rewritten history"
        with self.assertRaisesRegex(ValueError, "fingerprint"):
            self.load()

    def test_forward_promotion_updates_preserve_canonical_and_contextual_lookup(self):
        self.add_reference(canonical="O190")
        self.rows[0].update(promoted=True, promoted_to="logic/claims.md:C99",
                            crystallized_via="verbal-affirmation")
        index = self.load()
        self.assertTrue(index.lookup("O190")["promoted"])
        self.assertEqual(index.lookup("O176", source="ara/trace/note.md", line=1)["promoted_to"],
                         "logic/claims.md:C99")

    def test_each_sanctioned_state_field_can_change_without_rebinding(self):
        for field, value in (("promoted", True), ("promoted_to", "logic/claims.md:C99"),
                             ("crystallized_via", "artifact-commitment"), ("stale", True)):
            with self.subTest(field=field):
                self.rows[0][field] = value
                self.assertEqual(self.load().lookup("O190")[field], value)
                del self.rows[0][field]

    def test_immutable_occurrence_fields_cannot_change(self):
        for field, value in (("content", "different"), ("provenance", "human-endorsed"),
                             ("timestamp", "different"), ("bound_to", ["other"]),
                             ("context", "rewritten"), ("potential_type", "claim")):
            with self.subTest(field=field):
                original = copy.deepcopy(self.rows[0])
                self.rows[0][field] = value
                with self.assertRaisesRegex(ValueError, "occurrence|fingerprint"):
                    self.load()
                self.rows[0] = original

    def test_unknown_state_field_is_not_exempt_from_fingerprint(self):
        self.rows[0]["future_maturity_flag"] = True
        with self.assertRaisesRegex(ValueError, "fingerprint"):
            self.load()

    def test_canonical_id_cannot_shadow_original_id(self):
        self.registry["aliases"][0]["canonical_id"] = "O189"
        with self.assertRaisesRegex(ValueError, "canonical"):
            self.load()

    def test_repeated_alias_cannot_bind_same_occurrence(self):
        self.registry["aliases"][1] = copy.deepcopy(self.registry["aliases"][0])
        self.registry["aliases"][1]["canonical_id"] = "O194"
        with self.assertRaisesRegex(ValueError, "occurrence"):
            self.load()

    def test_unknown_lookup_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "unknown"):
            self.load().lookup("O999")

    def test_contextual_lookup_resolves_historical_reference(self):
        self.add_reference()
        index = self.load()
        self.assertEqual(index.lookup("O176", source="ara/trace/note.md", line=1)["content"], "process")

    def test_unregistered_reference_is_rejected(self):
        (self.root / "ara/trace/note.md").write_text("staged O176\n")
        with self.assertRaisesRegex(ValueError, "unaudited"):
            self.load()

    def test_changed_reference_is_rejected(self):
        self.add_reference()
        (self.root / "ara/trace/note.md").write_text("other O176\n")
        with self.assertRaisesRegex(ValueError, "reference fingerprint"):
            self.load()

    def test_wrong_reference_occurrence_is_rejected(self):
        self.add_reference()
        self.registry["references"][0]["bindings"][0]["canonical_id"] = "O190"
        with self.assertRaisesRegex(ValueError, "reference occurrence"):
            self.load()

    def test_reference_cannot_bind_to_other_historical_id(self):
        self.add_reference(canonical="O191")
        with self.assertRaisesRegex(ValueError, "reference occurrence"):
            self.load()

    def test_aggregate_reference_cannot_be_used_as_lookup(self):
        self.add_reference(kind="aggregate")
        index = self.load()
        with self.assertRaisesRegex(ValueError, "non-lookup"):
            index.lookup("O176", source="ara/trace/note.md", line=1)

    def test_contextual_premerge_spelling_does_not_change_global_unique_id(self):
        self.rows.append({"id": "O174", "timestamp": "elsewhere", "bound_to": [], "content": "nesting"})
        self.add_reference(identifier="O174", canonical="O190")
        index = self.load()
        self.assertEqual(index.lookup("O174")["content"], "nesting")
        self.assertEqual(index.lookup("O174", source="ara/trace/note.md", line=1)["content"], "identity")

    def test_duplicate_yaml_keys_are_rejected(self):
        self.write_inputs()
        (self.root / "ara/staging/observation_aliases.yaml").write_text("schema_version: 1\nschema_version: 1\n")
        with self.assertRaisesRegex(ValueError, "duplicate key"):
            self.checker.load_observations(self.root)

    def test_invalid_registry_shape_is_rejected(self):
        self.registry["aliases"] = "not a list"
        with self.assertRaisesRegex(ValueError, "aliases"):
            self.load()

    def test_missing_registry_is_rejected(self):
        self.write_inputs()
        (self.root / "ara/staging/observation_aliases.yaml").unlink()
        with self.assertRaisesRegex(ValueError, "observation_aliases"):
            self.checker.load_observations(self.root)

    def test_malformed_reference_target_fails_closed(self):
        self.add_reference()
        self.registry["references"][0]["bindings"][0]["canonical_id"] = []
        with self.assertRaisesRegex(ValueError, "reference binding"):
            self.load()

    def test_cli_prints_canonical_lookup_as_original_record(self):
        self.write_inputs()
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            status = self.checker.main(["--repo-root", str(self.root), "--lookup", "O190"])
        self.assertEqual(status, 0)
        payload = json.loads(stdout.getvalue())
        self.assertEqual(payload["lookup_id"], "O190")
        self.assertEqual(payload["observation"], self.rows[0])

    def test_cli_refuses_bare_ambiguous_lookup_without_output(self):
        self.write_inputs()
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            status = self.checker.main(["--repo-root", str(self.root), "--lookup", "O176"])
        self.assertEqual(status, 2)
        self.assertEqual(stdout.getvalue(), "")
        self.assertIn("ambiguous", stderr.getvalue())


if __name__ == "__main__":
    unittest.main()
