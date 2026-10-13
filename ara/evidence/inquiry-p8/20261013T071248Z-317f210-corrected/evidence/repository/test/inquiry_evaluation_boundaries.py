#!/usr/bin/env python3
"""Regression tests for review binding and immutable P8 authoring boundaries."""
import contextlib
from copy import deepcopy
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import inquiry_evaluation_cases as author


class AuthoringBoundaries(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='inquiry-p8-boundary-')
        self.addCleanup(self.temp.cleanup)
        self.suite = Path(self.temp.name) / 'suite'
        shutil.copytree(author.SUITE, self.suite)
        self.suite_patch = patch.object(author, 'SUITE', self.suite)
        self.suite_patch.start()
        self.addCleanup(self.suite_patch.stop)

    def manifest(self):
        return json.loads((self.suite / 'MANIFEST.json').read_text())

    def freeze(self):
        manifest = self.manifest()
        manifest['state'] = 'frozen'
        (self.suite / 'MANIFEST.json').write_bytes(author.js(manifest))

    def snapshot(self):
        return {str(p.relative_to(self.suite)): (p.read_bytes(), p.stat().st_mtime_ns)
                for p in self.suite.rglob('*') if p.is_file()}

    def test_limit_edit_cannot_inherit_review_with_unchanged_semantics(self):
        manifest = self.manifest()
        manifest['state'] = 'awaiting-independent-review'
        entry = next(e for e in manifest['cases'] if e['case_id'] == 'T13')
        path = self.suite / entry['oracle_path']
        oracle = json.loads(path.read_text())
        provenance = deepcopy(oracle['review_provenance'])
        provenance.update(status='reviewed', reviewer='test reviewer',
                          reviewed_input_sha256=entry['input_sha256'],
                          semantic_content_sha256=author.semantic_digest(oracle))
        oracle['review_provenance'] = provenance
        entry['review_provenance'] = provenance
        path.write_bytes(author.js(oracle))
        entry['oracle_sha256'] = author.sha(path.read_bytes())
        (self.suite / 'MANIFEST.json').write_bytes(author.js(manifest))
        original = author.authored

        def changed_limit():
            seeds = original()
            author.block(author.block(seeds['T13'][0], 'inquiry-limits'), 'pairs')[1] = '999'
            return seeds

        with patch.object(author, 'authored', changed_limit):
            outputs = author.materialize()
        changed = json.loads(outputs[path])
        self.assertEqual(oracle['expected'], changed['expected'])
        self.assertEqual(oracle['semantic_specification'], changed['semantic_specification'])
        self.assertEqual(changed['review_provenance']['status'], 'pending-independent-review')
        self.assertNotEqual(author.sha(outputs[self.suite / entry['input_path']]), entry['input_sha256'])

    def test_review_requires_ancestry_and_optional_receipt_digests(self):
        entry = next(e for e in self.manifest()['cases'] if e['case_id'] == 'T13')
        oracle = json.loads((self.suite / entry['oracle_path']).read_text())
        data = (self.suite / entry['input_path']).read_bytes()
        self.assertTrue(author.review_matches(oracle, entry, oracle, data, entry['source_ancestry']))
        self.assertFalse(author.review_matches(oracle, entry, oracle, data, {'recipe': 'different'}))
        for key in ['reviewed_input_sha256', 'semantic_content_sha256']:
            bad_oracle, bad_entry = deepcopy(oracle), deepcopy(entry)
            bad_oracle['review_provenance'][key] = '0' * 64
            bad_entry['review_provenance'] = bad_oracle['review_provenance']
            self.assertFalse(author.review_matches(bad_oracle, bad_entry, oracle, data, entry['source_ancestry']))

    def test_unchanged_frozen_check_and_default_are_read_only(self):
        self.freeze()
        before = self.snapshot()
        with contextlib.redirect_stdout(io.StringIO()):
            author.main(['--check'])
            author.main([])
        self.assertEqual(before, self.snapshot())

    def test_changed_frozen_artifacts_refuse_before_any_write(self):
        self.freeze()
        changed = self.suite / 'inputs/T13.sexp'
        changed.write_bytes(changed.read_bytes() + b'\n')
        before = self.snapshot()
        for args in [[], ['--check']]:
            with self.assertRaisesRegex(SystemExit, 'frozen suite differs'):
                author.main(args)
            self.assertEqual(before, self.snapshot())

    def test_frozen_producer_refuses_before_launch_or_cache_write(self):
        self.freeze()
        before = self.snapshot()
        with patch('subprocess.run') as launch:
            with self.assertRaisesRegex(SystemExit, 'frozen suite refuses certificate producer'):
                author.main(['--producer', str(Path(self.temp.name) / 'producer')])
        launch.assert_not_called()
        self.assertEqual(before, self.snapshot())


class IndependentReceiptBoundary(unittest.TestCase):
    tool = ROOT / 'evaluation/inquiry-p8/review/independent_finite_audit.py'

    def test_default_audit_does_not_change_original_receipt(self):
        receipt = ROOT / 'evaluation/inquiry-p8/independent-review.json'
        before = receipt.read_bytes(), receipt.stat().st_mtime_ns
        result = subprocess.run([sys.executable, str(self.tool)], capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr.decode())
        self.assertEqual(json.loads(result.stdout)['status'], 'PASS')
        self.assertEqual(before, (receipt.read_bytes(), receipt.stat().st_mtime_ns))

    def test_existing_output_refuses_before_reading_suite(self):
        with tempfile.TemporaryDirectory(prefix='inquiry-p8-receipt-') as temp:
            root = Path(temp)
            tool = root / 'evaluation/inquiry-p8/review/independent_finite_audit.py'
            tool.parent.mkdir(parents=True)
            shutil.copyfile(self.tool, tool)
            # No manifest exists in this copy. Existing-output refusal must
            # precede suite loading, and preserve its exact bytes and timestamp.
            receipt = root / 'existing.json'
            receipt.write_bytes(b'original review receipt\n')
            before = receipt.read_bytes(), receipt.stat().st_mtime_ns
            result = subprocess.run([sys.executable, str(tool), '--out', str(receipt)], capture_output=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn(b'audit not started', result.stderr)
            self.assertEqual(before, (receipt.read_bytes(), receipt.stat().st_mtime_ns))


if __name__ == '__main__':
    unittest.main()
