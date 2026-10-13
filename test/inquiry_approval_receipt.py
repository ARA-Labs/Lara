#!/usr/bin/env python3
"""The correction receipt must approve every protocol item that defers to it.

No inquiry implementation, driver, consumer or production preflight is run.
Synthetic approvals stay inside temporary fixtures.
"""
import copy
import json
import shutil
from pathlib import Path
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import inquiry_evaluation_manifest as manifest
CANDIDATE = ROOT / 'evaluation/inquiry-p8-corrected'


def receipt_approvals(protocol):
    return {'approved_amendments': [
                {'id': a['id'], 'approval_text': 'test-only',
                 'interpretation_sha256': manifest.digest(a['interpretation'].encode())}
                for a in protocol.get('amendments', []) if a.get('status') == manifest.RECEIPT_APPROVAL],
            'data_policy_sha256': manifest.digest(manifest.json_bytes(protocol['data_policy']))}


def freeze_copy(base, approvals):
    """Freeze a copy of the real candidate under a test-only receipt."""
    shutil.copytree(CANDIDATE, base)
    protocol_bytes = (base / 'protocol.json').read_bytes()
    manifest_bytes = (base / 'MANIFEST.json').read_bytes()
    (base / 'candidate-protocol.json').write_bytes(protocol_bytes)
    (base / 'candidate-manifest.json').write_bytes(manifest_bytes)
    receipt = {'status': 'APPROVED', 'provenance': 'user', 'researcher': 'test-only',
               'metadata_only_freeze_authorized': True, 'reviewed_candidate_commit': 'a' * 40,
               'candidate_protocol_path': 'candidate-protocol.json',
               'candidate_protocol_sha256': manifest.digest(protocol_bytes),
               'candidate_manifest_path': 'candidate-manifest.json',
               'candidate_manifest_sha256': manifest.digest(manifest_bytes), **approvals}
    receipt_bytes = manifest.json_bytes(receipt)
    (base / 'test-only-approval.json').write_bytes(receipt_bytes)
    frozen_manifest = json.loads(manifest_bytes); frozen_manifest['state'] = 'frozen'
    frozen_manifest_bytes = manifest.json_bytes(frozen_manifest)
    (base / 'MANIFEST.json').write_bytes(frozen_manifest_bytes)
    protocol = json.loads(protocol_bytes)
    protocol['freeze']['state'] = 'frozen'
    protocol['freeze']['manifest_sha256'] = manifest.digest(frozen_manifest_bytes)
    protocol['correction_approval'] = {'state': 'approved', 'path': 'test-only-approval.json',
                                       'sha256': manifest.digest(receipt_bytes)}
    (base / 'protocol.json').write_bytes(manifest.json_bytes(protocol))


class ReceiptApprovals(unittest.TestCase):
    def test_candidate_defers_t07_amendment_and_data_policy(self):
        protocol = json.loads((CANDIDATE / 'protocol.json').read_text())
        deferred = [a['id'] for a in protocol['amendments'] if a.get('status') == manifest.RECEIPT_APPROVAL]
        self.assertEqual(deferred, ['distinct-t07-support'])
        self.assertEqual(protocol['data_policy']['state'], manifest.RECEIPT_APPROVAL)

    def test_receipt_must_bind_each_deferred_meaning(self):
        protocol = json.loads((CANDIDATE / 'protocol.json').read_text())
        receipt = receipt_approvals(protocol)
        manifest.require_receipt_approvals(protocol, receipt)
        for name, change, error in [
                ('missing amendment', lambda r, p: r.update(approved_amendments=[]), 'amendment: distinct-t07-support'),
                ('empty approval text', lambda r, p: r['approved_amendments'][0].update(approval_text=''), 'amendment: distinct-t07-support'),
                ('blank approval text', lambda r, p: r['approved_amendments'][0].update(approval_text=' '), 'amendment: distinct-t07-support'),
                ('non-string approval text', lambda r, p: r['approved_amendments'][0].update(approval_text=True), 'amendment: distinct-t07-support'),
                ('repeated amendment id', lambda r, p: r['approved_amendments'].insert(0, {'id': 'distinct-t07-support'}), 'repeats an amendment id'),
                ('missing amendment id', lambda r, p: r['approved_amendments'][0].pop('id'), 'string ids'),
                ('non-string amendment id', lambda r, p: r['approved_amendments'][0].update(id=['distinct-t07-support']), 'string ids'),
                ('amendments not a list', lambda r, p: r.update(approved_amendments={}), 'not a list of objects'),
                ('amendment entry not an object', lambda r, p: r.update(approved_amendments=['distinct-t07-support']), 'not a list of objects'),
                ('other interpretation', lambda r, p: p['amendments'][1].update(interpretation='changed'), 'amendment: distinct-t07-support'),
                ('missing data policy', lambda r, p: r.pop('data_policy_sha256'), 'data policy'),
                ('other data policy', lambda r, p: p['data_policy'].update(fresh_measurement_runs=2), 'data policy'),
                ('proposed data policy', lambda r, p: p['data_policy'].update(state='proposed'), 'data policy'),
                ('null data policy', lambda r, p: p.update(data_policy=None), 'data policy'),
                ('proposed amendment', lambda r, p: p['amendments'][1].update(status='proposed'), 'lacks researcher approval')]:
            with self.subTest(name):
                r, p = copy.deepcopy(receipt), copy.deepcopy(protocol)
                change(r, p)
                with self.assertRaisesRegex(ValueError, error):
                    manifest.require_receipt_approvals(p, r)

    def test_frozen_candidate_copy_loads_only_with_receipt_approvals(self):
        protocol = json.loads((CANDIDATE / 'protocol.json').read_text())
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / 'approved'
            freeze_copy(base, receipt_approvals(protocol))
            _, loaded_protocol, _, _, inventory = manifest.load_suite(base / 'MANIFEST.json')
            self.assertEqual(loaded_protocol['data_policy'], protocol['data_policy'])
            self.assertIn('test-only-approval.json', inventory)
            base = Path(tmp) / 'unapproved'
            freeze_copy(base, {})
            with self.assertRaisesRegex(ValueError, 'does not approve amendment'):
                manifest.load_suite(base / 'MANIFEST.json')
            base = Path(tmp) / 'amendment-only'
            approvals = receipt_approvals(protocol); del approvals['data_policy_sha256']
            freeze_copy(base, approvals)
            with self.assertRaisesRegex(ValueError, 'does not approve the data policy'):
                manifest.load_suite(base / 'MANIFEST.json')


if __name__ == '__main__':
    unittest.main()
