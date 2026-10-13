#!/usr/bin/env python3
"""Corrected support identity, draft freeze and input-pin boundaries.

No inquiry implementation, driver, consumer or production preflight is run.
"""
import argparse
import copy
import importlib.util
import json
import shutil
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))
import inquiry_evaluation_cases as author
import inquiry_evaluation_manifest as manifest
from inquiry_support_annotations import support_key, t07_annotations, validate_ground_annotations
from evidence_measured import parse
from inquiry_approval_receipt import freeze_copy, receipt_approvals
spec = importlib.util.spec_from_file_location('corrected_runner', ROOT / 'scripts/inquiry-evaluate.py')
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)
CANDIDATE = ROOT / 'evaluation/inquiry-p8-corrected'


class SupportAnnotations(unittest.TestCase):
    def source(self, corrected=True):
        suite = CANDIDATE if corrected else ROOT / 'evaluation/inquiry-p8'
        tree = parse((suite / 'inputs/T07.sexp').read_bytes())
        source = author.block(tree, 'requests')[1][3]
        return author.program(source), author.policy(source)

    def test_distinct_rule_positive_and_old_clone_negative(self):
        terms = t07_annotations(after=True)
        keys = validate_ground_annotations(*self.source(), terms)
        self.assertNotEqual(keys['attacker'], keys['new-attacker'])
        old = copy.deepcopy(terms)
        old['new-attacker'][1] = 'r-s'
        with self.assertRaisesRegex(ValueError, 'duplicate support key'):
            validate_ground_annotations(*self.source(False), old)

    def test_argument_and_derived_claim_renaming_does_not_change_keys(self):
        p, pol = self.source()
        terms = t07_annotations(after=True)
        original = validate_ground_annotations(p, pol, terms)
        d = next(d for d in p[6][1:] if d[0] == 'da' and d[1][1] == 'new-attacker')
        d[1][1] = 'another-name'; d[1][2] = ['sd', 'another-derived-claim']
        terms['another-name'] = terms.pop('new-attacker')
        self.assertEqual(original['new-attacker'], validate_ground_annotations(p, pol, terms)['another-name'])

    def test_all_support_fields_and_nested_fields_participate(self):
        base = t07_annotations()['consumer']
        changes = [lambda t: t.__setitem__(1, 'other-rule'),
                   lambda t: t[2].append(['x', ['con', 'constant']]),
                   lambda t: t[3][1][3][1].__setitem__(1, 'other-leaf'),
                   lambda t: t[4].append(['question', ['leaf', 'seed']]),
                   lambda t: t[5].append('obligation'),
                   lambda t: t[6].__setitem__(1, 'trusted')]
        for change in changes:
            altered = copy.deepcopy(base); change(altered)
            self.assertNotEqual(support_key(base), support_key(altered))

    def test_incomplete_non_ground_and_unsupported_annotations_fail_closed(self):
        for term in ([['leaf']], [['inst', 'rule']], [['unknown', 'seed']]):
            with self.assertRaises(ValueError):
                support_key(term[0])
        non_ground = t07_annotations()['witness']
        non_ground[2].append(['x', ['var', 'x']])
        with self.assertRaisesRegex(ValueError, 'non-ground'):
            support_key(non_ground)
        terms = t07_annotations(after=True); terms.pop('consumer')
        with self.assertRaisesRegex(ValueError, 'incomplete argument coverage'):
            validate_ground_annotations(*self.source(), terms)
        terms = t07_annotations(after=True); terms['attacker'][1] = 'other-rule'
        with self.assertRaisesRegex(ValueError, 'source/annotation mismatch'):
            validate_ground_annotations(*self.source(), terms)

    def test_source_questions_and_malformed_rules_fail_closed(self):
        p, pol = self.source()
        pol[3][1][9].append(['q', 'mandatory-question', ['apat', 'seed'], ['mandatory']])
        with self.assertRaisesRegex(ValueError, 'rule questions'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))
        p, pol = self.source(); pol[3][1].pop()
        with self.assertRaisesRegex(ValueError, 'malformed source rule'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))

    def test_all_rule_fields_obey_the_bounded_source_shape_contract(self):
        mutations = [(3, ['bogus-rule-mode'], 'rule mode'),
                     (3, ['strict'], 'rule mode'),
                     (4, ['l', ['bogus-proposition']], 'premise proposition'),
                     (4, ['l', ['apat', 'seed', ['pv', 'x']]], 'premise proposition'),
                     (5, ['l', ['no']], 'premise labels'),
                     (6, ['bogus-proposition'], 'conclusion proposition'),
                     (6, ['apat', 't', ['pl', ['tc', 'constant']]], 'conclusion proposition'),
                     (7, ['bogus-bool'], 'allow-trusted boolean'),
                     (7, ['true'], 'allow-trusted boolean'),
                     (8, ['l', ['cref', 'backend', ['integer-natural', '1'], 'digest']], 'certifiers')]
        for index, value, error in mutations:
            with self.subTest(field=index, shape=value):
                p, pol = self.source(); pol[3][1][index] = value
                with self.assertRaisesRegex(ValueError, error):
                    validate_ground_annotations(p, pol, t07_annotations(after=True))

    def test_unreferenced_rule_fields_are_also_checked(self):
        p, pol = self.source()
        unused = copy.deepcopy(pol[3][1]); unused[1] = 'unused-rule'
        unused[6] = ['bogus-proposition']; pol[3].append(unused)
        with self.assertRaisesRegex(ValueError, 'conclusion proposition'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))

    def test_duplicate_or_ambiguous_source_identities_fail_closed(self):
        for tag, error in [('dl', 'duplicate leaf identity'), ('da', 'duplicate argument identity')]:
            p, pol = self.source()
            p[6].append(copy.deepcopy(next(d for d in p[6][1:] if d[0] == tag)))
            with self.assertRaisesRegex(ValueError, error):
                validate_ground_annotations(p, pol, t07_annotations(after=True))
        p, pol = self.source(); pol[3].append(copy.deepcopy(pol[3][1]))
        with self.assertRaisesRegex(ValueError, 'duplicate rule identity'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))
        p, pol = self.source()
        next(d for d in p[6][1:] if d[0] == 'da')[1][1] = 'seed'
        with self.assertRaisesRegex(ValueError, 'ambiguous leaf/argument reference'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))

    def test_source_parameters_and_unreviewed_shapes_fail_closed(self):
        p, pol = self.source(); pol[3][1][2].append(['parameter', 'x'])
        with self.assertRaisesRegex(ValueError, 'non-ground rule parameters'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))
        p, pol = self.source(); p[6][3][1][3][0] = 'new-shape'
        with self.assertRaisesRegex(ValueError, 'unsupported source argument shape'):
            validate_ground_annotations(p, pol, t07_annotations(after=True))


class FreezeBoundaries(unittest.TestCase):
    def test_draft_refuses_measurement_before_any_executable_or_destination(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / 'draft'
            base.mkdir()
            protocol = json.loads((CANDIDATE / 'protocol.json').read_text())
            protocol['freeze']['state'] = 'awaiting-researcher-approval'
            (base / 'protocol.json').write_bytes(manifest.json_bytes(protocol))
            out = Path(tmp) / 'measure'
            args = argparse.Namespace(manifest=str(base / 'MANIFEST.json'), out=str(out),
                                      native='/forbidden', lean='/forbidden', consumer='/forbidden')
            with patch.object(runner, 'executable', side_effect=AssertionError('executable resolved')):
                with self.assertRaises(ValueError):
                    runner.measure(args)
            self.assertFalse(out.exists())

    def test_freeze_marker_alone_does_not_approve_correction(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / 'fixture'
            protocol = json.loads((CANDIDATE / 'protocol.json').read_text())
            freeze_copy(base, receipt_approvals(protocol))
            manifest.load_suite(base / 'MANIFEST.json')
            frozen_protocol = json.loads((base / 'protocol.json').read_text())
            frozen_protocol['correction_approval']['state'] = 'pending-researcher-approval'
            (base / 'protocol.json').write_bytes(manifest.json_bytes(frozen_protocol))
            with self.assertRaises(ValueError):
                manifest.load_suite(base / 'MANIFEST.json')

    def test_approval_binds_both_candidate_protocol_and_case_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)
            original_protocol = (CANDIDATE / 'protocol.json').read_bytes()
            original_manifest = (CANDIDATE / 'MANIFEST.json').read_bytes()
            (base / 'candidate-protocol.json').write_bytes(original_protocol)
            (base / 'candidate-manifest.json').write_bytes(original_manifest)
            receipt = {'status': 'APPROVED', 'provenance': 'user', 'researcher': 'test-only',
                       'metadata_only_freeze_authorized': True, 'reviewed_candidate_commit': 'a' * 40,
                       'candidate_protocol_path': 'candidate-protocol.json',
                       'candidate_protocol_sha256': manifest.digest(original_protocol),
                       'candidate_manifest_path': 'candidate-manifest.json',
                       'candidate_manifest_sha256': manifest.digest(original_manifest)}
            receipt_bytes = manifest.json_bytes(receipt)
            (base / 'test-only-approval.json').write_bytes(receipt_bytes)
            protocol = json.loads(original_protocol)
            protocol['freeze']['state'] = 'frozen'
            protocol['correction_approval'] = {'state': 'approved', 'path': 'test-only-approval.json',
                                               'sha256': manifest.digest(receipt_bytes)}
            altered = json.loads(original_manifest)
            altered['cases'][0]['input_sha256'] = '0' * 64
            altered_bytes = manifest.json_bytes(altered)
            protocol['freeze']['manifest_sha256'] = manifest.digest(altered_bytes)
            (base / 'MANIFEST.json').write_bytes(altered_bytes)
            (base / 'protocol.json').write_bytes(manifest.json_bytes(protocol))
            with self.assertRaisesRegex(ValueError, 'approved candidate inputs'):
                manifest.load_suite(base / 'MANIFEST.json')
            protocol['budget']['max_documents'] = 97
            (base / 'protocol.json').write_bytes(manifest.json_bytes(protocol))
            with self.assertRaisesRegex(ValueError, 'approved candidate protocol changed'):
                manifest.load_suite(base / 'MANIFEST.json')

    def test_approved_metadata_only_freeze_retains_support_and_review_identities(self):
        # Synthetic approval is confined to this temporary fixture. Original
        # frozen bytes provide a complete hash/review/partition fixture, and no
        # executable or repository preflight is used.
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp) / 'fixture'
            shutil.copytree(ROOT / 'evaluation/inquiry-p8', base)
            candidate_manifest = json.loads((base / 'MANIFEST.json').read_text())
            candidate_manifest['state'] = 'awaiting-researcher-approval'
            candidate_manifest['recipe_version'] = author.CORRECTED_RECIPE
            for case in candidate_manifest['cases']:
                oracle = json.loads((base / case['oracle_path']).read_text())
                case['authored_semantic_content_sha256'] = manifest.semantic_digest(oracle)
            candidate_manifest_bytes = manifest.json_bytes(candidate_manifest)
            candidate_protocol = json.loads((base / 'protocol.json').read_text())
            candidate_protocol['recipes']['version'] = author.CORRECTED_RECIPE
            candidate_protocol['freeze']['state'] = 'awaiting-researcher-approval'
            candidate_protocol['freeze']['manifest_sha256'] = manifest.digest(candidate_manifest_bytes)
            candidate_protocol['correction_approval'] = {'state': 'pending', 'path': 'test-only-approval.json', 'sha256': None}
            candidate_protocol_bytes = manifest.json_bytes(candidate_protocol)
            (base / 'candidate-protocol.json').write_bytes(candidate_protocol_bytes)
            (base / 'candidate-manifest.json').write_bytes(candidate_manifest_bytes)
            receipt = {'status': 'APPROVED', 'provenance': 'user', 'researcher': 'test-only',
                       'metadata_only_freeze_authorized': True, 'reviewed_candidate_commit': 'a' * 40,
                       'candidate_protocol_path': 'candidate-protocol.json',
                       'candidate_protocol_sha256': manifest.digest(candidate_protocol_bytes),
                       'candidate_manifest_path': 'candidate-manifest.json',
                       'candidate_manifest_sha256': manifest.digest(candidate_manifest_bytes)}
            receipt_bytes = manifest.json_bytes(receipt)
            (base / 'test-only-approval.json').write_bytes(receipt_bytes)
            frozen_manifest = copy.deepcopy(candidate_manifest); frozen_manifest['state'] = 'frozen'
            frozen_manifest_bytes = manifest.json_bytes(frozen_manifest)
            (base / 'MANIFEST.json').write_bytes(frozen_manifest_bytes)
            frozen_protocol = copy.deepcopy(candidate_protocol)
            frozen_protocol['freeze']['state'] = 'frozen'
            frozen_protocol['freeze']['manifest_sha256'] = manifest.digest(frozen_manifest_bytes)
            frozen_protocol['correction_approval'] = {'state': 'approved', 'path': 'test-only-approval.json',
                                                       'sha256': manifest.digest(receipt_bytes)}
            (base / 'protocol.json').write_bytes(manifest.json_bytes(frozen_protocol))
            _, _, loaded, _, inventory = manifest.load_suite(base / 'MANIFEST.json')
            self.assertEqual(loaded, frozen_manifest)
            self.assertIn('test-only-approval.json', inventory)
            self.assertIn('candidate-protocol.json', inventory)
            self.assertIn('candidate-manifest.json', inventory)
            for field, value in [('supporting_artifacts', []),
                                 ('input_commit_rule', 'changed-rule'),
                                 ('legacy_freeze_tag_created', True)]:
                with self.subTest(field=field):
                    altered = copy.deepcopy(frozen_protocol); altered['freeze'][field] = value
                    (base / 'protocol.json').write_bytes(manifest.json_bytes(altered))
                    with self.assertRaisesRegex(ValueError, 'approved candidate protocol changed'):
                        manifest.load_suite(base / 'MANIFEST.json')
            (base / 'protocol.json').write_bytes(manifest.json_bytes(frozen_protocol))
            for field, value in [('independent_review', {'path': 'other-review.json', 'sha256': '0' * 64}),
                                 ('quality_review', {'path': 'other-quality.json', 'sha256': '0' * 64})]:
                with self.subTest(manifest_field=field):
                    altered = copy.deepcopy(frozen_manifest); altered[field] = value
                    altered_bytes = manifest.json_bytes(altered)
                    (base / 'MANIFEST.json').write_bytes(altered_bytes)
                    protocol = copy.deepcopy(frozen_protocol)
                    protocol['freeze']['manifest_sha256'] = manifest.digest(altered_bytes)
                    (base / 'protocol.json').write_bytes(manifest.json_bytes(protocol))
                    with self.assertRaisesRegex(ValueError, 'approved candidate inputs'):
                        manifest.load_suite(base / 'MANIFEST.json')

    def test_original_input_pin_cannot_be_replaced(self):
        p = {'code_commit': 'unused', 'code_paths': {}, 'recipes': {'version': 'inquiry-p8-recipes@1'}}
        with patch.object(manifest, 'git', side_effect=lambda *args: b'old' if args[-1] == manifest.INPUT_COMMIT else b'new'):
            with self.assertRaisesRegex(ValueError, 'original suite input pin cannot change'):
                manifest.repository_preflight(p, ROOT / 'evaluation/inquiry-p8', {}, 'different')

    def test_corrected_pin_is_required(self):
        p = {'code_commit': 'unused', 'code_paths': {}, 'recipes': {'version': author.CORRECTED_RECIPE}}
        with self.assertRaisesRegex(ValueError, 'explicit --input-commit'):
            manifest.repository_preflight(p, CANDIDATE, {})

    def test_only_five_inputs_change_and_all_expected_results_stay_exact(self):
        old = json.loads((ROOT / 'evaluation/inquiry-p8/MANIFEST.json').read_text())
        new = json.loads((CANDIDATE / 'MANIFEST.json').read_text())
        self.assertEqual(len(new['cases']), 96)
        changed = []
        for a, b in zip(old['cases'], new['cases']):
            self.assertEqual(a['case_id'], b['case_id'])
            if a['input_sha256'] != b['input_sha256']:
                changed.append(b['case_id'])
            ao = json.loads((ROOT / 'evaluation/inquiry-p8' / a['oracle_path']).read_text())
            bo = json.loads((CANDIDATE / b['oracle_path']).read_text())
            self.assertEqual(ao['expected'], bo['expected'])
            review_hash = bo['review_provenance'].get('review_sha256')
            self.assertNotEqual(review_hash, old['independent_review']['sha256'])
            if review_hash is not None:
                self.assertEqual(review_hash, new['independent_review']['sha256'])
        self.assertEqual(changed, ['T07'] + [f'T07-source-declarations-{n}' for n in (0, 1, 4, 16)])


if __name__ == '__main__':
    unittest.main()
