#!/usr/bin/env python3
"""Decode candidate input bytes and authored expected ASTs with a real consumer.

This is authoring/setup validation. It starts no inquiry driver and derives no
oracle. It refuses to overwrite a receipt or accept changed manifest hashes.
"""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
from evidence_measured import canonical
from inquiry_evaluation_manifest import digest, read_json, require, safe_path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--suite', required=True, type=Path)
    parser.add_argument('--consumer', required=True, type=Path)
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    require(not args.out.exists(), 'authoring receipt already exists')
    base = args.suite.resolve()
    manifest = read_json(base / 'MANIFEST.json')
    consumer = args.consumer.resolve()
    results = []
    with tempfile.TemporaryDirectory(prefix='p8-corrected-consumer-') as temporary:
        expected = Path(temporary) / 'authored-expectation.stdout'
        for case in manifest['cases']:
            source = safe_path(base, case['input_path'])
            oracle_path = safe_path(base, case['oracle_path'])
            require(digest(source.read_bytes()) == case['input_sha256'], 'input hash changed')
            require(digest(oracle_path.read_bytes()) == case['oracle_sha256'], 'oracle hash changed')
            oracle = read_json(oracle_path)
            data = b''.join(canonical(form) for form in oracle['expected']['results'])
            expected.write_bytes(data)
            command = [str(consumer), 'consume', 'accepted', str(source), str(expected)]
            result = subprocess.run(command, capture_output=True, timeout=30)
            results.append({'case_id': case['case_id'], 'command': command, 'exit_code': result.returncode,
                            'stdout': result.stdout.decode(), 'stderr': result.stderr.decode(),
                            'input_sha256': case['input_sha256'], 'oracle_sha256': case['oracle_sha256'],
                            'encoded_authored_expected_ast_sha256': digest(data),
                            'expectation_origin': oracle['oracle_kind']})
            require(result.returncode == 0, 'consumer decode failed: ' + case['case_id'])
    receipt = {'scope': 'candidate authoring decode validation; outside measurement',
               'provenance': 'ai-executed', 'independent_review_status': 'PENDING',
               'inquiry_driver_invocations': 0, 'consumer_sha256': digest(consumer.read_bytes()),
               'consumer_build_command': ['cabal', 'exec', '--', 'ghc', '-package', 'lara',
                                          '-outputdir', '/tmp/p8-consumer-build', '-o', '/tmp/p8-consumer',
                                          'scripts/inquiry-codec-client.hs'],
               'consumer_build_executed': False, 'manifest_sha256': digest((base / 'MANIFEST.json').read_bytes()),
               'checks': 'parse and roundtrip original input bytes and encoded authored expected result ASTs; no source analysis',
               'results': results}
    with args.out.open('x') as output:
        output.write(json.dumps(receipt, indent=2) + '\n')
    print('decoded 96 candidate inputs and authored result ASTs; independent review remains pending')


if __name__ == '__main__':
    main()
