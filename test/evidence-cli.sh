#!/usr/bin/env bash
# Behavioral acceptance of the real certified-evidence CLI. Never rewrites originals.
set -euo pipefail
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
cabal build exe:lara
lara_bin="$(cabal list-bin exe:lara)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/lara-evidence-cli.XXXXXX")"
trap 'rm -rf "$tmp_root"' EXIT HUP INT TERM
python3 - "$repo_root" "$lara_bin" "$tmp_root" <<'PY'
import copy
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

REPO, LARA, TMP = (Path(arg).resolve() for arg in sys.argv[1:])
COUNT = 0
MANIFEST = 'lara-evidence.sexp'


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def passed(name):
    global COUNT
    COUNT += 1
    print(f'PASS {COUNT:02d}: {name}', flush=True)


def wire(value):
    """Independent exact Wire printer; CR/NUL are literal quoted payloads."""
    if isinstance(value, list):
        return '(' + ' '.join(map(wire, value)) + ')'
    require(isinstance(value, str), f'non-string Wire atom: {value!r}')
    if value and all(0x21 <= ord(c) <= 0x7e and c not in '();"\\' for c in value):
        return value
    return '"' + value.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n') + '"'


def canonical(value):
    return (wire(value) + '\n').encode('utf-8')


def parse(raw):
    text = raw.decode('utf-8') if isinstance(raw, bytes) else raw
    index = 0

    def skip():
        nonlocal index
        while index < len(text):
            if text[index] in ' \t\r\n':
                index += 1
            elif text[index] == ';':
                while index < len(text) and text[index] != '\n':
                    index += 1
            else:
                break

    def form():
        nonlocal index
        skip()
        require(index < len(text), 'unexpected end of S-expression')
        char = text[index]
        index += 1
        if char == '(':
            result = []
            while True:
                skip()
                require(index < len(text), 'unclosed S-expression list')
                if text[index] == ')':
                    index += 1
                    return result
                result.append(form())
        if char == '"':
            result = []
            while index < len(text):
                char = text[index]
                index += 1
                if char == '"':
                    return ''.join(result)
                if char == '\\':
                    require(index < len(text), 'unterminated Wire escape')
                    char = text[index]
                    index += 1
                    require(char in '"\\n', f'invalid Wire escape {char!r}')
                    char = '\n' if char == 'n' else char
                result.append(char)
            raise AssertionError('unclosed Wire quote')
        require(0x21 <= ord(char) <= 0x7e and char not in '();"\\', 'invalid bare atom')
        start = index - 1
        while index < len(text) and 0x21 <= ord(text[index]) <= 0x7e and text[index] not in '();"\\':
            index += 1
        return text[start:index]

    result = form()
    skip()
    require(index == len(text), 'trailing S-expression input')
    return result


def field(value, name):
    matches = [item[1:] for item in value if isinstance(item, list) and item and item[0] == name]
    require(len(matches) == 1, f'expected one {name!r} field, got {matches!r}')
    return matches[0]


def sha(raw):
    return 'sha256:' + hashlib.sha256(raw).hexdigest()


def clone(name, original='a'):
    source = REPO / 'examples/certified-evidence' / f'package-{original}'
    if original == 'quarantined':
        source = REPO / 'fixtures/evidence/quarantined'
    root = TMP / name
    shutil.copytree(source, root)
    return root


def manifest(root):
    return parse((root / MANIFEST).read_bytes())


def objects(value):
    return field(value, 'objects')


def append_object(value, item):
    sections = [section for section in value if isinstance(section, list) and section and section[0] == 'objects']
    require(len(sections) == 1, 'expected one mutable objects section')
    sections[0].append(item)


def meta(value, ident):
    matches = [item for item in objects(value) if item[1] == ident]
    require(len(matches) == 1, f'expected one object {ident}')
    return matches[0]


def save_manifest(root, value):
    (root / MANIFEST).write_bytes(canonical(value))


def repin(root, *ids):
    value = manifest(root)
    for item in objects(value):
        if item[1] in ids:
            raw = (root / item[2]).read_bytes()
            item[3:5] = [str(len(raw)), sha(raw)]
    save_manifest(root, value)


def global_path(root, name):
    value = manifest(root)
    return root / meta(value, field(value, name)[0])[2]


def replace_file(path, before, after, count=-1):
    raw = path.read_text(encoding='utf-8')
    require(before in raw, f'mutation target missing: {before!r} in {path}')
    path.write_text(raw.replace(before, after, count), encoding='utf-8')


def run(*args, executable=LARA, cwd=REPO):
    command = [str(executable), *map(str, args)]
    try:
        result = subprocess.run(command, cwd=cwd, capture_output=True, timeout=30)
    except subprocess.TimeoutExpired as error:
        raise AssertionError(f'CLI hung (including FIFO safety): {command!r}') from error
    result.context = (f'command={command!r}\nexit={result.returncode}\n'
                      f'stdout={result.stdout!r}\nstderr={result.stderr!r}')
    return result


def rejected(result, code=1, r8=False):
    require(result.returncode == code, result.context)
    require(result.stdout == b'', 'failure emitted accepted/partial stdout\n' + result.context)
    require(bool(result.stderr), 'failure omitted diagnostics\n' + result.context)
    if r8:
        require(b'R8' in result.stderr, 'missing evidence/admission class R8\n' + result.context)
    return result


def accepted(root, *options, checked=None, declared=None, assurance=None):
    result = run('check-ara', root, *options)
    require(result.returncode == 0, result.context)
    report = parse(result.stdout)
    require(report[:2] == ['lara-evidence-report', '1'], result.context)
    require(result.stdout == canonical(report), 'noncanonical report\n' + result.context)
    require(field(report, 'versions') == ['lara-syntax@0.11', 'lara-evidence@0.1'], 'wrong public versions')
    checked_ids, declared_ids = field(report, 'checked'), field(report, 'declared')
    require(len(set(checked_ids + declared_ids)) == len(checked_ids + declared_ids), 'partition duplicates/overlap')
    if checked is not None:
        require(checked_ids == checked, f'checked IDs: {checked_ids!r}, expected {checked!r}')
    if declared is not None:
        require(declared_ids == declared, f'declared IDs: {declared_ids!r}, expected {declared!r}')
    if assurance is not None:
        require(field(report, 'assurance') == [assurance], 'wrong evidence assurance')
    value = manifest(root)
    source = global_path(root, 'source').read_bytes()
    require(field(report, 'manifest') == [sha((root / MANIFEST).read_bytes())], 'manifest not raw SHA256')
    require(field(report, 'source') == [sha(source)], 'source not raw SHA256')
    policy_option = options.index('--policy') if '--policy' in options else None
    policy = Path(options[policy_option + 1]) if policy_option is not None else global_path(root, 'policy')
    origin = 'verifier' if policy_option is not None else 'package'
    require(field(report, 'policy') == [origin, sha(policy.read_bytes())], 'wrong raw policy hash/origin')
    leaves = re.findall(r'^leaf\s+(\S+)\s*:', source.decode('utf-8'), re.M)
    require(set(checked_ids + declared_ids) == set(leaves), 'partition omitted declared source leaf')
    # Requests come from captured source syntax, not from report defaults or checker names.
    requests = {}
    leaf = None
    for line in source.decode('utf-8').splitlines():
        match = re.match(r'^leaf\s+(\S+)\s*:', line)
        if match:
            leaf = match[1]
        match = re.match(r'\s*extract\s*=\s*(.*)', line)
        if match:
            requests[leaf] = parse(match[1])
    replays = field(report, 'replays')
    require([item[1] for item in replays] == checked_ids, 'replays differ from checked partition')
    dependencies = ['dependencies']
    requested_ids = []
    for replay in replays:
        require(replay[0] == 'leaf' and replay[2] == requests[replay[1]], 'normalized request mismatch')
        ident = requests[replay[1]][2]
        expected_meta = meta(value, ident)
        deps = field(replay, 'deps')
        require(deps == [expected_meta], f'runner deps not actual requested manifest object: {replay!r}')
        dependencies.append(['leaf', replay[1], ['objects', *deps]])
        requested_ids.append(ident)
    require(field(report, 'dependency-report-digest') == [sha(canonical(dependencies))], 'dependency digest independent recomputation differs')
    globals_ids = [field(value, key)[0] for key in ('paper', 'source', 'policy')]
    required = [item for item in objects(value) if item[1] in requested_ids and item[1] not in globals_ids]
    captured = [meta(value, ident) for ident in globals_ids] + required
    require(field(report, 'captured') == captured, 'captured union is not globals plus requested objects in manifest order')
    for item in captured:
        raw = (root / item[2]).read_bytes()
        require(item[3:] == [str(len(raw)), sha(raw)], f'captured metadata not actual raw bytes: {item!r}')
    envelope = [item for item in report if not (isinstance(item, list) and item and item[0] == 'evidence-digest')]
    require(field(report, 'evidence-digest') == [sha(canonical(envelope))], 'evidence identity independent recomputation differs')
    verdict = field(report, 'core-verdict')[0]
    require(verdict[0] == 'verdict' and verdict[2] == 'accept', 'report includes rejected core verdict')
    require(field(report, 'core-replay') == [verdict[1]], 'core replay tuple differs from verdict')
    return report, result


A_IDS = ['forward-1631', 'forward-1632']
B_IDS = ['train-0', 'train-1', 'train-2', 'loss-0', 'loss-1', 'loss-2', 'loss-3', 'loss-4']
originals = {}
for letter, ids in [('a', A_IDS), ('b', B_IDS)]:
    root = clone('original-' + letter, letter)
    report, result = accepted(root, checked=ids, declared=[], assurance='evidence-checked')
    originals[letter] = (root, report, result)
    passed(f'original {letter.upper()}: exact checked {len(ids)}, empty declared, raw hashes, normalized requests, runner deps, capture and independent digests')
    verifier = global_path(root, 'policy')
    override, _ = accepted(root, '--policy', str(verifier), checked=ids, declared=[], assurance='evidence-checked')
    for key in ('core-replay', 'core-verdict', 'replays', 'dependency-report-digest', 'captured'):
        require(field(override, key) == field(report, key), f'verifier policy changed {key}')
    require(field(override, 'evidence-digest') != field(report, 'evidence-digest'), 'policy origin omitted from evidence identity')
    require(field(override, 'policy')[1] == field(report, 'policy')[1], 'identical supplied policy bytes changed hash')
    passed(f'original {letter.upper()}: identical verifier policy changes evidence identity only')

root = clone('drop-allowlist')
policy = global_path(root, 'policy')
replace_file(policy, 'evidence-checkers = (checkers (csv-row 1))', 'evidence-checkers = (checkers)')
repin(root, 'policy')
rejected(run('check-ara', root), r8=True)
passed('dropping checker allowlist is R8, not checker-name acceptance')

root = clone('policy-before-bytes')
policy = global_path(root, 'policy')
with policy.open('a', encoding='utf-8') as handle:
    handle.write('\nadmission { (certified, checker(csv-row, 1)) = reject }\n')
repin(root, 'policy')
healthy = rejected(run('check-ara', root), r8=True)
(root / 'evidence/benchmarking.csv').write_bytes(b'broken requested bytes')
broken = rejected(run('check-ara', root), r8=True)
require(healthy.stderr == broken.stderr, 'bad evidence bytes masked earlier full-policy rejection')
passed('full policy rejects before integrity/capture of bad requested bytes')

root = clone('integrity-tamper')
with (root / 'evidence/benchmarking.csv').open('ab') as handle:
    handle.write(b'\n')
rejected(run('check-ara', root), r8=True)
passed('original dependency tamper without repin fails integrity')

root = clone('same-length-integrity-tamper')
path = root / 'evidence/benchmarking.csv'
raw = path.read_bytes()
path.write_bytes(bytes([raw[0] ^ 1]) + raw[1:])
rejected(run('check-ara', root), r8=True)
passed('same-length requested-byte mutation fails SHA256 integrity')

root = clone('unrequested-bytes-ignored')
value = manifest(root)
for item in objects(value):
    if item[1] not in {'paper', 'source', 'policy', 'benchmarking'}:
        path = root / item[2]
        path.unlink()
        path.symlink_to(root / 'nonexistent-unrequested-target')
ignored, _ = accepted(root, checked=A_IDS, declared=[], assurance='evidence-checked')
require(ignored == originals['a'][1], 'unrequested broken objects acquired byte assurance or changed receipt')
passed('unrequested licenses/origin bytes are not captured, opened, or given byte assurance')

root = clone('selected-csv-mismatch')
path = root / 'evidence/benchmarking.csv'
raw = path.read_bytes()
rows = list(csv.reader(io.StringIO(raw.decode('utf-8'), newline='')))
header = rows[0]
selected = [row for row in rows[1:] if row[header.index('')] == '1631']
require(len(selected) == 1, 'original CSV trial 1631 is not unique')
selected[0][header.index('time')] = '0.125'
output = io.StringIO(newline='')
csv.writer(output, lineterminator='\n').writerows(rows)
path.write_bytes(output.getvalue().encode('utf-8'))
repin(root, 'benchmarking')
rejected(run('check-ara', root), r8=True)
passed('repinned selected original CSV number fails proposition equality')

root = clone('selected-notebook-mismatch', 'b')
path = root / 'evidence/1_minimal_code_example.ipynb'
notebook = json.loads(path.read_bytes())
notebook['cells'][19]['outputs'][0]['text'][0] = '999\n'
path.write_bytes((json.dumps(notebook, ensure_ascii=False) + '\n').encode('utf-8'))
repin(root, 'notebook')
rejected(run('check-ara', root), r8=True)
passed('repinned original notebook wrong loss fails proposition equality')

root = clone('dependency-retarget')
value = manifest(root)
old_meta = meta(value, 'benchmarking')
new_meta = copy.deepcopy(old_meta)
new_meta[1:3] = ['benchmarking-copy', 'evidence/benchmarking-copy.csv']
append_object(value, new_meta)
shutil.copyfile(root / old_meta[2], root / new_meta[2])
save_manifest(root, value)
source = global_path(root, 'source')
replace_file(source, 'refs = [evidence/benchmarking.csv]', 'refs = [evidence/benchmarking.csv, evidence/benchmarking-copy.csv]', 1)
replace_file(source, '(csv-row 1 benchmarking ', '(csv-row 1 benchmarking-copy ', 1)
repin(root, 'source')
retarget, _ = accepted(root, checked=A_IDS, declared=[], assurance='evidence-checked')
baseline = originals['a'][1]
require(field(retarget, 'core-verdict') == field(baseline, 'core-verdict'), 'same selected proposition changed core verdict')
require(field(retarget, 'core-replay') == field(baseline, 'core-replay'), 'retarget changed core proposition identity')
for key in ('dependency-report-digest', 'evidence-digest'):
    require(field(retarget, key) != field(baseline, key), f'retarget omitted from {key}')
require([item[1] for item in field(retarget, 'captured')[3:]] == ['benchmarking', 'benchmarking-copy'], 'retarget did not capture union of two dependencies')
passed('same-byte first-request retarget preserves core, changes dependency/evidence identities, captures union two')

root = clone('unused-broken-cert')
source = global_path(root, 'source')
with source.open('a', encoding='utf-8') as handle:
    handle.write('\nleaf unused-broken : forward_time_s(1631,"ProgressiveNet",10,0.125)\n'
                 '  kind = certified\n  provenance = checker(csv-row, 1)\n'
                 '  refs = [evidence/benchmarking.csv]\n'
                 '  extract = (csv-row 1 benchmarking (key "" "1631") (select ("" decimal) (method text) ("num prevs" decimal) (time decimal)) (predicate forward_time_s))\n')
repin(root, 'source')
rejected(run('check-ara', root), r8=True)
passed('unused certified declaration must replay and mismatched proposition rejects')
for command in ('check', 'deps'):
    rejected(run(command, source), r8=True)
    passed(f'{command}: unused certified declaration has no accepted source envelope without context')

root = clone('quarantined-ok', 'quarantined')
accepted(root, checked=['drop'], declared=['keep'], assurance='mixed')
passed('committed synthetic quarantine fixture accepts with checked drop and declared keep')
# Blocked is an anti-promotion overlay, not a blanket quarantine marker.
# Build a synthetic removed undercutter of a retained complete support.
replace_file(global_path(root, 'source'), '\n  open cq', '')
replace_file(global_path(root, 'source'),
             'arg arg-pruned : supports(claim-main) by pass from [drop]',
             'arg arg-pruned : supports(claim-undercut) by prune-attack from [drop]')
replace_file(global_path(root, 'policy'), '  question cq : score(X) (optional)\n', '')
with global_path(root, 'policy').open('a', encoding='utf-8') as handle:
    handle.write('\nrule prune-attack(X)\n  mode = defeasible\n'
                 '  premises = [ evidence(X) ]\n  conclusion = verdict(1)\n')
with global_path(root, 'source').open('a', encoding='utf-8') as handle:
    handle.write('\nclaim claim-undercut\n  nl = "Synthetic undercut witness"\n'
                 '  formal = verdict(1)\n'
                 '  binding = { author = author, rationale = "synthetic fixture", audit-status = reviewed }\n'
                 '\nundercut arg-pruned arg-open.rule\nstatus claim-main\n')
repin(root, field(manifest(root), 'source')[0], field(manifest(root), 'policy')[0])
report, _ = accepted(root, checked=['drop'], declared=['keep'], assurance='mixed')
verdict = field(report, 'core-verdict')[0]
statuses = field(verdict, 'statuses')
blocked = [item for item in statuses if item[-1] == 'evidence-blocked']
require(bool(blocked), 'quarantined accepted source falsely published an unblocked status')
conditional = field(verdict, 'conditional')
require([item[1] for item in blocked] == [item[1] for item in conditional], 'blocked status lacks matching conditional core diagnostic')
passed('synthetic quarantined fixture: checked drop, declared keep, mixed assurance, truthful blocked core')
for command in ('check', 'deps'):
    rejected(run(command, global_path(root, 'source')), r8=True)
    passed(f'{command}: quarantined certification still refused without context')
root = clone('quarantined-mismatch', 'quarantined')
replace_file(root / 'evidence/measurements.csv', 'drop,7', 'drop,8')
repin(root, 'measurements')
rejected(run('check-ara', root), r8=True)
passed('quarantine cannot hide a certified proposition mismatch')

for kind in ('missing', 'symlink-final', 'symlink-intermediate', 'fifo', 'directory', 'lfs', 'invalid-utf8'):
    root = clone('requested-' + kind)
    path = root / 'evidence/benchmarking.csv'
    if kind == 'missing':
        path.unlink()
    elif kind == 'symlink-final':
        other = root / 'same-bytes.csv'
        path.rename(other)
        path.symlink_to(other)
    elif kind == 'symlink-intermediate':
        evidence = root / 'evidence'
        target = root / 'real-evidence'
        evidence.rename(target)
        evidence.symlink_to(target, target_is_directory=True)
    elif kind == 'fifo':
        path.unlink()
        os.mkfifo(path)
    elif kind == 'directory':
        path.unlink()
        path.mkdir()
    elif kind == 'lfs':
        path.write_bytes(b'version https://git-lfs.github.com/spec/v1\noid sha256:' + b'0' * 64 + b'\nsize 298568\n')
        repin(root, 'benchmarking')
    else:
        path.write_bytes(b'id,value\none,\xff\n')
        repin(root, 'benchmarking')
    rejected(run('check-ara', root), r8=True)
    passed(f'requested object {kind}: rejects evidence with empty stdout, no hang')

for kind in ('noncanonical', 'duplicate-id', 'duplicate-path', 'parent-path', 'absolute-path', 'nul-path', 'nul-parent-component'):
    root = clone('manifest-' + kind)
    value = manifest(root)
    if kind == 'noncanonical':
        (root / MANIFEST).write_bytes(canonical(value) + b'\n')
    else:
        item = meta(value, 'benchmarking')
        if kind == 'duplicate-id':
            extra = copy.deepcopy(item)
            extra[2] = 'evidence/another.csv'
            append_object(value, extra)
        elif kind == 'duplicate-path':
            extra = copy.deepcopy(item)
            extra[1] = 'another-id'
            append_object(value, extra)
        else:
            item[2] = {'parent-path': '../benchmarking.csv', 'absolute-path': '/tmp/benchmarking.csv',
                       'nul-path': 'evidence/benchmarking.csv\0suffix',
                       'nul-parent-component': '..\0suffix/benchmarking.csv'}[kind]
        save_manifest(root, value)
    rejected(run('check-ara', root), 2)
    passed(f'manifest {kind}: invalid package exits 2 with empty stdout')

for name in ('paper', 'source', 'policy'):
    for kind in ('hash', 'length'):
        root = clone('global-' + name + '-' + kind)
        value = manifest(root)
        item = meta(value, field(value, name)[0])
        if kind == 'hash':
            item[4] = 'sha256:' + '0' * 64
        else:
            item[3] = str(int(item[3]) + 1)
        save_manifest(root, value)
        rejected(run('check-ara', root), 2)
        passed(f'global {name} wrong {kind}: invalid package exits 2')

root = clone('source-structural')
global_path(root, 'source').write_bytes(b'this is not a Lara source\n')
repin(root, 'source')
rejected(run('check-ara', root), 2)
passed('repinned structurally invalid source is exit 2, not evidence rejection')

root, baseline, baseline_run = originals['a']
destination = TMP / 'published'
report, publication = accepted(root, '--out', str(destination), checked=A_IDS, declared=[], assurance='evidence-checked')
require(publication.stdout == baseline_run.stdout, 'publication changed stdout report')
require(sorted(item.name for item in destination.iterdir()) == ['core-verdict.sexp', 'report.sexp'], 'publication included unexpected files')
require((destination / 'report.sexp').read_bytes() == publication.stdout, 'published report differs from stdout')
require((destination / 'core-verdict.sexp').read_bytes() == canonical(field(report, 'core-verdict')[0]), 'published core verdict differs from accepted report')
passed('publication writes only accepted report/core verdict and identical report stdout')
(destination / 'sentinel').write_bytes(b'leave destination untouched\0\r\n')
before = {item.name: (item.stat().st_ino, item.read_bytes()) for item in destination.iterdir()}
rejected(run('check-ara', root, '--out', destination), 2)
after = {item.name: (item.stat().st_ino, item.read_bytes()) for item in destination.iterdir()}
require(before == after, 'existing publication destination modified')
require(not list(TMP.glob('.published.evidence-*')), 'failed publication leaked temporary sibling')
passed('existing output rejects exit 2 with empty stdout and destination unchanged')
failed_output = TMP / 'failed-output'
rejected(run('check-ara', TMP / 'integrity-tamper', '--out', failed_output), r8=True)
require(not failed_output.exists(), 'failed evidence check created output bundle')
require(not list(TMP.glob('.failed-output.evidence-*')), 'failed check leaked publication candidate')
passed('failed certification creates no output bundle')

root = clone('receipt-not-authority')
receipt = TMP / 'receipt'
accepted(root, '--out', str(receipt), checked=A_IDS, declared=[], assurance='evidence-checked')
receipt_bytes = (receipt / 'report.sexp').read_bytes()
# Even a prior accepted receipt present inside the input package is not a cache.
(root / 'report.sexp').write_bytes(receipt_bytes)
(root / 'core-verdict.sexp').write_bytes((receipt / 'core-verdict.sexp').read_bytes())
(root / 'evidence/benchmarking.csv').write_bytes(b'mutated after accepted receipt')
rejected(run('check-ara', root), r8=True)
require((receipt / 'report.sexp').read_bytes() == receipt_bytes, 'recheck mutated persisted receipt')
passed('persisted accepted receipt is never authoritative: current input is replayed after mutation')

for letter in ('a', 'b'):
    root = originals[letter][0]
    source = global_path(root, 'source')
    for command in ('check', 'deps'):
        rejected(run(command, source), r8=True)
        passed(f'original {letter.upper()} legacy {command}: no evidence context, exit 1, empty stdout')
    policy = global_path(root, 'policy')
    policy_id = re.search(r'^policy\s+(\S+)', policy.read_text(encoding='utf-8'), re.M).group(1)
    mapping = root / 'minimal.laramap'
    mapping.write_bytes(canonical(['lara-map@1', ['policy', policy_id, policy.name], ['backends'],
                                  ['members', ['member', 'original', source.name]], ['alignments'], ['questions']]))
    for command in ('check', 'map-input'):
        result = rejected(run(command, mapping), r8=True)
        require(b'original' in result.stderr and b'map' in result.stderr.lower(), 'missing composite member admission attribution\n' + result.context)
        passed(f'original {letter.upper()} {command} map adapter: member admission rejection, no accepted envelope')
    world = root / 'world.sexp'
    world.write_bytes(canonical(['pw-run', '1', ['worlds', ['world', 'original', 'context', ['lara', source.name]]],
                                ['edges'], ['comparisons'], ['pw-surface', '1', ['bridges'], ['queries']]]))
    for command in ('pw', 'pw-input'):
        result = run(command, world)
        require(result.returncode == 1, result.context)
        require(result.stderr == b'', 'PW rejection violated existing stdout-only envelope\n' + result.context)
        error = parse(result.stdout)
        require(error[:3] == ['pw-error', '1', 'world'], 'PW failed outside world loading\n' + result.context)
        require(any(isinstance(item, list) and item[:2] == ['world-input', 'original'] for item in error[3:]), 'PW lacks existing world-input rejection envelope\n' + result.context)
        passed(f'original {letter.upper()} {command}: existing world-input rejection envelope, no acceptance')

legacy_parent = TMP / 'legacy'
legacy_parent.mkdir()
legacy = legacy_parent / 'walking-skeleton'
shutil.copytree(REPO / 'bundles/walking-skeleton', legacy)
with (legacy / 'emitted.lara').open('a', encoding='utf-8') as handle:
    handle.write('\nleaf unused-cert : randomized(exp_ow)\n  kind = certified\n'
                 '  provenance = checker(csv-row, 1)\n  refs = []\n')
# The helper must reach its real source-check door, not manifest/hash setup refusal.
result = run(legacy, LARA, executable=REPO / 'scripts/replay.sh')
require(result.returncode == 1, result.context)
require(b'R8' in result.stderr, 'legacy helper never reached source-without-context refusal\n' + result.context)
require(result.stdout == b'', 'legacy helper published a successful replay\n' + result.context)
passed('legacy replay helper reaches and refuses unused source certification without context')

print(f'evidence CLI acceptance: {COUNT} scenarios passed', flush=True)
PY
