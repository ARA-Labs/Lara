#!/usr/bin/env python3
"""Exercise the concrete PW boundary against the compiled Lean example host.

The fixture's q→q map gives justified; q→p gives gap while the modal query
still asks about target q. That distinction catches accidental operand
translation and a resolver that ignores the file's declaration maps.
"""
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXE = ROOT / 'lean/.lake/build/bin/pw-example'
FIXTURE = ROOT / 'fixtures/pw/declared.sexp'
passed = 0


def mutate(text, old, new, count=-1):
    """Replace old with new, failing if old is absent. Without this, a fixture
    edit could make a case silently rerun the unmodified input."""
    assert old in text, old
    changed = text.replace(old, new, count)
    assert changed != text, old
    return changed


def run_command(args, code, fragment):
    global passed
    result = subprocess.run([str(EXE), *args], capture_output=True, text=True, timeout=30)
    assert result.returncode == code, (result.returncode, result.stdout, result.stderr)
    assert fragment in result.stdout, (fragment, result.stdout, result.stderr)
    assert result.stderr == '', result.stderr
    passed += 1
    return result.stdout


def run_case(text, code, fragment):
    with tempfile.TemporaryDirectory(prefix='lara-pw-') as tmp:
        source = pathlib.Path(tmp) / 'input.sexp'
        source.write_text(text)
        return run_command([str(source)], code, fragment)


def main():
    text = FIXTURE.read_text()
    output = run_case(text, 0, '(queries true true true)')
    assert output == ('(pw-example-result 1 (queries true true true) '
                      '(comparisons (comparison b (atom q) (comparable justified))))\n'), output
    run_case(mutate(text, '(status justified (atom q))',
                    '(status defeated (atom q))', 1), 0,
             '(queries false true true)')
    changed = run_case(mutate(text, '(pred q q)', '(pred q p)'), 0,
                       '(comparison b (atom q) (comparable gap))')
    assert '(queries true true true)' in changed, changed
    run_case(mutate(text, '(pred q q)', ''), 0, 'bridge-vocabulary')
    run_case(mutate(text, '(pred q q)', '(pred q missing)'), 0, 'target-query')
    run_case(mutate(text, '(pred q q)', '(pred q q) (pred q p)'), 0,
             '(comparable justified)')
    run_case(mutate(text, '(bridge b src tgt', '(bridge b nowhere tgt'), 1,
             'unknown-source')
    run_case(mutate(text, '(bridge b src tgt', '(bridge b src nowhere'), 1,
             'unknown-target')
    run_case(mutate(text, '(dia b ', '(dia missing '), 1, 'unknown-bridge')
    run_case(mutate(text, '(pose src', '(pose nowhere'), 1, 'unknown-context')
    run_case(mutate(text, '(pose src', '(pose tgt'), 1, 'bridge-source-mismatch')
    run_case(mutate(text, '(atom q)', '(atom q (con z))'), 1, 'not-a-query')
    run_case(mutate(text, 'rule-ok ', ''), 1, 'missing-clause')
    run_case(mutate(text, '(bridges', '(bridges (bridge b src tgt (symbols) '
                    '(leaves) (clauses leaf-ok rule-ok cert-ok))'), 1,
             'duplicate-bridge')
    run_case(mutate(text, 'pw-surface 1', 'pw-surface 99'), 1, 'unsupported-version')
    # A later version is recognized even when its section layout differs.
    run_case('(pw-surface 2 (bridges) (queries) (worlds))', 1, 'unsupported-version')
    run_case(mutate(text, 'status justified', 'status unsupported'), 1, 'status')
    run_case(text + '\n(extra)', 1, 'syntax')
    run_case('', 1, 'syntax')
    run_case('(pw-surface 1 (bridges) (queries))', 0, '(queries) (comparisons)')
    # Text boundary: comments, whitespace and quoted Unicode names survive.
    quoted = mutate(mutate(mutate(text, 'bridge b ', 'bridge "β bridge" '),
                           'dia b ', 'dia "β bridge" '), 'box b ', 'box "β bridge" ')
    run_case(quoted, 0, '(comparison "β bridge" (atom q) (comparable justified))')
    multi = '(pw-surface 1 (bridges ' + \
        '(bridge b src tgt (symbols (pred q q)) (leaves) ' + \
        '(clauses leaf-ok rule-ok cert-ok)) ' + \
        '(bridge back tgt src (symbols (pred q q)) (leaves) ' + \
        '(clauses leaf-ok rule-ok cert-ok))) ' + \
        '(queries (pose src (box b (dia back (status justified (atom p)))))))'
    run_case(multi, 0, '(queries true) (comparisons ' +
             '(comparison b (atom q) (comparable justified)) ' +
             '(comparison back (atom q) (comparable gap)))')
    run_command([], 1, '(pw-example-error 1 usage ')
    with tempfile.TemporaryDirectory(prefix='lara-pw-missing-') as tmp:
        run_command([str(pathlib.Path(tmp) / 'missing.sexp')], 1,
                    '(pw-example-error 1 io ')
    print(f'PW file-driven gate passed ({passed} cases).')


if __name__ == '__main__':
    main()
