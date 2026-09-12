#!/usr/bin/env python3
"""Haskell/Lean differential gate for the possible-world outer runtime (#322).

`lara pw` (Haskell, src/Lara/PW/Run.hs) and `pw-run` (Lean,
lean/Lara/PW/RunMain.lean) implement the `pw-run 1` contract independently:
each reads the run file, reads and checks every world with its own local
checker, loads the bridge registry, resolves edges, elaborates and evaluates
the modal queries, and compares the source claims. Neither reads the other's
output. The Lean definitions carry the proofs (`Model.evaluates_iff`,
`Model.compare_mem_iff_sat`); this gate is the evidence that the Haskell
runtime computes the same thing.

Three families:

1. Committed fixtures (fixtures/pw/run/*.sexp). Each fixture's stdout must
   equal its committed `*.expected` golden byte for byte, from both drivers,
   with exit 0. `--update` rewrites the goldens from the Haskell driver, and
   only after the Lean driver has produced the same bytes. Each fixture is
   also derived with `lara pw-input`, and the derived document — every world
   source inline — must run to the same golden on both drivers.
2. Mutations of those fixtures: every error stage and fault; stage order, and
   fault order within each stage; every field of a context's environment; the
   rule clause under a renaming symbol map; duplicate-report groups that agree
   and that conflict, under both conflict modes (#326); map and acceptance
   dependence; and the text boundary (quoted Unicode names, non-ASCII file
   paths and run directories, files that are not UTF-8). For each case both
   drivers must agree on the exit code and on stdout, and stdout must contain
   the fragment the case names; some cases also pin stdout, or its queries
   section, to a committed golden. Agreement is byte equality except for the
   three faults whose last atom is runtime-specific text (a reader's syntax
   message, a world's read or decode failure, and an unreadable run file):
   there that one atom is masked, and every other atom, including the arity,
   must agree. A case may set `exact` to demand byte equality even so. The two
   nesting-depth cases do, because the shared reader's bound, message and
   column are contract rather than runtime-specific text (#331), and the gate
   additionally checks that both readers declare the same bound in source.
3. `.lara` world sources (fixtures/pw/source/*.sexp, #327). Only `lara pw`
   can elaborate a `(lara PATH)` world, so this family runs `lara pw` on the
   run file, then runs `lara pw-input` and hands the derived document to both
   drivers: their bytes must equal `lara pw`'s on the original. The committed
   fixture also pins that output to a golden and requires the Lean `pw-run` to
   refuse the original file as `world-input` — that half is the committed
   fixture's alone (`check_source_fixtures`), because it is what says the Lean
   reference has no surface parser; the generated cases never run Lean on the
   original, only on the derived document. They cover every way a `.lara` world
   stops before an envelope exists (unreadable, not UTF-8, unparsable, no
   policy, elaboration failure, admission stop, policy quarantine), a
   conflicting group reached through elaboration, mixed inline and `.lara`
   worlds, and non-ASCII program paths and text. When `lara pw` refuses a
   world's source, `lara pw-input` must print the same envelope.

The Unicode-name and non-ASCII path cases run again under `LC_ALL=C` and under
an ISO-8859-1 locale, because both drivers must use UTF-8 for output, for the
run-file argument and for file paths whatever the locale. The ISO-8859-1
locale is built with glibc's `localedef` into a private `LOCPATH`, so no root
is needed. On Linux a locale that cannot be built fails the gate; elsewhere
those reruns are reported as skipped.

Both drivers must leave stderr empty. The run fails when either family is
empty, so a moved fixture directory cannot pass as agreement.

Usage: python3 scripts/check-pw-conformance.py [--update] [--no-build]
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/pw/run'
SOURCES = ROOT / 'fixtures/pw/source'
LEAN = ROOT / 'lean/.lake/build/bin/pw-run'
C_LOCALE = {'LC_ALL': 'C', 'LANG': 'C'}
# An 8-bit locale: every argv byte decodes to some character, so a runtime that
# decodes the run-file argument with the locale looks up the wrong bytes.
LATIN1_LOCALES = pathlib.Path(tempfile.gettempdir()) / 'lara-pw-conf-locales'
LATIN1 = {'LC_ALL': 'en_US.ISO-8859-1', 'LANG': 'en_US.ISO-8859-1', 'LOCPATH': str(LATIN1_LOCALES)}
# The shared reader's nesting bound (#331). Declared here because the cases
# build their input from it; `check_depth_bound` is what keeps this copy honest.
MAX_DEPTH = 10000
DEPTH_BOUND_SOURCES = (
    (pathlib.Path('src/Lara/Wire.hs'), r'^maxDepth = ([0-9]+)$'),
    (pathlib.Path('lean/Lara/Driver.lean'), r'^def maxDepth : Nat := ([0-9]+)$'),
    # The spec states the value in prose, where nothing else would notice it
    # drifting; §10.1's paragraph is normative, so it gets a keeper too.
    (pathlib.Path('docs/spec.md'), r'`maxDepth = ([0-9]+)`'),
)


def check_depth_bound():
    """Both readers must declare the same nesting bound as the cases assume.

    Not because the depth cases below are blind to a one-sided change — they
    compare the full envelope with exact=True, and the bound's value is printed
    inside its own message, so raising either side alone goes red there. This
    check earns its place for two other reasons: it fails first and by name
    rather than as an envelope mismatch, and MAX_DEPTH above is a third copy of
    the constant with no other keeper — the case generators read it, so nothing
    else would notice it drifting from the two readers."""
    for path, pattern in DEPTH_BOUND_SOURCES:
        text = (ROOT / path).read_text(encoding='utf-8')
        found = re.search(pattern, text, re.MULTILINE)
        if found is None:
            print(f'FAIL: no nesting bound matching {pattern!r} in {path}')
            sys.exit(2)
        if int(found.group(1)) != MAX_DEPTH:
            print(f'FAIL: {path} declares a nesting bound of {found.group(1)}, '
                  f'not {MAX_DEPTH}; update this gate and its sibling reader')
            sys.exit(2)


def read_sexpr(text):
    """Read one printed S-expression into nested lists of atom strings."""
    pos = 0

    def skip():
        nonlocal pos
        while pos < len(text) and text[pos] in ' \t\r\n':
            pos += 1

    def form():
        nonlocal pos
        skip()
        if text[pos] == '(':
            pos += 1
            items = []
            skip()
            while text[pos] != ')':
                items.append(form())
                skip()
            pos += 1
            return items
        if text[pos] == '"':
            pos += 1
            chars = []
            while text[pos] != '"':
                if text[pos] == '\\':
                    pos += 1
                    chars.append({'n': '\n'}.get(text[pos], text[pos]))
                else:
                    chars.append(text[pos])
                pos += 1
            pos += 1
            return chars and ''.join(chars) or ''
        start = pos
        while pos < len(text) and text[pos] not in ' \t\r\n()"':
            pos += 1
        return text[start:pos]

    value = form()
    skip()
    assert pos == len(text), ('trailing output', text)
    return value


def mask(tree):
    """Replace the runtime-specific final atom of the three detail-bearing
    faults. Each fault's arity is checked first, so a missing or extra atom
    still fails instead of being truncated away.

    A case that sets `exact` skips this and compares the bytes."""
    if not (isinstance(tree, list) and tree[:2] == ['pw-error', '1']):
        return tree
    stage = tree[2]
    if stage == 'wire' and tree[3] == 'syntax':
        assert len(tree) == 5, ('syntax arity', tree)
        return tree[:4] + ['<detail>']
    if stage == 'io':
        assert len(tree) == 4, ('io arity', tree)
        return tree[:3] + ['<detail>']
    if stage == 'world' and tree[3][0] == 'world-input':
        assert len(tree) == 4 and len(tree[3]) == 3, ('world-input arity', tree)
        return tree[:3] + [tree[3][:2] + ['<detail>']]
    return tree


def run(exe, path, env=None):
    result = subprocess.run([*exe, str(path)], capture_output=True, timeout=120,
                            env=None if env is None else {**os.environ, **env})
    result.stdout = result.stdout.decode('utf-8')
    result.stderr = result.stderr.decode('utf-8', errors='replace')
    assert result.stderr == '', (exe, path, result.stderr)
    assert result.stdout.endswith('\n') and result.stdout.count('\n') == 1, result.stdout
    return result.returncode, result.stdout


def mutate(text, old, new, nth=None):
    """Replace old with new, failing if old is absent, so a fixture edit
    cannot silently turn a case into a rerun of the unmodified input. With
    nth, replace only that (1-based) occurrence."""
    assert old in text, old
    if nth is None:
        return text.replace(old, new)
    index = -1
    for _ in range(nth):
        index = text.index(old, index + 1)
    return text[:index] + new + text[index + len(old):]


class Copy(str):
    """An extra file's content, copied from this fixture-relative path."""


# Option keys a case may set; every other key names an extra file to write,
# relative to the run file's directory (str text, bytes, or a Copy).
#   append           text appended to the mutated run file
#   source           the run file's path, relative to a fresh temporary
#                    directory (default input.sexp); the committed worlds are
#                    copied next to it
#   missing          do not write the run file, so both drivers fail to read it
#   golden           stdout must equal this fixture's committed golden
#   same-queries-as  stdout's queries section must equal this fixture's golden
#   also-under       environments to run the case under again
#   exact            compare stdout byte for byte, masking no fault detail
OPTIONS = ('append', 'source', 'missing', 'golden', 'same-queries-as', 'also-under', 'exact')
TEXT_BOUNDARY = [C_LOCALE, LATIN1]

# (name, base fixture or None, substitutions, options, exit, fragment).
# A substitution is (old, new) or (old, new, nth). A base of None means the
# first substitution's `new` is the whole input (text or bytes). `fragment` is
# one string stdout must contain, or a tuple of strings all of which it must.
CASES = [
    # Wire: the run codec and the embedded pw-surface codec.
    ('syntax: trailing form', 'fields', [], {'append': '\n(extra)'}, 2, '(pw-error 1 wire syntax '),
    ('syntax: empty input', None, [(None, '')], {}, 2, '(pw-error 1 wire syntax '),
    # The shared reader's nesting bound: one form deeper than it allows is a
    # located `syntax` refusal from BOTH readers, at the same column and with
    # the same message, so the detail is compared rather than masked. Before
    # #331 only Haskell bounded the nesting: Lean read the over-deep form and
    # refused it one layer later as `malformed run`, the same exit code under a
    # different category.
    ('syntax: nesting depth exceeded', None, [(None, '(' * (MAX_DEPTH + 2))], {'exact': True}, 2,
     '(pw-error 1 wire syntax "line 1, column ' + str(MAX_DEPTH + 2)
     + ': maximum S-expression nesting depth exceeded (' + str(MAX_DEPTH) + ')")'),
    # And the other side of the boundary: the deepest form the bound admits
    # reads cleanly and is refused by the run codec, not the reader. Without
    # this case a reader that refused one level too early would pass the case
    # above.
    ('nesting depth at the bound', None,
     [(None, '(' * (MAX_DEPTH + 1) + ')' * (MAX_DEPTH + 1))], {'exact': True}, 2,
     '(pw-error 1 wire malformed run)'),
    ('unsupported run version', None, [(None, '(pw-run 2 (worlds))')], {}, 2, '(pw-error 1 wire unsupported-version 2)'),
    ('version 01 is not 1', None, [(None, '(pw-run 01 (worlds) (edges) (comparisons) (pw-surface 1 (bridges) (queries)))')], {}, 2, 'unsupported-version 01'),
    ('unsupported surface version', 'fields', [('pw-surface 1', 'pw-surface 7')], {}, 2, '(pw-error 1 wire unsupported-version 7)'),
    ('malformed acceptance', 'fields', [('(edge b s0 t0 accepted)', '(edge b s0 t0 maybe)')], {}, 2, '(pw-error 1 wire malformed acceptance)'),
    ('malformed world source', 'fields', [('(file "worlds/src-s0.sexp")', '(path "worlds/src-s0.sexp")')], {}, 2, 'malformed world-source'),
    ('missing section', None, [(None, '(pw-run 1 (worlds) (edges) (pw-surface 1 (bridges) (queries)))')], {}, 2, 'malformed run'),
    ('sections out of order', None, [(None, '(pw-run 1 (edges) (worlds) (comparisons) (pw-surface 1 (bridges) (queries)))')], {}, 2, 'malformed worlds'),
    ('malformed embedded status', 'fields', [('status gap', 'status maybe')], {}, 2, 'malformed status'),
    ('malformed comparison claim', 'fields', [('(compare b s0 (atom q))', '(compare b s0 (atomx q))')], {}, 2, 'malformed atom'),
    ('malformed edge arity', 'fields', [('(edge b s0 t0 accepted)', '(edge b s0 accepted)')], {}, 2, 'malformed edge'),
    # Worlds: reading, decoding, preflight, checking, and context identity.
    ('duplicate world', 'fields', [('(world s1 src', '(world s0 src')], {}, 1, '(pw-error 1 world (duplicate-world s0))'),
    ('missing world file', 'fields', [('worlds/src-s2.sexp', 'worlds/missing.sexp')], {}, 1, '(world-input s2 '),
    ('world file syntax', 'fields', [('worlds/src-s2.sexp', 'worlds/broken.sexp')], {'worlds/broken.sexp': '(check-input'}, 1, '(world-input s2 '),
    ('world not check-input', 'inline', [('(check-input', '(check-inputs', 1)], {}, 1, '(world-input w0 '),
    # Duplicate-report groups (#326): a group whose members disagree is refused
    # and named, whatever the conflict mode; a group whose members agree is
    # inert, so the run answers exactly as without it. l1 and l3 both report
    # p; l2 reports q. l3 is added to both worlds, since a context's leaf
    # table is part of its environment.
    ('world with a conflicting group', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l2)))', 1)], {}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    ('world with a conflicting group under reject mode', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups reject (group g1 (l1 l2)))', 1)], {}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    ('world with a consistent group', 'inline', [('(leaf l2 (atom q)))', '(leaf l2 (atom q)) (leaf l3 (atom p)))'), ('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l3)))', 1)], {'golden': 'inline'}, 0, '(pw-result 1 '),
    ('world with a consistent group under reject mode', 'inline', [('(leaf l2 (atom q)))', '(leaf l2 (atom q)) (leaf l3 (atom p)))'), ('(queries (atom p))', '(queries (atom p)) (groups reject (group g1 (l1 l3)))', 2)], {'golden': 'inline'}, 0, '(pw-result 1 '),
    ('first conflicting group is named', 'inline', [('(leaf l2 (atom q)))', '(leaf l2 (atom q)) (leaf l3 (atom p)))'), ('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g0 (l1 l3)) (group g1 (l1 l2)) (group g2 (l2 l3)))', 1)], {}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    # A group naming an undeclared leaf is malformed (R14) at decoding, before
    # any group is compared.
    ('group with an undeclared member', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l9)))', 1)], {}, 1, '(world-input w0 '),
    ('replay preflight', 'inline', [('(backends (backend nd 1))', '(backends (backend zz 1))', 1)], {}, 1, '(pw-error 1 world (world-rejected w0 R13))'),
    ('checker rejection', 'inline', [('(attacks (undermine a2 a1 (pos)))', '(attacks)')], {}, 1, '(pw-error 1 world (world-rejected w1 missing-conflict))'),
    ('undeclared leaf', 'inline', [('(arg a2 (leaf l2))', '(arg a2 (leaf l9))')], {}, 1, '(pw-error 1 world (world-rejected w1 '),
    ('duplicate world state', 'inline', [('(args (arg a1 (leaf l1)) (arg a2 (leaf l2)))', '(args (arg a1 (leaf l1)))'), ('(attacks (undermine a2 a1 (pos)))', '(attacks)')], {}, 1, '(pw-error 1 world (duplicate-world-state w1 w0))'),
    # The context environment: every field a later world must repeat. Each
    # case changes the second world only.
    ('context environment: signature', 'inline', [('(preds (pred p (args)) (pred q (args)))', '(preds (pred p (args)) (pred q (args)) (pred r (args)))', 2)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    ('context environment: rules', 'inline', [('(policy (rules)', '(policy (rules (rule r9 (mode defeasible) (params) (premises (apat p)) (conclusion (apat q)) (questions) (allow-trusted false) (certifiers)))', 2)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    # Without its contrary, w1's undermine would also fail the checker
    # (missing-conflict); the environment check comes first.
    ('context environment: contraries', 'inline', [('(contraries (contrary (apat q) (apat p)))', '(contraries)', 2)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    ('context environment: exceptions', 'inline', [('(exceptions)', '(exceptions (exception r9 (apat q)))', 2)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    ('context environment: leaves', 'inline', [('(leaves (leaf l1 (atom p)) (leaf l2 (atom q)))', '(leaves (leaf l1 (atom p)) (leaf l2 (atom q)) (leaf l3 (atom p)))', 2)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    # The replay id lists the theory too, so preflight passes and the
    # environment check is what refuses the world.
    ('context environment: theories', 'inline', [('(theories)', '(theories t9)', 3), ('(theories)', '(theories (theory t9 (atom q)))', 3)], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    # Bridges: the checked registry.
    ('duplicate bridge', 'fields', [('(bridges', '(bridges (bridge b tgt src (symbols) (leaves) (clauses leaf-ok rule-ok cert-ok))')], {}, 1, '(pw-error 1 bridge (duplicate-bridge b))'),
    ('unknown source context', 'fields', [('(bridge b src tgt', '(bridge b nowhere tgt')], {}, 1, '(pw-error 1 bridge (unknown-source b nowhere))'),
    ('unknown target context', 'fields', [('(bridge b src tgt', '(bridge b src nowhere')], {}, 1, '(pw-error 1 bridge (unknown-target b nowhere))'),
    ('missing clause', 'fields', [('leaf-ok rule-ok cert-ok', 'leaf-ok cert-ok', 1)], {}, 1, '(invalid-bridge b (missing-clause rule-ok))'),
    ('rule clause: wrong target symbol', 'rules', [('(pred q q)', '(pred q p)')], {}, 1, '(pw-error 1 bridge (invalid-bridge ab (rule-clause-fails)))'),
    ('rule clause: symbol not carried', 'rules', [('(pred q q)', '')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    # The rule clause under renamed.sexp's renaming map: break each position
    # the translation must carry, in the premise, the constructor sub-pattern,
    # the conclusion and the critical question's answer.
    ('rule clause: premise not carried', 'renamed', [('(pred p p2) ', '')], {}, 1, '(pw-error 1 bridge (invalid-bridge ab (rule-clause-fails)))'),
    ('rule clause: premise mapped wrong', 'renamed', [('(pred p p2)', '(pred p q2)')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    ('rule clause: sub-pattern not carried', 'renamed', [('(con f g) ', '')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    ('rule clause: sub-pattern mapped wrong', 'renamed', [('(con f g)', '(con f z2)')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    ('rule clause: conclusion mapped wrong', 'renamed', [('(pred q q2)', '(pred q ok2)')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    ('rule clause: question not carried', 'renamed', [('(pred ok ok2) ', '')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    ('rule clause: question mapped wrong', 'renamed', [('(pred ok ok2)', '(pred ok p2)')], {}, 1, '(invalid-bridge ab (rule-clause-fails))'),
    # Edges.
    ('edge: unknown bridge', 'fields', [('(edge b s0 t0 accepted)', '(edge nob s0 t0 accepted)')], {}, 1, '(pw-error 1 edge (unknown-bridge nob))'),
    ('edge: unknown source world', 'fields', [('(edge b s0 t0 accepted)', '(edge b s9 t0 accepted)')], {}, 1, '(pw-error 1 edge (unknown-world s9))'),
    ('edge: unknown target world', 'fields', [('(edge b s0 t0 accepted)', '(edge b s0 t9 accepted)')], {}, 1, '(pw-error 1 edge (unknown-world t9))'),
    ('edge: source context', 'fields', [('(edge b s0 t0 accepted)', '(edge b t1 t0 accepted)')], {}, 1, '(pw-error 1 edge (source-context b t1))'),
    ('edge: target context', 'fields', [('(edge b s0 t0 accepted)', '(edge b s0 s2 accepted)')], {}, 1, '(pw-error 1 edge (target-context b s2))'),
    ('edge: duplicate', 'fields', [('(edge b s0 t0 accepted)', '(edge b s0 t0 accepted) (edge b s0 t0 rejected)')], {}, 1, '(pw-error 1 edge (duplicate-edge b s0 t0))'),
    # Queries: elaboration against the declared registry.
    ('query: unknown context', 'fields', [('(pose tgt', '(pose nowhere')], {}, 1, '(pw-error 1 query (unknown-context nowhere))'),
    ('query: unknown bridge', 'fields', [('(dia back (status justified (atom q)))', '(dia nob (status justified (atom q)))')], {}, 1, '(pw-error 1 query (unknown-bridge nob))'),
    ('query: nested unknown bridge', 'fields', [('(dia back (status defeated (atom p)))', '(dia nob2 (status defeated (atom p)))')], {}, 1, '(pw-error 1 query (unknown-bridge nob2))'),
    ('query: bridge source mismatch', 'fields', [('(pose tgt (dia back', '(pose tgt (dia b')], {}, 1, '(pw-error 1 query (bridge-source-mismatch b tgt src))'),
    ('query: target operand undeclared', 'fields', [('(dia b (status justified (atom p)))', '(dia b (status justified (atom s)))')], {}, 1, '(pw-error 1 query (not-a-query tgt (undeclared-predicate s)))'),
    ('query: target operand ill-sorted', 'fields', [('(box b (status gap (atom p)))', '(box b (status gap (atom u)))')], {}, 1, '(not-a-query tgt (ill-sorted-arguments u))'),
    ('query: local claim ill-sorted', 'fields', [('(and (status gap (atom p))', '(and (status gap (atom p (con z)))')], {}, 1, '(not-a-query src (ill-sorted-arguments p))'),
    # Comparisons.
    ('comparison: unknown bridge', 'fields', [('(compare b s1 (atom p))', '(compare nob s1 (atom p))')], {}, 1, '(pw-error 1 comparison (unknown-bridge nob))'),
    ('comparison: unknown world', 'fields', [('(compare b s1 (atom p))', '(compare b s9 (atom p))')], {}, 1, '(pw-error 1 comparison (unknown-world s9))'),
    ('comparison: source context', 'fields', [('(compare b s1 (atom p))', '(compare b t0 (atom p))')], {}, 1, '(pw-error 1 comparison (source-context b t0))'),
    # Stage order: the first refusing stage wins.
    ('order: world before edge', 'fields', [('(world s1 src', '(world s0 src'), ('(edge b s0 t0 accepted)', '(edge nob s0 t0 accepted)')], {}, 1, '(pw-error 1 world '),
    ('order: bridge before edge', 'fields', [('(bridge b src tgt', '(bridge b nowhere tgt'), ('(edge b s0 t0 accepted)', '(edge nob s0 t0 accepted)')], {}, 1, '(pw-error 1 bridge '),
    ('order: edge before query', 'fields', [('(edge b s0 t0 accepted)', '(edge nob s0 t0 accepted)'), ('(pose tgt', '(pose nowhere')], {}, 1, '(pw-error 1 edge '),
    ('order: query before comparison', 'fields', [('(pose tgt', '(pose nowhere'), ('(compare b s1 (atom p))', '(compare nob s1 (atom p))')], {}, 1, '(pw-error 1 query '),
    # Fault order within a stage: two faults in one stage, and the one the
    # check order reaches first is reported.
    ('within wire: first malformed section', None, [(None, '(pw-run 1 (worlds (world w)) (edges (edge b)) (comparisons) (pw-surface 1 (bridges) (queries)))')], {}, 2, '(pw-error 1 wire malformed world)'),
    ('within wire: run sections before document', None, [(None, '(pw-run 1 (worlds) (edges (edge b)) (comparisons) (pw-surface 1 (bridges) (queries (pose c))))')], {}, 2, '(pw-error 1 wire malformed edge)'),
    ('within world: duplicate before reading', 'fields', [('(world s1 src (file "worlds/src-s1.sexp"))', '(world s0 src (file "worlds/missing.sexp"))')], {}, 1, '(pw-error 1 world (duplicate-world s0))'),
    ('within world: decoding before groups', 'inline', [('(check-input', '(check-inputs', 1), ('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l2)))', 1)], {}, 1, '(world-input w0 '),
    ('within world: groups before preflight', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l2)))', 1), ('(backends (backend nd 1))', '(backends (backend zz 1))', 1)], {}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    ('within world: preflight before environment', 'inline', [('(preds (pred p (args)) (pred q (args)))', '(preds (pred p (args)) (pred q (args)) (pred r (args)))', 2), ('(backends (backend nd 1))', '(backends (backend zz 1))', 2)], {}, 1, '(pw-error 1 world (world-rejected w1 R13))'),
    ('within world: environment before checking', 'inline', [('(preds (pred p (args)) (pred q (args)))', '(preds (pred p (args)) (pred q (args)) (pred r (args)))', 2), ('(attacks (undermine a2 a1 (pos)))', '(attacks)')], {}, 1, '(pw-error 1 world (context-environment w1 c))'),
    ('within bridge: duplicate before endpoints', 'fields', [('(bridge back tgt src', '(bridge b nowhere src')], {}, 1, '(pw-error 1 bridge (duplicate-bridge b))'),
    ('within bridge: source before target', 'fields', [('(bridge b src tgt', '(bridge b nowhere1 nowhere2')], {}, 1, '(pw-error 1 bridge (unknown-source b nowhere1))'),
    ('within bridge: endpoints before clauses', 'fields', [('(bridge b src tgt', '(bridge b nowhere tgt'), ('leaf-ok rule-ok cert-ok', 'cert-ok', 1)], {}, 1, '(pw-error 1 bridge (unknown-source b nowhere))'),
    # The two scan-order cases together pin leaf-ok, rule-ok, cert-ok.
    ('within bridge: clause scan order', 'fields', [('leaf-ok rule-ok cert-ok', 'cert-ok', 1)], {}, 1, '(invalid-bridge b (missing-clause leaf-ok))'),
    ('within bridge: clause scan order, rule-ok before cert-ok', 'fields', [('leaf-ok rule-ok cert-ok', 'leaf-ok', 1)], {}, 1, '(invalid-bridge b (missing-clause rule-ok))'),
    ('within bridge: clauses before rule clause', 'rules', [('leaf-ok rule-ok cert-ok', 'leaf-ok cert-ok'), ('(pred q q)', '(pred q p)')], {}, 1, '(invalid-bridge ab (missing-clause rule-ok))'),
    ('within edge: bridge before worlds', 'fields', [('(edge b s0 t0 accepted)', '(edge nob s9 t9 accepted)')], {}, 1, '(pw-error 1 edge (unknown-bridge nob))'),
    ('within edge: source world before target world', 'fields', [('(edge b s0 t0 accepted)', '(edge b s9 t9 accepted)')], {}, 1, '(pw-error 1 edge (unknown-world s9))'),
    ('within edge: source context before target context', 'fields', [('(edge b s0 t0 accepted)', '(edge b t1 s2 accepted)')], {}, 1, '(pw-error 1 edge (source-context b t1))'),
    ('within query: queries in order', 'fields', [('(pose src (dia b', '(pose nowhere1 (dia b'), ('(pose tgt', '(pose nowhere2')], {}, 1, '(pw-error 1 query (unknown-context nowhere1))'),
    ('within query: conjuncts in order', 'fields', [('(and (status gap (atom p))', '(and (status gap (atom zz1))'), ('(not (dia b (top)))', '(status gap (atom zz2))')], {}, 1, '(not-a-query src (undeclared-predicate zz1))'),
    ('within query: bridge before operand', 'fields', [('(dia b (status justified (atom p)))', '(dia nob (status justified (atom zz)))')], {}, 1, '(pw-error 1 query (unknown-bridge nob))'),
    ('within query: source mismatch before operand', 'fields', [('(pose tgt (dia back (status justified (atom q)))', '(pose tgt (dia b (status justified (atom zz)))')], {}, 1, '(pw-error 1 query (bridge-source-mismatch b tgt src))'),
    ('within comparison: bridge before world', 'fields', [('(compare b s1 (atom p))', '(compare nob s9 (atom p))')], {}, 1, '(pw-error 1 comparison (unknown-bridge nob))'),
    ('within comparison: comparisons in order', 'fields', [('(compare b s1 (atom p))', '(compare nob1 s1 (atom p))'), ('(compare b s0 (atom q))', '(compare nob2 s0 (atom q))')], {}, 1, '(pw-error 1 comparison (unknown-bridge nob1))'),
    # Results: comparisons read the declared map; modal operands are not
    # translated, so remapping p changes a profile and no modal answer.
    ('map dependence', 'fields', [('(pred p p)', '(pred p q)', 1)], {'same-queries-as': 'fields'}, 0, '(comparison b s1 (atom p) (comparable justified gap))'),
    ('first-match symbol map', 'fields', [('(pred p p)', '(pred p p) (pred p q)', 1)], {}, 0, '(comparison b s1 (atom p) (comparable gap justified))'),
    ('acceptance flip', 'fields', [('(edge b s0 t1 rejected)', '(edge b s0 t1 accepted)')], {}, 0, '(comparison b s0 (atom q) (comparable justified gap))'),
    ('all edges rejected', 'inline', [('(edge e w0 w1 accepted)', '(edge e w0 w1 rejected)')], {}, 0, '(comparison e w0 (atom p) (incomparable all-candidate-bridges-rejected))'),
    # The text boundary. Quoted Unicode identifiers and every non-ASCII path
    # case also run under LC_ALL=C and ISO-8859-1; the non-UTF-8 files do not.
    ('quoted unicode names', 'inline', [
        ('(world w0 c', '(world "w 0 ω" "c ☃"'), ('(world w1 c', '(world w1 "c ☃"'),
        ('(bridge e c c', '(bridge "é e" "c ☃" "c ☃"'),
        ('(edge e w0 w1 accepted)', '(edge "é e" "w 0 ω" w1 accepted)'),
        ('(compare e w0 (atom p))', '(compare "é e" "w 0 ω" (atom p))'),
        ('(compare e w1 (atom p))', '(compare "é e" w1 (atom p))'),
        ('(pose c ', '(pose "c ☃" '), ('(dia e ', '(dia "é e" '), ('(box e ', '(box "é e" ')],
     {'also-under': TEXT_BOUNDARY}, 0, '(comparison "é e" "w 0 ω" (atom p) (comparable defeated))'),
    ('non-ascii world path', 'fields', [('worlds/src-s0.sexp', 'worlds/src-sω é.sexp')],
     {'worlds/src-sω é.sexp': Copy('worlds/src-s0.sexp'), 'golden': 'fields', 'also-under': TEXT_BOUNDARY}, 0, '(pw-result 1 '),
    ('non-ascii run file path', 'inline', [], {'source': 'rün ω.sexp', 'golden': 'inline', 'also-under': TEXT_BOUNDARY}, 0, '(pw-result 1 '),
    # World paths resolve against the run file's directory, so a non-ASCII
    # directory reaches every world read.
    ('non-ascii run directory', 'fields', [], {'source': 'café ω/fields.sexp', 'golden': 'fields', 'also-under': TEXT_BOUNDARY}, 0, '(pw-result 1 '),
    # Error paths echo the path in their detail, so printing it must not fail.
    ('missing non-ascii run file', None, [(None, '')], {'source': 'rün ω.sexp', 'missing': True, 'also-under': TEXT_BOUNDARY}, 2, '(pw-error 1 io '),
    ('missing world under non-ascii directory', 'fields', [('worlds/src-s2.sexp', 'worlds/missing.sexp')], {'source': 'dir ω/fields.sexp', 'also-under': TEXT_BOUNDARY}, 1, '(world-input s2 '),
    ('world file not UTF-8', 'fields', [('worlds/src-s2.sexp', 'worlds/latin1.sexp')], {'worlds/latin1.sexp': b'(check-input \xff)'}, 1, '(world-input s2 '),
    ('run file not UTF-8', None, [(None, b'(pw-run 1 \xff)')], {}, 2, '(pw-error 1 io '),
]
LOCALE_CASES = {'quoted unicode names', 'non-ascii world path', 'non-ascii run file path',
                'non-ascii run directory', 'missing non-ascii run file',
                'missing world under non-ascii directory'}


def world_text(name):
    """A committed .lara world's text, for cases that write a variant of it."""
    return (SOURCES / 'worlds' / name).read_text(encoding='utf-8')


def policy_text(extra):
    """The committed pw-lara policy under a new id, with `extra` appended."""
    return world_text('pw-lara.policy.lara').replace('policy pw-lara', 'policy pw-variant') + extra


# The groups.sexp fixture's w1, as an inline source: it declares the leaf
# table w0.lara elaborates to, so it can share w0.lara's context.
INLINE_W1 = ('(inline (check-input (replay-id (core lara-core@0.2) (policy pw-t7) (backends (backend nd 1))'
             ' (theories) (artifact pw-groups-w1)) (unit (sigma (sorts) (cons) (preds (pred p (args)) (pred q (args))))'
             ' (policy (rules) (contraries (contrary (apat q) (apat p))) (exceptions)) (theories)'
             ' (leaves (leaf l1 (atom p)) (leaf l2 (atom q)) (leaf l3 (atom p))) (args (arg a1 (leaf l1)) (arg a2 (leaf l2)))'
             ' (attacks (undermine a2 a1 (pos))) (queries (atom p)) (groups reject (group g1 (l1 l3))))))')

# (name, substitutions on lara.sexp, options, exit, fragment). Options are
# those of CASES; extra keys write files under the run directory, beside the
# copied fixtures/pw/source/worlds. Every case runs `lara pw` on the run file,
# then `lara pw-input`: a derived document must run to `lara pw`'s bytes on
# both drivers, and a refused derivation must print `lara pw`'s envelope.
SOURCE_CASES = [
    # Every way a .lara world stops before an envelope exists is world-input.
    # Each fragment names the step that stopped, not just the fault: the seven
    # pre-envelope refusals share one constructor, so a prefix-only assertion
    # would let a policy-parse failure pass a source-invalid case vacuously.
    #
    # Two of them ("cannot read" for a missing file and for one that is not
    # UTF-8) are told apart only by GHC's own `IOError` text, so that much is
    # `base`-owned rather than this project's. The pins stop at the operation
    # and reason (`openFile: does not exist`, `hGetContents: invalid argument`)
    # and deliberately omit the parenthetical `strerror` tail, which is the
    # part a platform or toolchain can reword with no behaviour change.
    ('lara: missing program', [('worlds/w0.lara', 'worlds/missing.lara')], {}, 1, ('(pw-error 1 world (world-input w0 "cannot read ', 'worlds/missing.lara: openFile: does not exist')),
    ('lara: program does not parse', [('worlds/w0.lara', 'worlds/broken.lara')], {'worlds/broken.lara': 'artifact x at'}, 1, ('(world-input w0 "parse error at ', 'worlds/broken.lara:1:14: expected an identifier"))')),
    # Program text that is not UTF-8: the locale encoding the PW doors set is
    # strict, so this is the same read failure `lara check` reports rather than
    # a surrogate-escaped decode. Both PW doors agree either way, so only this
    # direct case sees it — the cross-driver comparison cannot.
    ('lara: program is not UTF-8', [('worlds/w0.lara', 'worlds/latin1.lara')], {'worlds/latin1.lara': b'# bad byte: \xff\n' + world_text('w0.lara').encode('utf-8')}, 1, ('(world-input w0 "cannot read ', 'worlds/latin1.lara: hGetContents: invalid argument')),
    ('lara: policy missing', [('worlds/w0.lara', 'worlds/nopolicy.lara')], {'worlds/nopolicy.lara': world_text('w0.lara').replace('policy pw-lara', 'policy nowhere')}, 1, ('(world-input w0 "cannot read policy ', 'worlds/nowhere.policy.lara: openFile: does not exist')),
    ('lara: source invalid', [('worlds/w0.lara', 'worlds/duplicate-leaf.lara')], {'worlds/duplicate-leaf.lara': world_text('w0.lara').replace('leaf l3 : p', 'leaf l1 : p')}, 1, '(world-input w0 "source invalid: duplicate leaf id '),
    # An undeclared leaf reference elaborates, and is the checker's R1 on the
    # derived envelope, exactly as on a hand-written one.
    ('lara: undeclared leaf is the checker\'s R1', [('worlds/w0.lara', 'worlds/undeclared.lara')], {'worlds/undeclared.lara': world_text('w0.lara').replace('by leaf(l3)', 'by leaf(l9)')}, 1, '(pw-error 1 world (world-rejected w0 R1))'),
    ('lara: admission stop', [('worlds/w0.lara', 'worlds/stop.lara')],
     {'worlds/stop.lara': world_text('w0.lara').replace('policy pw-lara', 'policy pw-variant'),
      'worlds/pw-variant.policy.lara': policy_text('\nadmission { (observed, user) = reject }\n')}, 1, '(world-input w0 "leaf \'l1\': kind=observed, provenance=user matched admission row (observed, user) = reject (R8)'),
    # A policy quarantine prunes support the frozen envelope cannot express,
    # so no envelope is derived (Lara.Elaborate.sourceResultCheckInput). The
    # detail says that, then the audit: the audit line alone is what `lara
    # check` prints beside an accept.
    ('lara: policy quarantine', [('worlds/w0.lara', 'worlds/quarantined.lara')],
     {'worlds/quarantined.lara': world_text('w0.lara').replace('policy pw-lara', 'policy pw-variant'),
      'worlds/pw-variant.policy.lara': policy_text('\nadmission { (observed, user) = quarantine }\n')}, 1, '(world-input w0 "policy quarantine: a check-input envelope cannot express a pruned unit; admission audit: leaves [l1{policy-quarantine}'),
    # Worlds are read in order, and the first without an envelope is reported.
    ('lara: first unreadable world is reported', [('worlds/w0.lara', 'worlds/missing0.lara'), ('worlds/w1.lara', 'worlds/missing1.lara')], {}, 1, ('(world-input w0 "cannot read ', 'worlds/missing0.lara: openFile: does not exist')),
    # A group conflict reached through elaboration: l1, which no argument
    # uses, now reports q against l3's p. The derived envelope carries the
    # group, and the loader refuses it on both drivers.
    ('lara: conflicting group', [('worlds/w0.lara', 'worlds/conflict.lara')], {'worlds/conflict.lara': world_text('w0.lara').replace('leaf l1 : p', 'leaf l1 : q')}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    ('lara: conflicting group under reject mode', [('worlds/w0.lara', 'worlds/conflict.lara')],
     {'worlds/conflict.lara': world_text('w0.lara').replace('leaf l1 : p', 'leaf l1 : q').replace('policy pw-lara', 'policy pw-variant'),
      'worlds/pw-variant.policy.lara': policy_text('\nduplicate-reports = reject\n')}, 1, '(pw-error 1 world (world-groups w0 g1))'),
    ('lara: consistent group under reject mode', [('worlds/w0.lara', 'worlds/r0.lara'), ('worlds/w1.lara', 'worlds/r1.lara')],
     {'worlds/r0.lara': world_text('w0.lara').replace('policy pw-lara', 'policy pw-variant'),
      'worlds/r1.lara': world_text('w1.lara').replace('policy pw-lara', 'policy pw-variant'),
      'worlds/pw-variant.policy.lara': policy_text('\nduplicate-reports = reject\n'), 'golden': 'lara'}, 0, '(pw-result 1 '),
    # A .lara world and an inline envelope share a context when they declare
    # the same environment.
    ('lara: mixed with an inline world', [('(lara "worlds/w1.lara")', INLINE_W1)], {'golden': 'lara'}, 0, '(pw-result 1 '),
    # A checker rejection of an elaborated world is world-rejected, as for an
    # envelope: without its undermine, w1's contrary a1 and a2 are attack-incomplete.
    ('lara: checker rejects the elaborated world', [('worlds/w1.lara', 'worlds/rejected.lara')], {'worlds/rejected.lara': world_text('w1.lara').replace('undermine a2 a1.leaf\n', '')}, 1, '(pw-error 1 world (world-rejected w1 missing-conflict))'),
    # The text boundary: program paths and program text are UTF-8 under every
    # locale, as world paths are.
    ('lara: non-ascii program path', [('worlds/w0.lara', 'worlds/w ω0.lara')], {'worlds/w ω0.lara': Copy('../source/worlds/w0.lara'), 'golden': 'lara', 'also-under': TEXT_BOUNDARY}, 0, '(pw-result 1 '),
    ('lara: non-ascii program text', [('worlds/w0.lara', 'worlds/omega.lara')], {'worlds/omega.lara': world_text('w0.lara').replace('"p holds"', '"p holds — ω"'), 'golden': 'lara', 'also-under': TEXT_BOUNDARY}, 0, '(pw-result 1 '),
    # Refusals before any world is read are the same envelope from both doors.
    ('lara: run file does not decode', [('(edge e w0 w1 accepted)', '(edge e w0 w1 maybe)')], {}, 2, '(pw-error 1 wire malformed acceptance)'),
]
# The two reruns above are the only test of the locale encoding `pwTextBoundary`
# sets for .lara text, so the set is pinned the way LOCALE_CASES is: dropping an
# `also-under` must fail the gate rather than silently retire the coverage.
SOURCE_LOCALE_CASES = {'lara: non-ascii program path', 'lara: non-ascii program text'}


def build():
    for command, cwd in ((['cabal', 'build', '-v0', 'exe:lara'], ROOT),
                         (['lake', 'build', 'pw-run'], ROOT / 'lean')):
        result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
        if result.returncode != 0:
            print(f'FAIL: {" ".join(command)}\n{result.stdout}{result.stderr}')
            sys.exit(2)


# Asks glibc's setlocale, the call GHC's runtime makes, in an unconfined
# process. /usr/bin/locale is not a usable probe: Ubuntu 26.04's AppArmor
# profile confines it to the system charmaps, so it reads a LOCPATH locale as
# ASCII even though every other process loads it.
LOCALE_PROBE = ('import locale\n'
                'try:\n'
                '    locale.setlocale(locale.LC_ALL, "")\n'
                'except locale.Error as err:\n'
                '    print(f"setlocale failed: {err}")\n'
                'else:\n'
                '    print(locale.nl_langinfo(locale.CODESET))\n')


def build_latin1():
    """Build the ISO-8859-1 locale into LATIN1_LOCALES with localedef, which
    needs no root. Return None when the locale loads, else why it does not."""
    LATIN1_LOCALES.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, **LATIN1}
    try:
        # -c writes the locale despite localedef's portability warnings; the
        # probe below is what decides whether it is usable.
        subprocess.run(['localedef', '-c', '-i', 'en_US', '-f', 'ISO-8859-1',
                        str(LATIN1_LOCALES / 'en_US.ISO-8859-1')], capture_output=True)
    except FileNotFoundError as err:
        return str(err)
    probe = subprocess.run([sys.executable, '-c', LOCALE_PROBE], capture_output=True,
                           text=True, env=env)
    codeset = probe.stdout.strip()
    if codeset == 'ISO-8859-1':
        return None
    try:
        hint = subprocess.run(['locale', 'charmap'], capture_output=True, text=True,
                              env=env).stdout.strip()
    except FileNotFoundError:
        hint = 'unavailable'
    return (f'setlocale under the built locale reports {codeset!r} '
            f'(`locale charmap` says {hint!r})')


def haskell_exe():
    result = subprocess.run(['cabal', 'list-bin', 'exe:lara'], cwd=ROOT,
                            capture_output=True, text=True, check=True)
    return [result.stdout.strip(), 'pw']


def compare_drivers(haskell, path, env=None, exact=False):
    """Byte equality, except that a detail-bearing fault's final atom is
    masked; the rest of such an envelope must still agree atom for atom. With
    exact, nothing is masked and the bytes themselves must agree."""
    h_code, h_out = run(haskell, path, env)
    l_code, l_out = run([str(LEAN)], path, env)
    assert h_code == l_code, ('exit codes differ', h_code, l_code, h_out, l_out)
    h_tree, l_tree = read_sexpr(h_out), read_sexpr(l_out)
    if exact or (mask(h_tree) == h_tree and mask(l_tree) == l_tree):
        assert h_out == l_out, ('outputs differ', h_out, l_out)
    else:
        assert mask(h_tree) == mask(l_tree), ('outputs differ', h_out, l_out)
    return h_code, h_out


def golden_text(fixture, root=FIXTURES):
    return (root / f'{fixture}.expected').read_text(encoding='utf-8')


def source_heads(text):
    """The head keyword of every world source in a printed run document."""
    tree = read_sexpr(text)
    assert tree[:2] == ['pw-run', '1'] and tree[2][0] == 'worlds', text
    return [world[3][0] for world in tree[2][1:]]


def derive(haskell, path, env=None):
    """Run `lara pw-input`; on success also write the derived document beside
    the run file and check that every world source is inline."""
    code, out = run([haskell[0], 'pw-input'], path, env)
    if code == 0:
        assert all(head == 'inline' for head in source_heads(out)), out
        derived = path.parent / 'derived.sexp'
        derived.write_text(out, encoding='utf-8')
        return code, out, derived
    return code, out, None


def check_derivation(haskell, path, code, out, env=None):
    """The derived document runs to `lara pw`'s bytes on both drivers, or the
    derivation is refused with `lara pw`'s own envelope."""
    d_code, d_out, derived = derive(haskell, path, env)
    if derived is None:
        assert (d_code, d_out) == (code, out), ('derivation refused differently', d_out, out)
        return
    got, got_out = compare_drivers(haskell, derived, env)
    assert (got, got_out) == (code, out), ('derived run differs', got_out, out)


def check_pw_subtree_total():
    """Every .sexp under fixtures/pw/ must be owned by a gate that runs it.

    differential.sh and gen-anchor-manifest.sh exclude the whole fixtures/pw/
    subtree from the check-input@1 anchor set and from fixtures/ANCHORS.tsv,
    on the grounds that this family has its own harnesses. That argument only
    holds while the family is covered end to end. The other four excluded
    families are pinned by a manifest or discovered manifest-driven, so a stray
    unlisted file there is a setup failure; without this assertion a new .sexp
    at fixtures/pw/*.sexp, or under any new fixtures/pw/<subdir>/, would be
    discovered by no gate and pinned by no manifest — the exact state the anchor
    pin exists to prevent, relocated rather than removed.
    """
    root = ROOT / 'fixtures/pw'
    owned = set(FIXTURES.glob('*.sexp'))
    owned |= set((FIXTURES / 'worlds').glob('*.sexp'))
    owned.add(ROOT / 'fixtures/pw/declared.sexp')  # scripts/check-pw-example.py
    stray = sorted(p for p in root.rglob('*.sexp') if p not in owned)
    if stray:
        for p in stray:
            print(f'FAIL: {p.relative_to(ROOT)} is under fixtures/pw/ but no gate '
                  f'runs it; differential.sh excludes the whole subtree')
        sys.exit(2)


def check_fixtures(haskell, update):
    fixtures = sorted(FIXTURES.glob('*.sexp'))
    if not fixtures:
        print(f'FAIL: no fixtures under {FIXTURES}')
        sys.exit(2)
    for fixture in fixtures:
        code, out = compare_drivers(haskell, fixture)
        l_out = run([str(LEAN)], fixture)[1]
        assert out == l_out, ('fixture bytes differ', fixture, out, l_out)
        assert code == 0, (fixture, code, out)
        golden = fixture.with_suffix('.expected')
        if update:
            golden.write_text(out, encoding='utf-8')
        assert golden.exists(), f'missing golden {golden} (run with --update)'
        assert golden.read_text(encoding='utf-8') == out, ('golden differs', golden, out)
        # Derivation is the identity on meaning: with every file source
        # inlined, both drivers still print the golden.
        with tempfile.TemporaryDirectory(prefix='lara-pw-conf-') as tmp:
            home = pathlib.Path(tmp)
            shutil.copytree(FIXTURES / 'worlds', home / 'worlds')
            shutil.copy(fixture, home / fixture.name)
            check_derivation(haskell, home / fixture.name, code, out)
    return len(fixtures)


def check_source_fixtures(haskell, update):
    """Family 3's committed fixtures: `lara pw` prints the golden, the Lean
    reference refuses the file's first .lara world as world-input, and the
    derived document runs to the golden on both drivers."""
    fixtures = sorted(SOURCES.glob('*.sexp'))
    if not fixtures:
        print(f'FAIL: no fixtures under {SOURCES}')
        sys.exit(2)
    for fixture in fixtures:
        code, out = run(haskell, fixture)
        assert code == 0, (fixture, code, out)
        l_code, l_out = run([str(LEAN)], fixture)
        assert l_code == 1 and l_out.startswith('(pw-error 1 world (world-input '), ('lean on .lara sources', l_out)
        with tempfile.TemporaryDirectory(prefix='lara-pw-conf-') as tmp:
            home = pathlib.Path(tmp)
            shutil.copytree(SOURCES / 'worlds', home / 'worlds')
            shutil.copy(fixture, home / fixture.name)
            check_derivation(haskell, home / fixture.name, code, out)
        golden = fixture.with_suffix('.expected')
        if update:
            golden.write_text(out, encoding='utf-8')
        assert golden.exists(), f'missing golden {golden} (run with --update)'
        assert golden.read_text(encoding='utf-8') == out, ('golden differs', golden, out)
    return len(fixtures)


def write(path, content):
    if isinstance(content, Copy):
        shutil.copy((FIXTURES / content).resolve(), path)
    elif isinstance(content, bytes):
        path.write_bytes(content)
    else:
        path.write_text(content, encoding='utf-8')


def assert_fragments(fragment, out):
    """Every fragment a case names must appear in stdout.

    A tuple is how a case pins text on both sides of an echoed path: the gate
    runs the drivers on an absolute path, so a detail's own path is absolute,
    and only the relative tail of it is stable across the two.
    """
    for want in (fragment,) if isinstance(fragment, str) else fragment:
        assert want in out, ('fragment', want, out)


def run_case(haskell, case, env=None):
    name, base, subs, options, code, fragment = case
    with tempfile.TemporaryDirectory(prefix='lara-pw-conf-') as tmp:
        source = pathlib.Path(tmp) / options.get('source', 'input.sexp')
        home = source.parent
        home.mkdir(parents=True, exist_ok=True)
        shutil.copytree(FIXTURES / 'worlds', home / 'worlds')
        if base is None:
            text = subs[0][1]
        else:
            text = (FIXTURES / f'{base}.sexp').read_text(encoding='utf-8')
            for sub in subs:
                text = mutate(text, *sub)
            text += options.get('append', '')
        for rel, content in options.items():
            if rel not in OPTIONS:
                write(home / rel, content)
        if not options.get('missing'):
            write(source, text)
        try:
            got, out = compare_drivers(haskell, source, env, options.get('exact', False))
            assert got == code, ('exit', got, code, out)
            assert_fragments(fragment, out)
            if 'golden' in options:
                assert out == golden_text(options['golden']), ('golden', options['golden'], out)
            if 'same-queries-as' in options:
                expected = read_sexpr(golden_text(options['same-queries-as']))
                assert read_sexpr(out)[2] == expected[2], ('queries section changed', out)
        except AssertionError as err:
            print(f'FAIL: {name}{" under " + str(env) if env else ""}: {err}')
            sys.exit(1)


def run_source_case(haskell, case, env=None):
    name, subs, options, code, fragment = case
    with tempfile.TemporaryDirectory(prefix='lara-pw-conf-') as tmp:
        home = pathlib.Path(tmp)
        shutil.copytree(SOURCES / 'worlds', home / 'worlds')
        text = (SOURCES / 'lara.sexp').read_text(encoding='utf-8')
        for sub in subs:
            text = mutate(text, *sub)
        for rel, content in options.items():
            if rel not in OPTIONS:
                write(home / rel, content)
        source = home / 'input.sexp'
        write(source, text)
        try:
            got, out = run(haskell, source, env)
            assert got == code, ('exit', got, code, out)
            assert_fragments(fragment, out)
            if 'golden' in options:
                assert out == golden_text(options['golden'], SOURCES), ('golden', options['golden'], out)
            check_derivation(haskell, source, got, out, env)
        except AssertionError as err:
            print(f'FAIL: {name}{" under " + str(env) if env else ""}: {err}')
            sys.exit(1)


def check_source_cases(haskell, latin1_ok):
    runs = skipped = 0
    for case in SOURCE_CASES:
        for env in (None, *case[2].get('also-under', ())):
            if env is LATIN1 and not latin1_ok:
                skipped += 1
                continue
            run_source_case(haskell, case, env)
            runs += 1
    # Locale coverage for .lara program paths and program text must not vanish
    # with a case edit, as for CASES.
    covered = {case[0] for case in SOURCE_CASES if case[2].get('also-under') == TEXT_BOUNDARY}
    assert covered == SOURCE_LOCALE_CASES, covered ^ SOURCE_LOCALE_CASES
    return runs, skipped


def check_cases(haskell, latin1_ok):
    """Run every case, and its reruns; return (runs, skipped reruns)."""
    runs = skipped = 0
    for case in CASES:
        for env in (None, *case[3].get('also-under', ())):
            if env is LATIN1 and not latin1_ok:
                skipped += 1
                continue
            run_case(haskell, case, env)
            runs += 1
    # Locale coverage must not vanish with a case edit: output, the run-file
    # argument and file paths are UTF-8 whatever the locale.
    covered = {case[0] for case in CASES if case[3].get('also-under') == TEXT_BOUNDARY}
    assert covered == LOCALE_CASES, covered ^ LOCALE_CASES
    # The run file itself unreadable: both drivers report io at exit 2.
    with tempfile.TemporaryDirectory(prefix='lara-pw-conf-') as tmp:
        got, out = compare_drivers(haskell, pathlib.Path(tmp) / 'missing.sexp')
        assert got == 2 and out.startswith('(pw-error 1 io '), out
    return runs + 1, skipped


def main():
    update = '--update' in sys.argv
    check_depth_bound()
    check_pw_subtree_total()
    if '--no-build' not in sys.argv:
        build()
    latin1_problem = build_latin1()
    if latin1_problem and sys.platform.startswith('linux'):
        print(f'FAIL: cannot build the ISO-8859-1 locale: {latin1_problem}')
        sys.exit(2)
    haskell = haskell_exe()
    fixtures = check_fixtures(haskell, update)
    runs, skipped = check_cases(haskell, latin1_problem is None)
    source_fixtures = check_source_fixtures(haskell, update)
    source_runs, source_skipped = check_source_cases(haskell, latin1_problem is None)
    print(f'PW outer runtime conformance passed: {fixtures} fixtures, {len(CASES)} cases, {runs} runs;'
          f' {source_fixtures} .lara source fixtures, {len(SOURCE_CASES)} source cases, {source_runs} runs.')
    if skipped or source_skipped:
        print(f'  skipped {skipped + source_skipped} ISO-8859-1 reruns: {latin1_problem}')


if __name__ == '__main__':
    main()
