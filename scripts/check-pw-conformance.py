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

Two families:

1. Committed fixtures (fixtures/pw/run/*.sexp). Each fixture's stdout must
   equal its committed `*.expected` golden byte for byte, from both drivers,
   with exit 0. `--update` rewrites the goldens from the Haskell driver, and
   only after the Lean driver has produced the same bytes.
2. Mutations of those fixtures: every error stage and fault; stage order, and
   fault order within each stage; every field of a context's environment; the
   rule clause under a renaming symbol map; map and acceptance dependence; and
   the text boundary (quoted Unicode names, non-ASCII file paths and run
   directories, files that are not UTF-8). For each case both drivers must
   agree on the exit code and on stdout, and stdout must contain the fragment
   the case names; some cases also pin stdout, or its queries section, to a
   committed golden. Agreement is byte equality except for the three faults
   whose last atom is runtime-specific text (a reader's syntax message, a
   world's read or decode failure, and an unreadable run file): there that one
   atom is masked, and every other atom, including the arity, must agree.

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
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'fixtures/pw/run'
LEAN = ROOT / 'lean/.lake/build/bin/pw-run'
C_LOCALE = {'LC_ALL': 'C', 'LANG': 'C'}
# An 8-bit locale: every argv byte decodes to some character, so a runtime that
# decodes the run-file argument with the locale looks up the wrong bytes.
LATIN1_LOCALES = pathlib.Path(tempfile.gettempdir()) / 'lara-pw-conf-locales'
LATIN1 = {'LC_ALL': 'en_US.ISO-8859-1', 'LANG': 'en_US.ISO-8859-1', 'LOCPATH': str(LATIN1_LOCALES)}


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
    still fails instead of being truncated away."""
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
OPTIONS = ('append', 'source', 'missing', 'golden', 'same-queries-as', 'also-under')
TEXT_BOUNDARY = [C_LOCALE, LATIN1]

# (name, base fixture or None, substitutions, options, exit, fragment).
# A substitution is (old, new) or (old, new, nth). A base of None means the
# first substitution's `new` is the whole input (text or bytes).
CASES = [
    # Wire: the run codec and the embedded pw-surface codec.
    ('syntax: trailing form', 'fields', [], {'append': '\n(extra)'}, 2, '(pw-error 1 wire syntax '),
    ('syntax: empty input', None, [(None, '')], {}, 2, '(pw-error 1 wire syntax '),
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
    ('world with groups', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l2)))', 1)], {}, 1, '(pw-error 1 world (world-groups w0))'),
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
    ('within world: groups before preflight', 'inline', [('(queries (atom p))', '(queries (atom p)) (groups quarantine (group g1 (l1 l2)))', 1), ('(backends (backend nd 1))', '(backends (backend zz 1))', 1)], {}, 1, '(pw-error 1 world (world-groups w0))'),
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


def compare_drivers(haskell, path, env=None):
    """Byte equality, except that a detail-bearing fault's final atom is
    masked; the rest of such an envelope must still agree atom for atom."""
    h_code, h_out = run(haskell, path, env)
    l_code, l_out = run([str(LEAN)], path, env)
    assert h_code == l_code, ('exit codes differ', h_code, l_code, h_out, l_out)
    h_tree, l_tree = read_sexpr(h_out), read_sexpr(l_out)
    if mask(h_tree) == h_tree and mask(l_tree) == l_tree:
        assert h_out == l_out, ('outputs differ', h_out, l_out)
    else:
        assert mask(h_tree) == mask(l_tree), ('outputs differ', h_out, l_out)
    return h_code, h_out


def golden_text(fixture):
    return (FIXTURES / f'{fixture}.expected').read_text(encoding='utf-8')


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
    return len(fixtures)


def write(path, content):
    if isinstance(content, Copy):
        shutil.copy(FIXTURES / content, path)
    elif isinstance(content, bytes):
        path.write_bytes(content)
    else:
        path.write_text(content, encoding='utf-8')


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
            got, out = compare_drivers(haskell, source, env)
            assert got == code, ('exit', got, code, out)
            assert fragment in out, ('fragment', fragment, out)
            if 'golden' in options:
                assert out == golden_text(options['golden']), ('golden', options['golden'], out)
            if 'same-queries-as' in options:
                expected = read_sexpr(golden_text(options['same-queries-as']))
                assert read_sexpr(out)[2] == expected[2], ('queries section changed', out)
        except AssertionError as err:
            print(f'FAIL: {name}{" under " + str(env) if env else ""}: {err}')
            sys.exit(1)


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
    if '--no-build' not in sys.argv:
        build()
    latin1_problem = build_latin1()
    if latin1_problem and sys.platform.startswith('linux'):
        print(f'FAIL: cannot build the ISO-8859-1 locale: {latin1_problem}')
        sys.exit(2)
    haskell = haskell_exe()
    fixtures = check_fixtures(haskell, update)
    runs, skipped = check_cases(haskell, latin1_problem is None)
    print(f'PW outer runtime conformance passed: {fixtures} fixtures, {len(CASES)} cases, {runs} runs.')
    if skipped:
        print(f'  skipped {skipped} ISO-8859-1 reruns: {latin1_problem}')


if __name__ == '__main__':
    main()
