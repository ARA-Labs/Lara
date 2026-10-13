"""Bounded prereview guard for explicitly annotated ground support identities.

This checks annotation completeness and syntax for the listed ground examples.
It never infers propositions, checks typing, or computes acceptance/attacks.
Argument and derived-claim names identify annotation rows, not support keys.
"""
from evidence_measured import wire


def need(ok, message):
    if not ok:
        raise ValueError('support annotation: ' + message)


def ground_term(term):
    need(isinstance(term, list) and bool(term), 'missing ground substitution term')
    if term[0] in ('num', 'str'):
        need(len(term) == 2 and isinstance(term[1], str), 'malformed literal')
    elif term[0] == 'con':
        need(len(term) >= 2 and isinstance(term[1], str), 'malformed constructor')
        for child in term[2:]:
            ground_term(child)
    else:
        raise ValueError('support annotation: unsupported/non-ground substitution term')



def support_key(term):
    """Encode identity in the bounded annotation schema, retaining every field.

    This is not a universal typed-core equality or normalization procedure.
    """
    need(isinstance(term, list) and bool(term), 'missing term')
    if term[0] == 'leaf':
        need(len(term) == 2 and isinstance(term[1], str), 'malformed leaf')
    elif term[0] == 'inst':
        need(len(term) == 7 and isinstance(term[1], str), 'incomplete rule instance')
        for value, tag in zip(term[2:], ('subst', 'premises', 'discharges', 'holes', 'assurance')):
            need(isinstance(value, list) and value and value[0] == tag, 'missing ' + tag)
        for binding in term[2][1:]:
            need(isinstance(binding, list) and len(binding) == 2 and isinstance(binding[0], str), 'malformed substitution')
            ground_term(binding[1])
        for child in term[3][1:]:
            support_key(child)
        for discharge in term[4][1:]:
            need(isinstance(discharge, list) and len(discharge) == 2 and isinstance(discharge[0], str), 'malformed discharge')
            support_key(discharge[1])
        need(all(isinstance(h, str) for h in term[5][1:]), 'malformed hole')
        need(len(term[6]) == 2 and term[6][1] in ('none', 'trusted'), 'unsupported assurance')
    else:
        raise ValueError('support annotation: unsupported term shape')
    return wire(term)


def validate_ground_annotations(program, policy, annotations):
    """Match explicit annotations to this bounded parameter-free source recipe.

    The recipe permits parameter-free, question-free defeasible rules with
    nullary atom premises/conclusions, no labels or certifiers, and false
    allow-trusted flags. Source applications use leaf/argument references only.
    Shapes outside that recipe fail closed. Other authors must supply a reviewed extension.
    """
    need(isinstance(annotations, dict) and bool(annotations), 'missing annotations')
    declarations = program[6]
    need(declarations[0] == 'l' and policy[3][0] == 'l', 'unsupported declaration lists')
    need(all(isinstance(d, list) and len(d) == 2 and d[0] in ('dl', 'dc', 'da', 'dk')
             for d in declarations[1:]), 'unsupported declaration shape')
    leaf_rows = [d[1] for d in declarations[1:] if d[0] == 'dl']
    arg_rows = [d[1] for d in declarations[1:] if d[0] == 'da']
    need(all(isinstance(l, list) and len(l) == 7 and l[0] == 'leaf' and isinstance(l[1], str)
             for l in leaf_rows), 'malformed source leaf')
    need(all(isinstance(a, list) and len(a) == 4 and a[0] == 'arg' and isinstance(a[1], str)
             for a in arg_rows), 'malformed source argument')
    leaf_ids = [l[1] for l in leaf_rows]; arg_ids = [a[1] for a in arg_rows]
    need(len(leaf_ids) == len(set(leaf_ids)), 'duplicate leaf identity')
    need(len(arg_ids) == len(set(arg_ids)), 'duplicate argument identity')
    need(not set(leaf_ids) & set(arg_ids), 'ambiguous leaf/argument reference')
    leaves = set(leaf_ids)
    arguments = {a[1]: a[3] for a in arg_rows}
    rule_rows = policy[3][1:]
    need(all(isinstance(r, list) and len(r) == 10 and r[0] == 'rule' and isinstance(r[1], str)
             and all(isinstance(r[i], list) and r[i] and r[i][0] == 'l' for i in (2, 4, 5, 8, 9))
             for r in rule_rows), 'malformed source rule')
    # The supported recipe uses nullary ground atom patterns only. Reject
    # auxiliary fields and modes that would require additional elaboration;
    # this is a shape contract, not rule typing or proposition inference.
    def nullary_atom_pattern(value):
        return (isinstance(value, list) and len(value) == 2 and
                value[0] == 'apat' and isinstance(value[1], str))

    for rule in rule_rows:
        need(rule[2] == ['l'], 'unannotated/non-ground rule parameters')
        need(rule[3] == ['defeasible'], 'unsupported source rule mode')
        need(all(nullary_atom_pattern(premise) for premise in rule[4][1:]),
             'unsupported source rule premise proposition')
        need(rule[5] == ['l'], 'source premise labels require reviewed annotation extension')
        need(nullary_atom_pattern(rule[6]), 'unsupported source rule conclusion proposition')
        need(rule[7] == ['false'], 'unsupported source rule allow-trusted boolean')
        need(rule[8] == ['l'], 'source certifiers require reviewed annotation extension')
    rule_ids = [r[1] for r in rule_rows]
    need(len(rule_ids) == len(set(rule_ids)), 'duplicate rule identity')
    need(all(r[9] == ['l'] for r in rule_rows), 'rule questions require reviewed annotation extension')
    rules = {r[1]: r for r in rule_rows}
    need(set(annotations) == set(arguments), 'incomplete argument coverage')
    active = set()

    def reference(name):
        if name in leaves:
            return ['leaf', name]
        need(name in arguments and name not in active, 'unknown or recursive reference')
        active.add(name)
        term = expand(arguments[name])
        active.remove(name)
        return term

    def expand(raw):
        if isinstance(raw, list) and len(raw) == 2 and raw[0] == 'et':
            need(isinstance(raw[1], list) and len(raw[1]) == 2 and raw[1][0] == 'sl' and raw[1][1] in leaves,
                 'unsupported explicit term')
            return ['leaf', raw[1][1]]
        need(isinstance(raw, list) and len(raw) == 6 and raw[0] == 'it', 'unsupported source argument shape')
        need(raw[1] in rules and rules[raw[1]][2] == ['l'], 'unannotated/non-ground rule parameters')
        need(raw[2][0] == 'l' and raw[3][0] == 'l' and raw[4][0] == 'l', 'unsupported source instance fields')
        need(raw[5] == ['an'], 'unsupported source assurance')
        need(all(isinstance(r, str) for r in raw[2][1:]), 'unsupported source premise')
        need(raw[3] == ['l'] and raw[4] == ['l'], 'source discharges/holes require reviewed extension')
        return ['inst', raw[1], ['subst'], ['premises'] + [reference(r) for r in raw[2][1:]],
                ['discharges'], ['holes'], ['assurance', 'none']]

    keys = {}
    for name, annotation in annotations.items():
        key = support_key(annotation)
        need(key == support_key(reference(name)), 'source/annotation mismatch: ' + name)
        need(key not in keys.values(), 'duplicate support key: ' + name)
        keys[name] = key
    return keys


def t07_annotations(groups=0, after=False):
    leaf = ['leaf', 'seed']
    def inst(rule, premise):
        return ['inst', rule, ['subst'], ['premises', premise], ['discharges'], ['holes'], ['assurance', 'none']]
    witness = inst('r-t', leaf)
    terms = {'witness': witness, 'consumer': inst('r-v', witness), 'attacker': inst('r-s', leaf)}
    if after:
        terms['new-attacker'] = inst('r-s-new', leaf)
    for i in range(groups):
        terms[f'p8-inert-{i}-root'] = ['leaf', f'p8-inert-{i}']
    return terms
