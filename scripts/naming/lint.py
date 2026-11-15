#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""The naming lint of `docs/naming.md`, over a declaration dump of `scripts/naming/Dump.lean`.

    python3 scripts/naming/lint.py DUMP.tsv [DUMP.tsv ...]

Checks the Lantana and LantanaTest declarations of the dumps (Iris-Lean's are skipped) and
prints one line per violation; exit code 1 if there is any.  `scripts/naming/lint.sh` makes the
dumps and runs it.  Accepted exceptions are listed in ALLOW below, each with its reason.
"""
import re, sys

ALLOW = {
    # Iris-Lean's functor and functor-bundle names are UpperCamelCase (`AuthURF`, `GFunctor`).
    'functor': re.compile(r'(F|RF|URF|GF|OF)$'),
    # An order relation implementing `LE`/`HasSubset` is `le`, as the class's field
    # (`TrSpec.le`, `Model.Obligations.le`; docs/naming.md, §2).
    'order': {'le', 'lt'},
    # Attribute names follow Lean's attributes (`simp`, Iris-Lean's `rocq_alias`).
    'attribute': {'lantana_alias'},
}
# Words of theorem names that the convention replaces (docs/naming.md, §2): word -> replacement.
VOCAB = {'ex': 'exists', 'exist': 'exists', 'all': 'forall', 'mon': 'mono', 'idemp': 'idem',
         'included': 'inc', 'impl': 'imp', 'l': 'left', 'r': 'right', 'upd': 'update'}
# `all` meaning "for all the roots" (not ∀) in these lemma families.
VOCAB_OK = re.compile(r'_forest_all$')
GREEK = set('αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩℓ')


def up(c):
    return c.isupper() and c not in GREEK


def clean(n):
    return re.sub(r'^_private\.[^0]*\.0\.', '', n)


def noise(n, k):
    last = n.split('.')[-1]
    if re.search(r"[^\w'?!ℓ₀-₉]", last):
        return True  # notation, syntax and macro declarations
    if last.startswith(('term', 'hl_', 'command', 'tactic')):
        return True
    if last in ('noConfusionType', 'ctorElimType', 'mk') or re.match(r'(repr|decEq|default|match|proof)_\d', last):
        return True
    if re.search(r'\.(eq_\d+|eq_def|congr_eq_\d+)$', n):
        return True
    return False


rows = []
for path in sys.argv[1:]:
    rows += [l.rstrip('\n').split('\t') for l in open(path, encoding='utf-8')]
decls = {}
for r in rows:
    n, k, m = clean(r[0]), r[1], r[2]
    if m.split('.')[0] in ('Lantana', 'LantanaTest') and not noise(n, k):
        decls[n] = dict(k=k, m=m, rs=r[5], ln=r[6])
# lowerCamelCase spellings of every declaration name (a theorem may be named after one)
SPELL = set()
for r in rows:
    last = clean(r[0]).split('.')[-1]
    SPELL.add(last[:1].lower() + last[1:])

bad = []


def flag(n, d, msg):
    bad.append(f"{d['m'].replace('.', '/')}.lean:{d['ln']}: {n}: {msg}")


for n, d in sorted(decls.items()):
    k, rs = d['k'], d['rs']
    parts = n.split('.')
    last = parts[-1].rstrip("'")
    if '__' in last:
        flag(n, d, 'double underscore')
    if k == 'theorem':
        toks = [t for t in last.split('_') if t]
        if any(up(t[0]) and t not in ('True', 'False') for t in toks):
            flag(n, d, 'theorem name with an UpperCamelCase word (write it in lowerCamelCase)')
        if '_' not in last and re.search(r'[a-z0-9][A-Z]', last):
            # a lowerCamelCase theorem name must be the name of a definition (its conclusion) or the
            # field of the class it belongs to
            owner = parts[-2] if len(parts) > 1 else ''
            if last not in SPELL and last.lower() != owner.lower():
                flag(n, d, 'theorem named in lowerCamelCase (theorems are snake_case)')
        if not VOCAB_OK.search(last):
            for t in toks:
                if t in VOCAB:
                    flag(n, d, f'word `{t}` (write `{VOCAB[t]}`)')
        if re.fullmatch(r'N[a-z0-9]*_.*', last):
            flag(n, d, 'namespace constant `N…` (write `fooN`)')
    elif k in ('def', 'abbrev', 'opaque'):
        if last.startswith('inst') or last in ALLOW['attribute']:
            continue
        if '_' in last.strip('_'):
            flag(n, d, 'definition with an underscore (definitions are lowerCamelCase)')
        if rs in ('Prop', 'Type') and not up(last[0]) and last not in ALLOW['order']:
            flag(n, d, f'{rs}-valued definition in lowerCamelCase (write it in UpperCamelCase)')
        if rs == '-' and up(last[0]) and not ALLOW['functor'].search(last):
            flag(n, d, 'term-valued definition in UpperCamelCase (write it in lowerCamelCase)')
        if re.fullmatch(r'N[a-z0-9]*', last):
            flag(n, d, 'namespace constant `N…` (write `fooN`)')
    elif k in ('class', 'structure', 'inductive'):
        if not up(last[0]) or '_' in last:
            flag(n, d, 'type not in UpperCamelCase')
    elif k == 'ctor':
        if up(last[0]) or '_' in last.rstrip('_'):
            flag(n, d, 'constructor not in lowerCamelCase')
    elif k == 'instance':
        if up(last[0]):
            flag(n, d, 'instance name starting with an upper-case letter')

for b in bad:
    print(b)
print(f'{len(bad)} naming violation(s) in {len(decls)} declarations', file=sys.stderr)
sys.exit(1 if bad else 0)
