#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""The naming lint of `docs/naming.md`, over a declaration dump of `scripts/naming/Dump.lean`.

    python3 scripts/naming/lint.py DUMP.tsv [DUMP.tsv ...]

Checks the Lantana and LantanaTest declarations of the dumps (Iris-Lean's are skipped) and
prints one line per violation; exit code 1 if there is any.  `scripts/naming/lint.sh` makes the
dumps and runs it.  Accepted exceptions are listed in ALLOW and SAME_OK below, each with its
reason.
"""
import re, sys

ALLOW = {
    # Iris-Lean's functor and functor-bundle names are UpperCamelCase (`AuthURF`, `GFunctor`).
    'functor': re.compile(r'(F|RF|URF|GF|OF)$'),
    # An order relation implementing `LE` is `le`, as the class's field
    # (`TrSpec.le`, `Model.Obligations.le`; docs/naming.md, §2).
    'order': {'le', 'lt'},
    # Attribute names follow Lean's attributes (`simp`, Iris-Lean's `rocq_alias`).
    'attribute': {'lantana_alias'},
}
# Words that the convention replaces in the names of theorems and instances, and as the name
# of a definition (docs/naming.md, §1): word -> replacement.
VOCAB = {'ex': 'exists', 'exist': 'exists', 'all': 'forall', 'mon': 'mono', 'idemp': 'idem',
         'included': 'inc', 'impl': 'imp', 'l': 'left', 'r': 'right', 'upd': 'update',
         'subseteq': 'subset', 'mult': 'mul', 'expn': 'pow'}
# `all` meaning "for all the roots" (not ∀) in these lemma families.
VOCAB_OK = re.compile(r'_forest_all$')
# Abbreviations of a definition's name, which a name spells out (docs/naming.md, §1):
# word -> (replacement, module prefix where it is checked; None for everywhere).
ABBREV = {'sf': ('strongFair', None), 'ndf': ('noDischarge', None), 'nd': ('noDischarge', None),
          'lef': ('stayOrStep', None), 'ndLe': ('noDischargeLe', None),
          'obls': ('obligations', None), 'wits': ('witnesses', None),
          # elsewhere `wf` is "well-formed" (`Model.oforest_wf`)
          'wf': ('weakFair', 'Lantana.Temporal.Fairness')}
GREEK = set('αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩℓ')
DEFS = ('def', 'abbrev', 'opaque')
TYPES = ('class', 'structure', 'inductive')


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
        decls[n] = dict(k=k, m=m, rs=r[5], ln=r[6], priv=r[3], h=r[7] if len(r) > 7 else '')
# lowerCamelCase spellings of every declaration name (a theorem may be named after one)
SPELL = set()
for r in rows:
    last = clean(r[0]).split('.')[-1]
    SPELL.add(last[:1].lower() + last[1:])
# The definitions `Foo.bar` of an assertion family, by their flat spelling `fooBar`.
FLAT = {}
for n, d in decls.items():
    parts = n.split('.')
    if d['k'] in DEFS and len(parts) >= 2 and up(parts[-2][0]) and parts[-1][:1].islower():
        flat = parts[-2][:1].lower() + parts[-2][1:] + parts[-1][:1].upper() + parts[-1][1:]
        FLAT.setdefault(flat, '.'.join(parts[-2:]))
DEF_NAMES = {n for n, d in decls.items() if d['k'] in DEFS}
# The words of the library with their casing: its namespaces and types (`OWit`, `TrProp`).
WORDS = {}
for n, d in decls.items():
    parts = n.split('.')
    for c in parts[:-1] + (parts[-1:] if d['k'] in TYPES else []):
        if len(c) >= 4 and up(c[0]):
            WORDS.setdefault(c.lower(), set()).add(c)


def camel(c):
    """The camel-case words of a name component (`unexpBinOp` -> unexp, Bin, Op)."""
    return re.findall(r'[A-Z]+(?![a-z])|[A-Z]?[a-z0-9]+|[A-Z]', c)


# Two words that the namespaces, types and constructors write apart (`BinOp`, `PointsTo`).
APART = {}
for n, d in decls.items():
    parts = n.split('.')
    for c in parts[:-1] + (parts[-1:] if d['k'] in TYPES or d['k'] == 'ctor' else []):
        ws = camel(c)
        for a, b in zip(ws, ws[1:]):
            if len(a) >= 2 and len(b) >= 2 and a.isalpha() and b.isalpha():
                APART.setdefault((a + b).lower(), a + b)
# The first words of the members of each namespace (`Lantana.Obl`: discharge, fuel, ...).
FAMILY = {}
for n in decls:
    parts = n.split('.')
    FAMILY.setdefault('.'.join(parts[:-1]), set()).add(parts[-1].split('_')[0])

bad = []


def flag(n, d, msg):
    bad.append(f"{d['m'].replace('.', '/')}.lean:{d['ln']}: {n}: {msg}")


def in_scope(parts, name):
    """Whether `name` is a definition in the namespace `parts` or one of its prefixes."""
    return any('.'.join(parts[:i] + [name]) in DEF_NAMES for i in range(len(parts), -1, -1))


def check_words(n, d, parts, last):
    """The checks on the words of the name of a theorem or of a named instance."""
    toks = [t for t in last.split('_') if t]
    if not VOCAB_OK.search(last):
        for t in toks:
            if t in VOCAB:
                flag(n, d, f'word `{t}` (write `{VOCAB[t]}`)')
    for t in toks:
        if t in ABBREV and (ABBREV[t][1] is None or d['m'].startswith(ABBREV[t][1])):
            flag(n, d, f'abbreviation `{t}` (write `{ABBREV[t][0]}`)')
    head = toks[0] if toks else ''
    if head in FLAT and head != last and not in_scope(parts[:-1], head):
        flag(n, d, f'named after `{head}`, which is `{FLAT[head]}` (write `{FLAT[head]}_…`)')
    if len(toks) < 2 or not head[:1].islower() or in_scope(parts[:-1], head):
        return
    rest = last[len(head) + 1:]
    # `obl_discharge_leaf_roots` beside the family `Obl.discharge_*` of the same namespace
    fam = head[:1].upper() + head[1:]
    if toks[1] in FAMILY.get('.'.join(parts[:-1] + [fam]), ()):
        flag(n, d, f'beside the family `{fam}.{toks[1]}…` (write `{fam}.{rest}`)')
    # `Crash.crash_adequacy`: the namespace repeated, unless it is a class (a field named after it)
    owner = parts[-2] if len(parts) > 1 else ''
    if (d['k'] == 'theorem' and head == owner[:1].lower() + owner[1:]
            and decls.get('.'.join(parts[:-1]), {}).get('k') not in TYPES):
        flag(n, d, f'repeats its namespace `{owner}` (write `{rest}`)')


for n, d in sorted(decls.items()):
    k, rs = d['k'], d['rs']
    parts = n.split('.')
    last = parts[-1].rstrip("'")
    if '__' in last:
        flag(n, d, 'double underscore')
    if k in DEFS or k in TYPES or k in ('theorem', 'instance', 'ctor'):
        for w in camel(last):
            # two words written as one (`unexpBinop`, of `BinOp`)
            if len(w) >= 4 and w.lower() in APART and not last.startswith('inst'):
                sp = APART[w.lower()]
                sp = (sp[:1].upper() if up(w[0]) else sp[:1].lower()) + sp[1:]
                flag(n, d, f'`{w}` is written `{sp}` elsewhere')
            # an abbreviation inside a camel-case name (`workerObls`)
            if (k in DEFS or k in TYPES) and w.lower() in ABBREV and ABBREV[w.lower()][1] is None:
                flag(n, d, f'abbreviation `{w}` (write `{ABBREV[w.lower()][0]}`)')
    # a word cased differently from the namespace or type it comes from (`OwitRel`, of `OWit`)
    if up(last[0]) and (k in DEFS or k in TYPES):
        for w, cased in WORDS.items():
            if last.lower().startswith(w) and not any(last.startswith(c) for c in cased):
                flag(n, d, f'`{last[:len(w)]}` is cased `{sorted(cased)[0]}` elsewhere')
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
        check_words(n, d, parts, last)
        if re.fullmatch(r'N[a-z0-9]*_.*', last):
            flag(n, d, 'namespace constant `N…` (write `fooN`)')
    elif k in DEFS:
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
        if len(last) > 1 and last in VOCAB:
            flag(n, d, f'definition named `{last}` (write `{VOCAB[last]}`)')
    elif k in TYPES:
        if not up(last[0]) or '_' in last:
            flag(n, d, 'type not in UpperCamelCase')
    elif k == 'ctor':
        if up(last[0]) or '_' in last.rstrip('_'):
            flag(n, d, 'constructor not in lowerCamelCase')
    elif k == 'instance':
        if up(last[0]):
            flag(n, d, 'instance name starting with an upper-case letter')
        if not last.startswith('inst'):
            check_words(n, d, parts, last)

# A namespace that mirrors one of an enclosing namespace (`HeapLang.Obl` beside `Obl`): inside
# the enclosing namespace, the copy shadows the original (docs/naming.md, §1).
NSPACES = {'.'.join(n.split('.')[:i]) for n in decls for i in range(1, len(n.split('.')))}
for n, d in sorted(decls.items()):
    p = n.split('.')[:-1]
    for j in range(1, len(p) - 1):
        orig = '.'.join(p[:j] + [p[-1]])
        if orig in NSPACES:
            flag(n, d, f'in `{".".join(p)}`, which mirrors `{orig}` (put it in `{orig}`)')
            break

# Two theorems of the library with the same statement: one fact under two names.  The
# restatements kept on purpose, with their reasons:
SAME_OK = [
    # `SatPred.sat_*` are the class fields with the predicate explicit, for `S.sat_later h`.
    {'SatLater.later', 'SatPred.sat_later'}, {'SatBUpd.bupd', 'SatPred.sat_bupd'},
    {'SatExists.exists', 'SatPred.sat_exists'},
    # the same guarantee, proved by hand and inferred
    {'GuaranteeInfer.example_iprop', 'GuaranteeInfer.example_iprop_inferred'},
    # a client over the stable flag states the safety of the same program as its base client
    {'Examples.FlagClient.safety_of', 'Examples.FlagStableClient.flagClient_safety_of'},
    {'Examples.FlagClient.safety_adequacy', 'Examples.FlagStableClient.flagClient_safety_adequacy'},
    {'Examples.HandoffClient.safety_adequacy',
     'Examples.HandoffFlagStableClient.handoffClient_safety_adequacy'},
    {'Examples.TaskQueueClient.safety_adequacy',
     'Examples.TaskQueueFlagStableClient.taskQueueClient_safety_adequacy'},
]
same = {}
for n, d in decls.items():
    if d['k'] == 'theorem' and d['h'] and not d['priv'] and d['m'].startswith('Lantana.'):
        same.setdefault(d['h'], []).append(n)
for ns in same.values():
    short = {x.removeprefix('Lantana.') for x in ns}
    if len(ns) > 1 and not any(short <= ok for ok in SAME_OK):
        for n in sorted(ns):
            others = ', '.join(sorted(x for x in short if x != n.removeprefix('Lantana.')))
            flag(n, decls[n], f'same statement as {others} (keep one name)')

for b in bad:
    print(b)
print(f'{len(bad)} naming violation(s) in {len(decls)} declarations', file=sys.stderr)
sys.exit(1 if bad else 0)
