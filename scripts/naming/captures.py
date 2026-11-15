#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""Usages that a rename would capture, from the `.ilean` data of the tree *before* the rename.

    python3 scripts/naming/captures.py RENAMES.tsv ILEAN_ROOT ORIG_SRC_REV [--fix]

A usage written `x` inside the namespace `N` (the namespace of the declaration that contains it)
resolves to the innermost `S.x` that exists, `S` ranging over `N` and its prefixes.  If a renamed
declaration becomes `S.x` for an `S` inner to the one the usage resolved through, the usage
would now resolve to it.  With `--fix`, each captured usage in the current sources is replaced by
its target's name relative to the root (shortened to `BI.x` for Iris-Lean's BI lemmas).  The
usages are located in the current sources at the line they had before (`rename.py` does not move
lines): run `--fix` right after `rename.py`, before any edit that adds or removes lines.
"""
import collections, glob, json, re, subprocess, sys

sys.path.insert(0, 'scripts/naming')
RM_PATH, ILEAN_ROOT, REV = sys.argv[1], sys.argv[2], sys.argv[3]
FIX = '--fix' in sys.argv


def clean(n):
    return re.sub(r'^_private\.[^0]*\.0\.', '', n)


rm = {}
for l in open(RM_PATH):
    p = l.rstrip('\n').split('\t')
    rm[p[0]] = p[1]


def new_name(n):
    if n in rm:
        return rm[n]
    cs = n.split('.')
    for k in range(len(cs) - 1, 0, -1):
        p = '.'.join(cs[:k])
        if p in rm:
            return rm[p] + '.' + '.'.join(cs[k:])
    return n


ileans = glob.glob(ILEAN_ROOT + '/Lantana/**/*.ilean', recursive=True) + \
    glob.glob(ILEAN_ROOT + '/LantanaTest/**/*.ilean', recursive=True)
OLD = set()
data = []
for f in ileans:
    d = json.load(open(f))
    data.append(d)
    for n in d.get('decls', {}):
        OLD.add(clean(n))
NEW = {new_name(n) for n in OLD}
OLDSET = OLD


def resolve(ns_chain, text, names):
    for S in ns_chain:
        cand = (S + '.' + text) if S else text
        if cand in names:
            return cand
    return None


def chain(decl):
    cs = decl.split('.')[:-1]
    return ['.'.join(cs[:k]) for k in range(len(cs), 0, -1)]


src_cache = {}


def orig_lines(path):
    if path not in src_cache:
        src_cache[path] = subprocess.run(['git', 'show', f'{REV}:{path}'], capture_output=True,
                                         text=True).stdout.split('\n')
    return src_cache[path]


def u16(line, u):
    i = acc = 0
    while i < len(line) and acc < u:
        acc += 2 if ord(line[i]) > 0xFFFF else 1
        i += 1
    return i


hits = []
STALE = set()
for d in data:
    path = d['module'].replace('.', '/') + '.lean'
    lines = orig_lines(path)
    for key, v in d.get('references', {}).items():
        c = json.loads(key).get('c')
        if not c:
            continue
        C = clean(c['n'])
        for u in v.get('usages', []):
            if u[0] != u[2] or len(u) < 5:
                continue
            if u[0] >= len(lines):
                STALE.add(path)
                continue
            line = lines[u[0]]
            s, e = u16(line, u[1]), u16(line, u[3])
            T = line[s:e]
            if not T or T.startswith(('@', '_root_')) or (s > 0 and line[s - 1] == '.'):
                continue
            if line[:s].strip() == '' and re.match(r'[^:]*:=', line[e:]):
                continue  # a field of a structure instance (`ne k P := …`): not resolved by name
            E = clean(u[4])
            Cn = new_name(C)
            tc = T.split('.')
            # the text written after the rename: unchanged unless C itself was renamed
            if Cn != C:
                continue
            ch = chain(new_name(E))
            r = resolve(ch, T, NEW)
            if r is not None and r != Cn:
                # only captures by renamed declarations matter
                if r not in OLDSET or new_name(r) != r:
                    hits.append((path, u[0], s, e, T, C, r))
print(f'{len(hits)} captured usages; .ilean not matching the sources: {sorted(STALE)}')
for h in hits:
    print(f'  {h[0]}:{h[1]+1}: `{h[4]}` meant {h[5]}, would resolve to {h[6]}')
if FIX:
    byfile = collections.defaultdict(list)
    for h in hits:
        byfile[h[0]].append(h)
    for path, hs in byfile.items():
        cur = open(path, encoding='utf-8').read().split('\n')
        for (p, l, s, e, T, C, r) in sorted(hs, key=lambda h: (h[1], -h[2])):
            q = C[len('Iris.'):] if C.startswith('Iris.BI.') else C
            o = orig_lines(path)[l]
            # locate the same occurrence in the current line: the k-th occurrence of T as a word
            k = len(re.findall(r'(?<![\w.])' + re.escape(T) + r'(?![\w\'?!])', o[:s]))
            ms = list(re.finditer(r'(?<![\w.])' + re.escape(T) + r'(?![\w\'?!])', cur[l]))
            if k < len(ms):
                m = ms[k]
                cur[l] = cur[l][:m.start()] + q + cur[l][m.end():]
            else:
                print('  could not place', p, l + 1, T)
        open(path, 'w', encoding='utf-8').write('\n'.join(cur))
