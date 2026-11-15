#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""Rename declarations across the library, driven by the build's `.ilean` reference data.

Usage (from the package root, on a tree whose build is current):

    python3 scripts/naming/rename.py RENAMES.tsv [NAMESPACES.tsv] [--dry-run]

RENAMES.tsv: `old full name <TAB> new full name` per line (further columns ignored).
NAMESPACES.tsv: `old namespace <TAB> new namespace`, for namespaces that move without a
declaration of their own (e.g. `Lantana.Internal → Lantana.lwp.Internal`).

A constant is renamed if it is in RENAMES, or if a prefix of it is (its children follow it:
`foo.eq_1`, the declarations in the namespace `foo`).  Rewritten:

1. every resolved usage recorded in `.lake/build/lib/lean/{Lantana,LantanaTest}/**.ilean`, and
   every declaration name (the `decls` selection ranges).  The written form keeps the way the
   name was resolved: if `Lantana.Model.Obl.step` was written `Obl.step` (context
   `Lantana.Model`), the new text is the new name relative to that context after its own
   rename.  Generalized field notation (`h.foo`) only changes its last components.  A
   declaration that leaves its context is declared `_root_.<new name>`;
2. `namespace X` / `end X` and `open X …` commands (including explicit `open X (a b)` lists),
   tracking the namespace stack of each file;
3. backticked mentions inside comments (`` `Obl.step` ``) of `.lean` files, and inside the
   Markdown files given by `--docs FILE...` — only forms that name exactly one declaration.

Columns in `.ilean` are UTF-16 code units (LSP).  Every edit checks the text it replaces; a
mismatch (e.g. a range synthesized by a macro) is skipped and reported.  Identifiers inside
syntax quotations and name literals are not references: the build finds them.
"""
import collections, glob, json, os, re, sys

KEYWORDS = {'exists', 'forall', 'fun', 'have', 'show', 'from', 'at', 'by', 'do', 'then', 'else',
            'if', 'let', 'in', 'match', 'with', 'end', 'open', 'namespace', 'section', 'def',
            'theorem', 'example', 'instance', 'where', 'deriving', 'structure', 'class', 'mut'}


def comps(name):
    """Components of a (possibly «escaped») name."""
    out, cur, esc = [], '', False
    for ch in name:
        if esc:
            if ch == '»':
                esc = False
            else:
                cur += ch
        elif ch == '«':
            esc = True
        elif ch == '.':
            out.append(cur)
            cur = ''
        else:
            cur += ch
    out.append(cur)
    return out


IDCH = re.compile(r"[\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]")


def esc(c):
    return '«' + c + '»' if (c in KEYWORDS or not re.fullmatch(r"[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*", c)) else c


def esc_field(c):
    """A component written after a dot: keywords need no escaping there."""
    return c if re.fullmatch(r"[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*", c) else '«' + c + '»'


def text_of(cs, single_kw=True):
    if len(cs) == 1:
        return esc(cs[0])
    return '.'.join(cs[:1] + [esc(c) if not re.fullmatch(r"[^\W\d][\w'!?₀-₉ₐ-ₜᵢ-ᵪⱼ]*", c) else c
                              for c in cs[1:]])


def clean(n):
    return re.sub(r'^_private\.[^0]*\.0\.', '', n)


# ------------------------------------------------------------------------------------- the map
args = [a for a in sys.argv[1:] if not a.startswith('--')]
DRY = '--dry-run' in sys.argv
DOCS = []
if '--docs' in sys.argv:
    DOCS = sys.argv[sys.argv.index('--docs') + 1:]
    args = [a for a in args if a not in DOCS]
RMAP = {}
for line in open(args[0]):
    p = line.rstrip('\n').split('\t')
    if len(p) >= 2 and p[0] and not p[0].startswith('#'):
        RMAP[tuple(comps(p[0]))] = tuple(comps(p[1]))
NSMAP = {}
if len(args) > 1:
    for line in open(args[1]):
        p = line.rstrip('\n').split('\t')
        if len(p) >= 2:
            NSMAP[tuple(comps(p[0]))] = tuple(comps(p[1]))


def new_name(cs):
    """The new components of the constant/namespace `cs`, or None if unchanged."""
    cs = tuple(cs)
    if cs in RMAP:
        return RMAP[cs]
    for k in range(len(cs) - 1, 0, -1):
        pre = cs[:k]
        if pre in RMAP:
            return RMAP[pre] + cs[k:]
        if pre in NSMAP:
            return NSMAP[pre] + cs[k:]
    if cs in NSMAP:
        return NSMAP[cs]
    return None


def renamed(cs):
    n = new_name(cs)
    return n if n is not None else tuple(cs)


# ------------------------------------------------------------------------------------ the files
ROOT = os.getcwd()
ILEAN_ROOT = '.lake/build/lib/lean'
if '--ilean-root' in sys.argv:
    ILEAN_ROOT = sys.argv[sys.argv.index('--ilean-root') + 1]
    args = [a for a in args if a != ILEAN_ROOT]
ILEANS = glob.glob(ILEAN_ROOT + '/Lantana/**/*.ilean', recursive=True) + \
         glob.glob(ILEAN_ROOT + '/LantanaTest/**/*.ilean', recursive=True)
src_cache = {}


def src(path):
    if path not in src_cache:
        src_cache[path] = open(path, encoding='utf-8').read().split('\n')
    return src_cache[path]


def u16_to_idx(line, u):
    i = 0
    acc = 0
    while i < len(line) and acc < u:
        acc += 2 if ord(line[i]) > 0xFFFF else 1
        i += 1
    return i


edits = collections.defaultdict(dict)  # path -> {(l, s, e): (old_text, new_text, why)}
report = collections.Counter()
skipped = []


def add_edit(path, l, s, e, old, new, why):
    key = (l, s, e)
    cur = edits[path].get(key)
    if cur and cur[1] != new:
        skipped.append(f'{path}:{l+1}: conflicting edits {cur[1]!r} / {new!r}')
        return
    edits[path][key] = (old, new, why)


def rewrite_ident(T, old, new, is_decl, after_dot=False):
    """New text for the identifier text T that resolves to `old` (which becomes `new`).

    `after_dot`: T follows a `.` (generalized field notation `h.foo`, or `.foo` resolved in the
    expected type's namespace), so only its trailing components can change."""
    if after_dot:
        tc = comps(T)
        if len(new) < len(tc) or tuple(tc) != tuple(old[-len(tc):]):
            return None
        return text_of(list(new[-len(tc):])) if len(tc) > 1 else esc_field(new[-1])
    root = False
    if T.startswith('_root_.'):
        root, T = True, T[len('_root_.'):]
    at = ''
    if T.startswith('@'):
        at, T = '@', T[1:]
    tc = comps(T)
    k = 0
    while k < len(tc) and k < len(old) and tc[len(tc) - 1 - k] == old[len(old) - 1 - k]:
        k += 1
    if k == 0:
        return None
    if k < len(tc):
        # generalized field notation `h.foo`: only the trailing components can change
        if len(new) < k or new[:-k] == old[:-k] and new[-k:] == old[-k:]:
            return T
        head = T[:len(T) - len('.'.join(tc[len(tc) - k:]))]
        return at + head + text_of(list(new[-k:]))
    if root:
        return '_root_.' + at + text_of(list(new)) if not at else at + '_root_.' + text_of(list(new))
    ctx = old[:len(old) - k]
    ctx2 = renamed(ctx) if ctx else ()
    if new[:len(ctx2)] == ctx2 and len(new) > len(ctx2):
        rel = list(new[len(ctx2):])
        return at + text_of(rel)
    if is_decl:
        return '_root_.' + text_of(list(new))
    return at + text_of(list(new))


DECLARED = set()
for f in sorted(ILEANS):
    d = json.load(open(f))
    mod = d['module']
    path = mod.replace('.', '/') + '.lean'
    if not os.path.exists(path):
        continue
    lines = src(path)
    # declarations
    for name, r in d.get('decls', {}).items():
        old = tuple(comps(clean(name)))
        new = new_name(old)
        if new is None or len(r) < 8:
            continue
        l, c1, l2, c2 = r[4], r[5], r[6], r[7]
        if l != l2:
            continue
        s, e = u16_to_idx(lines[l], c1), u16_to_idx(lines[l], c2)
        T = lines[l][s:e]
        nt = rewrite_ident(T, old, new, True)
        if nt is None:
            report['decl text mismatch'] += 1
            skipped.append(f'{path}:{l+1}: declaration text {T!r} is not {".".join(old)}')
            continue
        DECLARED.add(old)
        if nt != T:
            add_edit(path, l, s, e, T, nt, 'decl')
    # usages
    for key, v in d.get('references', {}).items():
        c = json.loads(key).get('c')
        if not c:
            continue
        old = tuple(comps(clean(c['n'])))
        new = new_name(old)
        if new is None:
            continue
        for u in v.get('usages', []):
            l, c1, l2, c2 = u[0], u[1], u[2], u[3]
            if l != l2:
                report['multiline usage'] += 1
                continue
            s, e = u16_to_idx(lines[l], c1), u16_to_idx(lines[l], c2)
            T = lines[l][s:e]
            nt = rewrite_ident(T, old, new, False, after_dot=(s > 0 and lines[l][s - 1] == '.'))
            if nt is None:
                report['usage text mismatch'] += 1
                skipped.append(f'{path}:{l+1}: {T!r} is not {".".join(old)}')
                continue
            if nt != T:
                add_edit(path, l, s, e, T, nt, 'usage')

# ------------------------------------------------------------------ namespace / open commands
ALLNAMES = set()
for f in ILEANS:
    d = json.load(open(f))
    for name in d.get('decls', {}):
        ALLNAMES.add(tuple(comps(clean(name))))
    for key in d.get('references', {}):
        c = json.loads(key).get('c')
        if c:
            ALLNAMES.add(tuple(comps(clean(c['n']))))
NAMESPACES = set()
for n in ALLNAMES:
    for k in range(1, len(n)):
        NAMESPACES.add(n[:k])

ID = r"[^\s()\[\]{},:]+"


def resolve_ns(stack, A):
    a = tuple(comps(A))
    for k in range(len(stack), -1, -1):
        cand = tuple(stack[:k]) + a
        if cand in NAMESPACES or cand in ALLNAMES:
            return tuple(stack[:k]), cand
    return None, None


for path in sorted(set(glob.glob('Lantana/**/*.lean', recursive=True) + glob.glob('LantanaTest/**/*.lean', recursive=True))):
    lines = src(path)
    stack = []  # current namespace components
    frames = []  # (kind, ncomps, old_text, new_text)
    in_block_comment = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        # skip block comments (rough: comments starting a line)
        if in_block_comment or stripped.startswith('/-'):
            in_block_comment += line.count('/-') - line.count('-/')
            if in_block_comment < 0:
                in_block_comment = 0
            i += 1
            continue
        m = re.match(r'^(\s*)namespace\s+(' + ID + r')\s*(--.*)?$', line)
        if m:
            A = m.group(2)
            full = tuple(stack) + tuple(comps(A))
            nf = renamed(full)
            nt = A
            if nf != full:
                if nf[:len(stack)] == tuple(stack):
                    nt = text_of(list(nf[len(stack):]))
                    s = line.index(A, len(m.group(1)) + len('namespace'))
                    add_edit(path, i, s, s + len(A), A, nt, 'namespace')
                else:
                    skipped.append(f'{path}:{i+1}: namespace {A} → {".".join(nf)} leaves its context')
            frames.append(('ns', len(comps(A)), A, nt))
            stack.extend(comps(A))
            i += 1
            continue
        m = re.match(r'^(\s*)(?:@\[[^\]]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?section(?:\s+(' + ID + r'))?\s*(--.*)?$', line)
        if m:
            frames.append(('sec', 0, m.group(2) or '', m.group(2) or ''))
            i += 1
            continue
        if re.match(r'^\s*mutual\s*(--.*)?$', line):
            frames.append(('mutual', 0, '', ''))
            i += 1
            continue
        m = re.match(r'^(\s*)end(?:\s+(' + ID + r'))?\s*(--.*)?$', line)
        if m and frames:
            kind, n, A, nt = frames.pop()
            if kind == 'ns':
                del stack[len(stack) - n:]
                if m.group(2) and nt != A and m.group(2) == A:
                    s = line.index(A, len(m.group(1)) + 3)
                    add_edit(path, i, s, s + len(A), A, nt, 'end')
            i += 1
            continue
        m = re.match(r'^(\s*)(open|export)\s+(.*)$', line)
        if m:
            # gather a multi-line explicit list
            body_lines = [i]
            text = m.group(3)
            depth = text.count('(') - text.count(')')
            j = i
            while depth > 0 and j + 1 < len(lines):
                j += 1
                body_lines.append(j)
                depth += lines[j].count('(') - lines[j].count(')')
            # tokens: namespaces outside parentheses, items inside
            cur_ns = None
            cur_new = None
            for ln in body_lines:
                L0 = lines[ln].split('--')[0]
                start = (len(m.group(1)) + len(m.group(2))) if ln == i else 0
                if ln == i:
                    inside = None
                for tok in re.finditer(r'\(|\)|' + ID, L0[start:]):
                    t = tok.group(0)
                    s = start + tok.start()
                    if t == '(':
                        inside = True
                        continue
                    if t == ')':
                        inside = False
                        continue
                    if t in ('scoped', 'hiding', 'renaming', 'in', '→', '=>'):
                        if t == 'in':
                            break
                        continue
                    if inside is None and ln != i:
                        inside = True  # continuation lines of an explicit list
                    if inside:
                        if cur_ns is None:
                            continue
                        item = cur_ns + tuple(comps(t))
                        ni = new_name(item)
                        if ni is not None:
                            base = renamed(cur_ns)
                            if ni[:len(base)] == base:
                                add_edit(path, ln, s, s + len(t), t, text_of(list(ni[len(base):])), 'open item')
                            else:
                                skipped.append(f'{path}:{ln+1}: open item {t} moved to {".".join(ni)}')
                    else:
                        ctx, full = resolve_ns(stack, t)
                        if full is None:
                            cur_ns = None
                            continue
                        cur_ns = full
                        nf = renamed(full)
                        if nf != full:
                            if nf[:len(ctx)] == ctx:
                                add_edit(path, ln, s, s + len(t), t, text_of(list(nf[len(ctx):])), 'open')
                            else:
                                add_edit(path, ln, s, s + len(t), t, text_of(list(nf)), 'open')
            i = body_lines[-1] + 1
            continue
        i += 1

# ---------------------------------------------------------------------- mentions in comments
SUFFIX_OWNERS = collections.defaultdict(set)
for n in ALLNAMES:
    if n and n[0] in ('Lantana', 'LantanaTest'):
        for k in range(1, len(n)):
            SUFFIX_OWNERS[n[k:]].add(n)
FORMS = {}
for old, new in RMAP.items():
    if not old or old[0] not in ('Lantana', 'LantanaTest'):
        continue
    for k in range(1, len(old)):
        suf = old[k:]
        owners = SUFFIX_OWNERS.get(suf, set())
        if owners and owners != {old}:
            continue
        if len(suf) == 1 and len(suf[0]) < 3:
            continue  # `X`, `Nu`: in comments, more likely a variable than this declaration
        ctx = old[:k]
        ctx2 = renamed(ctx)
        nn = new[len(ctx2):] if new[:len(ctx2)] == ctx2 and len(new) > len(ctx2) else (new[1:] if new[0] == 'Lantana' else new)
        FORMS['.'.join(suf)] = '.'.join(nn)

TOKEN = re.compile(r"(?<![\w.'!?])([A-Za-z_][\w'!?.]*[\w'!?]|[A-Za-z_])(?![\w'!?])")


def rewrite_backticks(text):
    def span(m):
        inner = m.group(1)
        return '`' + TOKEN.sub(lambda t: FORMS.get(t.group(1), t.group(1)), inner) + '`'
    return re.sub(r'`([^`\n]+)`', span, text)


def comment_spans(full):
    """(start, end) of the comments of a Lean source."""
    out, i, n = [], 0, len(full)
    while i < n:
        if full.startswith('--', i):
            j = full.find('\n', i)
            j = n if j < 0 else j
            out.append((i, j))
            i = j
        elif full.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if full.startswith('/-', j):
                    depth += 1
                    j += 2
                elif full.startswith('-/', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            out.append((i, j))
            i = j
        elif full[i] == '"':
            j = i + 1
            while j < n and full[j] != '"':
                j += 2 if full[j] == '\\' else 1
            i = j + 1
        else:
            i += 1
    return out


# ------------------------------------------------------------------------------- apply
changed_files = 0
for path in sorted(set(list(edits) + glob.glob('Lantana/**/*.lean', recursive=True) +
                       glob.glob('LantanaTest/**/*.lean', recursive=True))):
    lines = list(src(path))
    es = edits.get(path, {})
    by_line = collections.defaultdict(list)
    for (l, s, e), (old, new, why) in es.items():
        by_line[l].append((s, e, old, new, why))
        report[why] += 1
    for l, lst in by_line.items():
        lst.sort(reverse=True)
        line = lines[l]
        last = None
        for s, e, old, new, why in lst:
            if last is not None and e > last:
                skipped.append(f'{path}:{l+1}: overlapping edits')
                continue
            if line[s:e] != old:
                skipped.append(f'{path}:{l+1}: text changed under edit {old!r}')
                continue
            line = line[:s] + new + line[e:]
            last = s
        lines[l] = line
    full = '\n'.join(lines)
    # comments
    spans = comment_spans(full)
    if spans:
        parts, prev = [], 0
        for s, e in spans:
            parts.append(full[prev:s])
            seg = full[s:e]
            if 'lantana_alias' not in seg:
                seg2 = rewrite_backticks(seg)
                if seg2 != seg:
                    report['comment'] += 1
                seg = seg2
            parts.append(seg)
            prev = e
        parts.append(full[prev:])
        full = ''.join(parts)
    # `#lantana_ignore name "reason"`: the reason strings
    full2 = re.sub(r'(#lantana_ignore\s+\S+\s+)("(?:[^"\\]|\\.)*")',
                   lambda m: m.group(1) + rewrite_backticks(m.group(2)), full)
    full = full2
    orig = '\n'.join(src(path))
    if full != orig:
        changed_files += 1
        if not DRY:
            open(path, 'w', encoding='utf-8').write(full)
for path in DOCS:
    t = open(path, encoding='utf-8').read()
    t2 = rewrite_backticks(t)
    if t2 != t:
        changed_files += 1
        report['doc file'] += 1
        if not DRY:
            open(path, 'w', encoding='utf-8').write(t2)

print('files changed:', changed_files)
for k, v in sorted(report.items()):
    print(f'  {k}: {v}')
for old in sorted(set(RMAP) - DECLARED):
    skipped.append(f'no declaration site found for {".".join(old)}')
print('skipped / to check by hand:', len(skipped))
for s in skipped:
    print('  ' + s)
