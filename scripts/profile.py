#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Profile the elaboration of the library, module by module, and print a Markdown report: totals,
# time per layer, the critical path through the import graph, the slowest modules and the slowest
# declarations (docs/performance.md explains the method and the numbers).
#
# Each module of Lantana/ (and the root module Lantana) is elaborated alone with
# `lake env lean -Dtrace.profiler=true` against the built .olean files of its imports, so run
# `lake build` first; nothing is written to .lake/. Do not run it while a build runs in this tree.
#
# Usage: scripts/profile.py [--threads N] [--threshold MS] [--top N] [--json FILE] [--load FILE]
#   --threads    LEAN_NUM_THREADS for each module (default: $LEAN_NUM_THREADS, else 4)
#   --threshold  profiler threshold in ms: only commands and proofs above it are reported (200)
#   --top        rows of the module and declaration tables (15)
#   --json FILE  also save the raw measurements to FILE
#   --load FILE  report from measurements saved with --json instead of profiling
import argparse, collections, json, os, re, subprocess, sys, time

ROOT = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..'))
# The layers of scripts/check-imports.sh; Lantana.L and Lantana.L.… belong to layer L.
LAYERS = ['Std', 'Init', 'Prelude', 'Algebra', 'BaseLogic', 'ProgramLogic', 'Trace', 'HeapLang',
          'Examples']
ENTRY = re.compile(r'^\[([A-Za-z.]+)\] \[([0-9.]+)\] \S+ ?(.*)$')
DECL = re.compile(r'^\s*(?:(?:private|protected|noncomputable|partial|unsafe|public|meta)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom|'
                  r'macro_rules|macro|syntax|notation|elab_rules|elab|example)\b(.*)$')


def modules():
    mods = ['Lantana.lean']
    for d, _, fs in os.walk(os.path.join(ROOT, 'Lantana')):
        mods += [os.path.relpath(os.path.join(d, f), ROOT) for f in fs if f.endswith('.lean')]
    return sorted(mods)


DEFVAL = re.compile(r'^\s*\[Elab\.definition\.value\] \[[0-9.]+\] \S+ (.*)$')
MACRO = re.compile(r'_macroRules_(.+)_\d+»?$')


def command_name(body):
    """The declaration a profiled command elaborates: its first declaration line, or else (a
    command the profiler cannot print, such as `macro_rules`) its first elaborated definition."""
    for l in body:
        m = DECL.match(l)
        if m:
            return (m.group(1) + ' ' + m.group(2).strip()).strip()[:90]
    for l in body:
        m = DEFVAL.match(l)
        if m:
            mm = MACRO.search(m.group(1))
            return f'macro_rules for {mm.group(1)}' if mm else m.group(1)[:90]
    first = body[0].strip() if body else ''
    return '(a command the profiler cannot print)' if first.startswith('failed to pretty print') \
        else (first or '?')[:90]


def profile_module(rel, threads, threshold):
    env = dict(os.environ, LEAN_NUM_THREADS=str(threads))
    t0 = time.time()
    p = subprocess.run(['lake', 'env', 'lean', '-Dtrace.profiler=true',
                        f'-Dtrace.profiler.threshold={threshold}', rel],
                       cwd=ROOT, env=env, capture_output=True, text=True)
    wall = time.time() - t0
    lines = (p.stdout + p.stderr).splitlines()
    entries, i = [], 0
    while i < len(lines):
        m = ENTRY.match(lines[i])
        if not m:
            i += 1
            continue
        j = i + 1
        while j < len(lines) and not ENTRY.match(lines[j]):
            j += 1
        cls, t, rest = m.group(1), float(m.group(2)), m.group(3)
        if cls == 'Elab.command':
            body = [rest] + lines[i + 1:j]
            prev = entries[-1] if entries else None
            # A command that elaborates commands (a macro, `macro_rules`) is reported once per
            # nesting level, as consecutive entries with almost the same time: keep one.
            if prev and prev['kind'] == 'command' and abs(prev['time'] - t) <= max(0.002, 0.005 * t):
                prev['time'] = max(prev['time'], t)
                prev['body'] += body
                prev['decl'] = command_name(prev['body'])
            else:
                entries.append({'kind': 'command', 'time': t, 'body': body,
                                'decl': command_name(body)})
        elif cls == 'Elab.async' and rest.startswith('elaborating proof of '):
            entries.append({'kind': 'proof', 'time': t,
                            'decl': rest[len('elaborating proof of '):].strip()})
        i = j
    for e in entries:
        e.pop('body', None)
    imports = []
    with open(os.path.join(ROOT, rel), encoding='utf-8') as fh:
        for l in fh:
            m = re.match(r'^(?:public\s+)?(?:meta\s+)?import\s+(Lantana[\w.]*)', l)
            if m:
                imports.append(m.group(1))
    return {'wall': wall, 'rc': p.returncode, 'entries': entries, 'imports': imports,
            'errors': [l for l in lines if ': error' in l][:5]}


def modname(rel):
    return rel[:-len('.lean')].replace('/', '.')


def layer(mod):
    parts = mod.split('.')
    if len(parts) == 1:
        return 'root'
    return 'Std, Init' if parts[1] in ('Std', 'Init') else parts[1]


def report(res, top):
    out = []
    w = {modname(k): v['wall'] for k, v in res.items()}
    failed = [k for k, v in res.items() if v['rc'] != 0]
    tot = sum(w.values())
    out.append('## Summary\n')
    if failed:
        out.append(f'**{len(failed)} modules failed to elaborate** (build first): '
                   + ', '.join(failed) + '\n')
    out.append(f'- {len(w)} modules; sum of per-module wall time {tot:.1f} s, mean {tot / len(w):.2f} s;'
               f' the fastest module takes {min(w.values()):.2f} s (the cost of loading its imports).')
    cmds = [(e['time'], e['kind'], modname(k), e['decl'])
            for k, v in res.items() for e in v['entries']]
    cmds.sort(reverse=True)
    ex = sum(t for t, _, m, _ in cmds if layer(m) == 'Examples')
    n1, n05 = (sum(1 for c in cmds if c[0] >= lim) for lim in (1.0, 0.5))
    out.append(f'- {n1} commands or proofs take 1 s or more, {n05} take 0.5 s or more.')
    out.append(f'- Above the threshold: {len(cmds)} commands and proofs, {sum(c[0] for c in cmds):.1f} s'
               f' in all, {ex:.1f} s of it in Examples.\n')
    out.append('## Per layer\n')
    out.append('| Layer | Modules | Sum (s) | Slowest module (s) |\n|---|--:|--:|--:|')
    by = collections.defaultdict(list)
    for m, t in w.items():
        by[layer(m)].append(t)
    for lay in ['Std, Init'] + LAYERS[2:] + ['root']:
        if lay in by:
            ts = by[lay]
            out.append(f'| {lay} | {len(ts)} | {sum(ts):.1f} | {max(ts):.2f} |')
    imps = {modname(k): [i for i in v['imports'] if i in w] for k, v in res.items()}
    memo = {}

    def cp(m):
        if m not in memo:
            best = max((cp(i) for i in imps[m]), key=lambda x: x[0], default=(0.0, []))
            memo[m] = (best[0] + w[m], best[1] + [m])
        return memo[m]
    length, path = max((cp(m) for m in w), key=lambda x: x[0])
    out.append(f'\n## Critical path\n\n{length:.1f} s over {len(path)} modules (the longest chain of '
               'imports, weighted by per-module wall time):\n')
    out.append('| Module | Wall (s) |\n|---|--:|')
    out += [f'| `{m}` | {w[m]:.2f} |' for m in path]
    out.append(f'\n## Slowest modules\n\n| Module | Wall (s) |\n|---|--:|')
    out += [f'| `{m}` | {t:.2f} |' for m, t in sorted(w.items(), key=lambda x: -x[1])[:top]]
    out.append('\n## Slowest declarations\n\n"command" is the elaboration of the declaration;'
               ' "proof" is a proof elaborated asynchronously (not included in its command).\n')
    out.append('| Time (s) | Kind | Declaration | Module |\n|--:|---|---|---|')
    out += [f'| {t:.2f} | {k} | `{d}` | `{m}` |' for t, k, m, d in cmds[:top]]
    return '\n'.join(out) + '\n'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--threads', type=int, default=int(os.environ.get('LEAN_NUM_THREADS', 4)))
    ap.add_argument('--threshold', type=int, default=200)
    ap.add_argument('--top', type=int, default=15)
    ap.add_argument('--json')
    ap.add_argument('--load')
    a = ap.parse_args()
    if a.load:
        res = json.load(open(a.load))
    else:
        res = {}
        for rel in modules():
            res[rel] = profile_module(rel, a.threads, a.threshold)
            print(f'{res[rel]["wall"]:7.2f} s  {rel}', file=sys.stderr, flush=True)
        if a.json:
            json.dump(res, open(a.json, 'w'), indent=1)
    sys.stdout.write(report(res, a.top))


if __name__ == '__main__':
    main()
