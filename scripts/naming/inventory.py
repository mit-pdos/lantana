#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""Candidate rename inventory for Lantana (naming-convention revision, docs/naming.md).

Input : all.tsv from scripts/naming/Dump.lean (Lantana and Iris runs merged)
        (name, kind, module, private, aliases, result sort, line).
Output: inventory.tsv  (cat, status, old, new, kind, location, rocq, note), sorted by category,
        summary on stdout. docs/naming-inventory.tsv is a copy of it.

status: auto      = mechanical consequence of the convention, no judgement needed
        review    = proposed name needs a human look (semantics / wording)
        decision  = depends on an open decision (D1..D6 in docs/naming.md)
        optional  = alignment nicety, not a convention violation
Each declaration gets at most one row; when several rules apply they compose (cats joined by +).
"""
import collections, re, sys

ROWS = [l.rstrip('\n').split('\t') for l in open(sys.argv[1] if len(sys.argv) > 1 else 'all.tsv')]
GREEK = set('αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩℓ')


def clean(n):
    return re.sub(r'^_private\.[^0]*\.0\.', '', n)


def noise(n, k):
    l = n.split('.')[-1]
    if re.search(r"[^\w'?!ℓ₀-₉]", l):
        return True
    if l.startswith(('term', 'hl_', 'command', 'tactic', 'termHl')):
        return True
    if l in ('noConfusionType', 'ctorElimType', 'mk') or re.match(r'(repr|decEq|default)_\d', l):
        return True
    if '.match_' in n or re.search(r'\.(eq_\d+|eq_def|congr_eq_\d+)$', n):
        return True
    if k == 'instance' and l.startswith('inst'):
        return True  # auto-generated instance names follow the class/type names
    return False


decls = {}
for n, k, m, priv, al, rs, ln in ROWS:
    if not m.startswith('Lantana'):
        continue
    if noise(n, k):
        continue
    full = clean(n)
    decls[full] = dict(k=k, m=m, priv=bool(priv) or n.startswith('_private'), al=al, rs=rs, ln=ln)
ALL_NAMES = set(decls) | {clean(r[0]) for r in ROWS}

plan = {}  # old -> dict(new, cats, status, note)
RANK = {'auto': 0, 'optional': 1, 'review': 2, 'decision': 3}


def propose(old, new, cat, status, note=''):
    if old not in decls or new == old:
        return
    cur = plan.get(old)
    if cur is None:
        plan[old] = dict(new=new, cats=[cat], status=status, note=note)
    else:
        cur['new'] = new
        cur['cats'].append(cat)
        if RANK[status] > RANK[cur['status']]:
            cur['status'] = status
        if note:
            cur['note'] = (cur['note'] + '; ' + note).strip('; ')


def current(old):
    return plan[old]['new'] if old in plan else old


def split(full):
    p = full.split('.')
    return '.'.join(p[:-1]), p[-1]


def retok(last, f):
    """Apply f to the list of underscore tokens of `last` (trailing primes kept)."""
    m = re.match(r"^(.*?)('*)$", last)
    body, primes = m.group(1), m.group(2)
    toks = body.split('_')
    return '_'.join(f(toks)) + primes


def lc(s):
    return s[:1].lower() + s[1:]


def uc(s):
    return s[:1].upper() + s[1:]


L = 'Lantana.'

# ---------------------------------------------------------------- A. the lWP construction
A = {
    'lwpStep': 'lwp.step', 'lwpStep_mono': 'lwp.step_mono', 'lwpStep_ne': 'lwp.step_ne',
    'lwpPre': 'lwp.pre', 'lwpPre_mono': 'lwp.pre_mono', 'liftTerm': 'lwp.liftTerm',
    'Internal.Args': 'lwp.Internal.Args', "Internal.pre'": "lwp.Internal.pre'",
    "Internal.pre'_mono": "lwp.Internal.pre'_mono",
}
for o, n in A.items():
    propose(L + o, L + n, 'A-lwp', 'auto', 'Iris-Lean WeakestPre: wp.pre / TotalWeakestPre: twp.pre, twp.Internal.*')
for o, n in {'Internal.get': 'lwp.Internal.lfp', 'Internal.get_unfold': 'lwp.Internal.lfp_unfold',
             'Internal.get_ne': 'lwp.Internal.lfp_ne', 'Internal.get_ind_strong': 'lwp.Internal.lfp_ind_strong'}.items():
    propose(L + o, L + n, 'A-lwp', 'decision',
            'D1b: Iris-Lean TotalWeakestPre names this twp.Internal.get; lfp is the descriptive alternative')
for o, n in {'frame_lwp': 'frameLwp', 'isExcept0_lwp': 'isExcept0Lwp', 'elimModal_fupd_lwp': 'elimModalFupdLwp',
             'elimModal_bupd_lwp': 'elimModalBupdLwp', 'elimModal_mupd_lwp': 'elimModalMupdLwp',
             'elimModal_fupd_lwp_wrongMask': 'elimModalFupdLwp_wrongMask',
             'elimModal_fupd_lwp_atomic': 'elimModalFupdLwpAtomic', 'elimModal_mupd_lwp_atomic': 'elimModalMupdLwpAtomic',
             'elimModal_fupd_lwp_atomic_wrongMask': 'elimModalFupdLwpAtomic_wrongMask',
             'addModal_fupd_lwp': 'addModalFupdLwp', 'addModal_mupd_lwp': 'addModalMupdLwp'}.items():
    propose(L + o, L + n, 'Q-instance', 'optional', 'Iris-Lean WeakestPre instance names (frameWp, elimModalFupdWp, ...)')

# ---------------------------------------------------------------- E. Prop-valued defs -> UpperCamel
LE_RELS = {'TrProp.le', 'TrSpec.le', 'Model.Obls.le', 'Model.Obl.le', 'Model.Witness.le', 'Model.eventLe',
           'Model.Witness.ndLe'}
renamed_ns = {}  # old namespace -> new namespace (defs used with dot notation)
for full, d in list(decls.items()):
    if d['k'] not in ('def', 'abbrev', 'opaque') or d['rs'] != 'Prop':
        continue
    ns, last = split(full)
    if not last[0].islower():
        continue
    new = ns + '.' + uc(last)
    short = full.removeprefix(L)
    if short in LE_RELS:
        propose(full, new, 'E-PropDef', 'decision', 'D3: order relation; UpperCamel or an LE instance (keep le/≤)')
    elif full == 'Iris.Stuckness.maybeReducible':
        propose(full, new, 'E-PropDef', 'review',
                "same predicate as Iris-Lean's Stuckness.MaybeReducible (ProgramLogic/WeakestPre.lean:69) up to currying; adopt its signature")
    else:
        propose(full, new, 'E-PropDef', 'auto', 'Mathlib/Iris-Lean: Prop-valued definitions are UpperCamelCase')
    renamed_ns[full] = new
# Iris-namespace defs from Lantana
for full in ('Iris.Stuckness.maybeReducible', 'Iris.Stuckness.pureSafe'):
    if full in decls:
        propose(full, 'Iris.Stuckness.' + uc(full.split('.')[-1]), 'E-PropDef', 'review',
                "Lantana declaration in Iris's namespace; Iris-Lean has Stuckness.MaybeReducible (not imported)")
        renamed_ns[full] = 'Iris.Stuckness.' + uc(full.split('.')[-1])

# ---------------------------------------------------------------- F. IProp-valued UpperCamel -> lowerCamel
F = {'ALC': 'alc', 'ALCb': 'alcIf', 'Guar': 'guar'}
for o, n in F.items():
    propose(L + o, L + n, 'F-IPropDef', 'auto', 'IProp-valued: lowerCamelCase (cf. Iris-Lean laterIf, ownE, lc)')

# ---------------------------------------------------------------- G. TrProp-valued UpperCamel -> lowerCamel (decision D4)
G = {'IsBehavior': 'isBehavior', 'StepOfInfOften': 'stepOfInfOften', 'Schedule': 'schedule',
     'SchedCounters': 'schedCounters', 'Fairness.Action.SF': 'Fairness.Action.strongFair',
     'Fairness.Action.WF': 'Fairness.Action.weakFair', 'Fairness.Action.Convex': 'Fairness.Action.convex',
     'Fairness.Action.Persists': 'Fairness.Action.persists', 'Fairness.Sched.SF': 'Fairness.Sched.strongFair',
     'Fairness.AttemptGrant.Fair': 'Fairness.AttemptGrant.fair',
     'Fairness.AttemptGrant.IsCounter': 'Fairness.AttemptGrant.isCounter',
     'Fairness.AttemptGrant.Certain': 'Fairness.AttemptGrant.certain',
     'Fairness.FairnessAssumption.IsCounter': 'Fairness.FairnessAssumption.isCounter',
     'Fairness.FairnessAssumption.Certain': 'Fairness.FairnessAssumption.certain'}
for o, n in G.items():
    propose(L + o, L + n, 'G-TrPropDef', 'decision', 'D4: TrProp C = Trace C → Prop treated as an assertion type (like IProp, Set)')
for full in decls:  # TrProp.along : Prop
    pass

# ---------------------------------------------------------------- K. type names
for o, n in {'invHeapGS': 'InvHeapGS', 'invHeapPreS': 'InvHeapGpreS', 'MonoListGP': 'MonoListPG'}.items():
    propose(L + o, L + n, 'K-Type', 'auto', 'UpperCamelCase classes; Lantana pre-classes are XGpreS, single-inG bundles XG (GhostMapPG)')

# ---------------------------------------------------------------- I. defs with underscores -> lowerCamel
I = {'MonoListP.lb_own': 'MonoListP.lbOwn', 'MonoListP.auth_own': 'MonoListP.authOwn',
     'MonoListP.idx_own': 'MonoListP.idxOwn', 'own_inv': 'ownInv', 'uPred_fupd': 'uPredFUpd',
     'Examples.ghostMapP_auth': 'Examples.ghostMapPAuth', 'Examples.ghostMapP_elem': 'Examples.ghostMapPElem'}
for o, n in I.items():
    propose(L + o, L + n, 'I-DefUnderscore', 'auto', 'definitions are lowerCamelCase (Iris-Lean style.md; Iris-Lean Instances still has uPred_fupd, ghost_map_elem)')
# theorems that spell those defs with underscores
I_TOK = [('ghostMapP_elem', 'ghostMapPElem'), ('ghostMapP_auth', 'ghostMapPAuth'), ('lb_own', 'lbOwn'),
         ('auth_own', 'authOwn'), ('idx_own', 'idxOwn')]
for full, d in decls.items():
    if d['k'] not in ('theorem', 'instance'):
        continue
    ns, last = split(current(full))
    nl = last
    if 'MonoListP' in full or 'ghostMapP' in last:
        for a, b in I_TOK:
            nl = re.sub(r'(^|_)' + a + r'(?=_|$|\')', lambda m: m.group(1) + b, nl)
    if nl != last:
        propose(full, ns + '.' + nl, 'I-DefUnderscore', 'review', 'refers to the renamed definition(s); check every definition the name mentions')

# ---------------------------------------------------------------- C. Rocq prefix -> namespace
C_RULES = [  # (namespace of the flat decl, token regex, target namespace, kinds, status)
    # NOT here: Model.oforest_*, osat_*, owit_*, FairnessAssumption.counterMove_*, Model.mapForall2_*:
    # each is about a definition of exactly that name (Model.oforest, ...), which is the Mathlib rule.
    (L[:-1], r'obl', L + 'Obl', ('theorem',), 'review'),
    (L + 'HeapLang', r'loc', L + 'HeapLang.Loc', ('theorem',), 'review'),
]
for full, d in list(decls.items()):
    cur = current(full)
    ns, last = split(cur)
    for src, tok, dst, kinds, st in C_RULES:
        if ns == src and d['k'] in kinds:
            m = re.match(r'(' + tok + r')_(.+)$', last)
            if m:
                propose(full, dst + '.' + m.group(2), 'C-Namespace', st,
                        'no definition named ' + tok + '; the rest of the family lives in ' + dst.removeprefix(L))
# Par / Wit families
for o, n in {'parBelow': 'Par.below', 'parLe': 'Par.le', 'parBelow_obl': 'Par.below_obl',
             'parBelow_thread': 'Par.below_thread', 'parLe_obl': 'Par.le_obl', 'witCreds': 'Wit.creds',
             'witCreds_succ': 'Wit.creds_succ', 'witLayers': 'Wit.layers'}.items():
    propose(L + o, L + n, 'C-Namespace', 'review', 'family already lives in Par.* / Wit.*')
for full in list(decls):
    ns, last = split(current(full))
    if ns == L[:-1] and re.match(r'par(Below|Le)_', last) and full not in plan:
        m = re.match(r'par(Below|Le)_(.*)$', last)
        propose(full, L + 'Par.' + lc(m.group(1)) + '_' + m.group(2), 'C-Namespace', 'review', 'family already lives in Par.*')

# ---------------------------------------------------------------- E (cont). namespaces of renamed Prop defs
for full in list(decls):
    for old_ns, new_ns in renamed_ns.items():
        if full.startswith(old_ns + '.'):
            cur = current(full)
            if cur.startswith(old_ns + '.'):
                propose(full, new_ns + cur[len(old_ns):], 'E-PropDef', plan.get(old_ns, {}).get('status', 'auto'),
                        'dot-notation namespace follows the renamed definition')
# ---------------------------------------------------------------- D. vocabulary of theorem names
VOC = {'ex': 'exists', 'all': 'forall', 'mon': 'mono', 'idemp': 'idem', 'included': 'inc', 'impl': 'imp', 'upd': 'update'}
LR = {'l': 'left', 'r': 'right'}
for full, d in list(decls.items()):
    if d['k'] not in ('theorem',):
        continue
    ns, last = split(current(full))
    nl = retok(last, lambda ts: [VOC.get(t, t) for t in ts])
    if nl != last:
        propose(full, ns + '.' + nl, 'D-Vocabulary', 'auto',
                'Iris-Lean BI: exists/forall (never ex/all), mono, idem, inc (CMRA inclusion), imp (BIBase.imp)')
        last = nl
    nl = retok(last, lambda ts: [LR.get(t, t) for t in ts])
    if nl != last:
        propose(full, ns + '.' + nl, 'D-LeftRight', 'decision',
                'D2: Iris-Lean BI/Algebra/Std use _left/_right (≈90%); Iris-Lean WP keeps _l/_r (wp_frame_l)')
for o, n in {'TrProp.ex': 'TrProp.exists', 'TrProp.all': 'TrProp.forall', 'TrSpec.ex': 'TrSpec.exists',
             'TrSpec.all': 'TrSpec.forall', 'TrIProp.ex': 'TrIProp.exists', 'TrIProp.all': 'TrIProp.forall'}.items():
    propose(L + o, L + n, 'D-Vocabulary', 'auto', 'as Iris-Lean BIBase.exists / BIBase.forall (declared with «»)')
for full, d in decls.items():  # _1/_2 suffixes: list only
    if d['k'] == 'theorem' and re.search(r'_[12]$', full) and full not in plan:
        propose(full, full, 'D-Vocabulary', 'review', 'Iris-Lean uses _mp/_mpr for the halves of an iff; check meaning of _1/_2')
        plan.setdefault(full, dict(new=full, cats=['D-Vocabulary'], status='review',
                                   note='Iris-Lean uses _mp/_mpr for the halves of an iff; check meaning of _1/_2'))

# ---------------------------------------------------------------- F (cont). theorem tokens ALC/ALCb
for full, d in list(decls.items()):
    if d['k'] not in ('theorem', 'instance'):
        continue
    ns, last = split(current(full))
    nl = retok(last, lambda ts: [{'ALC': 'alc', 'ALCb': 'alcIf'}.get(t, t) for t in ts])
    if nl != last:
        propose(full, ns + '.' + nl, 'F-IPropDef', 'auto', 'refers to the renamed definition')

# ---------------------------------------------------------------- H. theorems named in lowerCamelCase
H = {'certifyEntries': 'certify_entries', 'alwaysRun': 'always_run', 'bundleAlwaysCert': 'bundle_always_cert',
     'untilRunDischarged': 'until_run_discharged', 'regMark': 'reg_mark', 'sysStepIter': 'sysStep_iter',
     'regCheck': 'reg_check', 'certOfEntry': 'cert_of_entry', 'bundleUntilCert': 'bundle_until_cert',
     'bundleIntro': 'bundle_intro', 'untilRun': 'until_run', 'regRegister': 'reg_register',
     'getOblsThreadActive': 'obls_thread_active_get', 'Examples.initThreads': 'Examples.init_threads'}
for o, n in H.items():
    propose(L + o, L + n, 'H-TheoremCamel', 'review', 'theorems are snake_case; Rocq name shown, a statement-based name may be better')

# ---------------------------------------------------------------- J. snake-split references to camelCase defs
J = {'sat_frame_move': 'satFrame_move', 'sat_sat_frame': 'sat_satFrame', 'except_0_inv': 'except0_inv',
     'is_except_0_inv': 'isExcept0_inv', 'except_0_rupd': 'except0_rupd',
     'HeapLang.base_step_to_val': 'HeapLang.baseStep_toVal',
     'HeapLang.base_step_to_val_atomic': 'HeapLang.baseStep_toVal_atomic',
     'HeapLang.prim_step_to_val_always_to_val': 'HeapLang.primStep_toVal_always_toVal',
     'iProp_sat_lc_and': 'iPropSat_lc_and', 'iProp_sat_lc_at_and': 'iPropSat_lc_at_and',
     'iProp_sat_lc_at_frame_and': 'iPropSat_lc_at_frame_and', 'guar_state_fact': 'guar_stateFact',
     'Examples.lockLevel_lb': 'Examples.lockLevelLb_of_lockLevel', 'Examples.lockLevel_lb_valid': 'Examples.lockLevelLb_valid',
     'Examples.TicketLock.aliveFairLock_release_progress': 'Examples.TicketLock.aliveFairLock_releaseProgress',
     'Examples.TicketLock.lockInvAliveTrSpec_release_progress': 'Examples.TicketLock.lockInvAliveTrSpec_releaseProgress',
     'Examples.TicketLockMono.aliveFairLock_release_progress': 'Examples.TicketLockMono.aliveFairLock_releaseProgress',
     'Examples.TicketLockMono.lockInvAliveTrSpec_release_progress': 'Examples.TicketLockMono.lockInvAliveTrSpec_releaseProgress',
     'Examples.TicketLockMono.aliveFairLock_next_monotone': 'Examples.TicketLockMono.aliveFairLock_nextMonotone',
     'Examples.TicketLockMono.lockInvAliveTrSpec_next_monotone': 'Examples.TicketLockMono.lockInvAliveTrSpec_nextMonotone'}
for o, n in J.items():
    if L + o in decls:
        ns, last = split(current(L + o))
        propose(L + o, L + n if L + o not in plan else ns + '.' + n.split('.')[-1], 'J-SplitRef', 'review',
                'a lowerCamelCase definition keeps its spelling inside theorem names (Iris-Lean #689)')
for full in list(decls):  # osat_alloc_obl_{discharged,assigned} (after C)
    cur = current(full)
    for a, b in (('obl_discharged', 'oblDischarged'), ('obl_assigned', 'oblAssigned')):
        if cur.startswith(L + 'Model.OSat.alloc_' + a):
            propose(full, cur.replace(a, b), 'J-SplitRef', 'review', 'refers to OPreds.' + b)

# ---------------------------------------------------------------- L. namespace constants
for full, d in list(decls.items()):
    ns, last = split(current(full))
    if not full.startswith(L + 'Examples.') and not full.startswith('LantanaTest'):
        continue
    if d['k'] in ('def', 'abbrev') and re.fullmatch(r'N[a-z]*', last):
        ex = ns.split('.')[-1]
        new = (lc(ex) + 'N') if last == 'N' else (last[1:] + 'N')
        propose(full, ns + '.' + new, 'L-NamespaceConst', 'review', 'Iris-Lean: ticketLockN, invHeapN, spinlockN (fooN)')
    m = re.fullmatch(r'(N[a-z]*)_(.+)', last)
    if d['k'] == 'theorem' and m:
        ex = ns.split('.')[-1]
        base = (lc(ex) + 'N') if m.group(1) == 'N' else (m.group(1)[1:] + 'N')
        propose(full, ns + '.' + base + '_' + m.group(2), 'L-NamespaceConst', 'review', 'follows the constant')

# ---------------------------------------------------------------- M. namespace repeated in example names
for full, d in list(decls.items()):
    if not full.startswith(L + 'Examples.') or d['k'] != 'theorem':
        continue
    ns, last = split(current(full))
    exns = ns.split('.')[-1]
    tok = last.split('_')[0]
    if tok == lc(exns) and '_' in last:
        propose(full, ns + '.' + last[len(tok) + 1:], 'M-RepeatNs', 'auto', 'Examples.FlagClient.flagClient_x → Examples.FlagClient.x')

# ---------------------------------------------------------------- N. stdlib facts in Lantana namespaces
N_ = {'getElem?_set_append': 'List.getElem?_set_append',
      'getLast?_eq_getElem?_of_length': 'List.getLast?_eq_getElem?_of_length',
      'Model.getLast?_eq_getElem?_of_length': 'List.getLast?_eq_getElem?_of_length',
      'Model.getLast?_take': 'List.getLast?_take_succ_of_getElem?',
      'Model.lt_length_of_getElem?': 'List.lt_length_of_getElem?', 'Model.option_rel_inv': 'Option.Rel.inv'}
for o, n in N_.items():
    propose(L + o, n, 'N-Stdlib', 'review', 'general List/Option fact: Lantana.Prelude, in the type namespace (two copies of getLast?_eq_getElem?_of_length: merge)')

# ---------------------------------------------------------------- O. Model.Obl/Obls (decision D5)
for full in list(decls):
    cur = current(full)
    for a, b in (('Lantana.Model.Obls', 'Lantana.Model.Obligations'), ('Lantana.Model.Obl', 'Lantana.Model.Obligation')):
        if cur == a or cur.startswith(a + '.'):
            propose(full, b + cur[len(a):], 'O-ObligationType', 'decision',
                    'D5: Lantana.Obl (assertions) and Lantana.Model.Obl (model type) share a short name; cf. Model.Witness/Witnesses')
            break

# ---------------------------------------------------------------- namespaces follow renamed definitions/types
DEFISH = ('def', 'abbrev', 'opaque', 'class', 'structure', 'inductive')
moved = {o: v for o, v in plan.items() if decls[o]['k'] in DEFISH and v['new'] != o}
for full in list(decls):
    cur = current(full)
    parts = cur.split('.')
    for i in range(len(parts) - 1, 0, -1):
        pre = '.'.join(parts[:i])
        if pre in moved and pre != full:
            v = moved[pre]
            propose(full, v['new'] + cur[len(pre):], v['cats'][0], v['status'],
                    'namespace follows ' + pre.removeprefix(L) + ' (dot-notation uses need no change)')
            break

# auto-generated parent projections (toX) regenerate from the class names: drop them
for o in [o for o in plan if re.match(r'to[A-Za-z]', o.split('.')[-1]) and decls[o]['k'] in ('field', 'instance')]:
    del plan[o]

# ---------------------------------------------------------------- collisions
news = collections.Counter(v['new'] for v in plan.values())
existing = set(decls) - set(plan)
for old, v in plan.items():
    if v['new'] != old and (news[v['new']] > 1 or v['new'] in existing):
        v['note'] = ('COLLISION with ' + v['new'] + '; ' + v['note']).strip('; ')
        if v['status'] == 'auto':
            v['status'] = 'review'

# ---------------------------------------------------------------- output
out = open('inventory.tsv', 'w')
out.write('category\tstatus\told\tnew\tkind\tlocation\trocq\tnote\n')
rows = []
for old, v in plan.items():
    d = decls[old]
    loc = d['m'].replace('.', '/') + '.lean:' + d['ln']
    cat = '+'.join(dict.fromkeys(v['cats']))
    rows.append((cat, v['status'], old.removeprefix(L), v['new'].removeprefix(L), d['k'], loc,
                 d['al'].replace('lan:', ''), v['note']))
rows.sort(key=lambda r: (r[0], r[5]))
for r in rows:
    out.write('\t'.join(r) + '\n')
out.close()
c = collections.Counter((r[0].split('+')[0], r[1]) for r in rows)
cats = sorted({k for k, _ in c})
print(f"{'category':22} {'auto':>5} {'review':>6} {'decision':>8} {'optional':>8}")
for k in cats:
    print(f"{k:22} {c[(k,'auto')]:5} {c[(k,'review')]:6} {c[(k,'decision')]:8} {c[(k,'optional')]:8}")
print('total rows', len(rows), '| collisions', sum('COLLISION' in r[7] for r in rows),
      '| files touched (definitions)', len({r[5].split(':')[0] for r in rows}))
