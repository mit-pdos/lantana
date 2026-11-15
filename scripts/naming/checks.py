#!/usr/bin/env python3
# Copyright (c) The Lantana-Lean Contributors
# Released under Apache 2.0 license as described in the file LICENSE.
"""Per-rule naming checks, Iris-Lean vs Lantana (docs/naming.md, section 2).

Reads all.tsv (scripts/naming/Dump.lean) from the current directory, prints the number of
declarations each rule flags in Iris-Lean and in Lantana, and writes the flagged declarations
to lan_findings.json and iris_findings.json. Raw: notation and auto-generated names are not
filtered here (inventory.py filters them)."""
import collections, re, sys, json
rows=[l.rstrip('\n').split('\t') for l in open('all.tsv')]
D=[dict(n=r[0],k=r[1],m=r[2],priv=r[3],al=r[4],rs=r[5],ln=r[6]) for r in rows]
for d in D:
    d['root']='Iris' if d['m'].startswith('Iris') else 'Lantana'
    nm=d['n']
    # strip private prefix
    if nm.startswith('_private'):
        nm=re.sub(r'^_private\.[^0]*\.0\.','',nm)
    d['name']=nm
    d['last']=nm.split('.')[-1]
# names of defs/types (camel refs)
refnames=set()
for d in D:
    if d['k'] in ('def','abbrev','opaque','class','structure','inductive','ctor','field','instance'):
        l=d['last']; refnames.add(l[:1].lower()+l[1:])
GREEK=set('αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩℓ')
def is_upper(c): return c.isupper() and c not in GREEK
findings=collections.defaultdict(list)
def add(cat,d,extra=''): findings[(cat,d['root'])].append((d,extra))
for d in D:
    k=d['k']; l=d['last'].rstrip("'"); 
    if l.startswith('inst') and k=='instance': pass
    toks=[t for t in l.split('_') if t]
    if k=='theorem':
        bad=[t for t in toks if is_upper(t[0]) and t not in ('True','False')]
        if bad: add('T1 theorem token UpperCase',d,','.join(bad))
        for t in toks:
            if re.search(r'[a-z0-9][A-Z]',t) and (t[:1].lower()+t[1:]) not in refnames:
                add('T2 camelCase token not a known decl',d,t)
        for i in range(len(toks)-1):
            for j in range(i+2,min(len(toks),i+4)+1):
                cand=toks[i]+''.join(x[:1].upper()+x[1:] for x in toks[i+1:j])
                if cand in refnames and len(cand)>3:
                    add('T3 snake-split ref to camelCase decl',d,'_'.join(toks[i:j])+'→'+cand); break
        for bad,good in [('ex','exists'),('exist','exists'),('all','forall'),('mon','mono'),('idemp','idem'),('included','inc'),('l','left'),('r','right'),('2','mpr'),('1','mp'),('upd','update'),('imp','impl')]:
            if bad in toks: add(f'V {bad}->{good}',d)
    if k in ('def','abbrev','opaque'):
        if d['last'].startswith('inst'): continue
        if '_' in l.strip('_'): add('D1 def with underscore',d)
        if d['rs'] in ('Prop','Type') and not is_upper(l[0]): add(f'D2 {d["rs"]}-valued def not UpperCamel',d)
        if d['rs']=='-' and is_upper(l[0]): add('D3 term-valued def UpperCamel',d)
    if k in ('class','structure','inductive'):
        if not is_upper(l[0]) or '_' in l: add('S1 type not UpperCamel',d)
    if k=='ctor':
        if is_upper(l[0]) or '_' in l: add('C1 ctor not lowerCamel',d)
    if k=='instance':
        if is_upper(l[0]): add('I1 instance UpperCase',d)
    if k=='field':
        if is_upper(l[0]): add('F1 field UpperCase',d)
    if "'" in d['last'] and k in ('def','abbrev','class','structure','inductive'): add('P1 primed def/type',d)
    if '__' in d['last']: add('N1 double underscore',d)
cnt=collections.Counter()
for d in D:
    cnt[(d['root'],d['k'])]+=1
tot={r:sum(v for (rr,k),v in cnt.items() if rr==r) for r in ('Iris','Lantana')}
cats=sorted({c for c,_ in findings})
print(f"{'check':45} {'Iris':>6} {'Lantana':>8}   (totals Iris={tot['Iris']}, Lantana={tot['Lantana']})")
for c in cats:
    print(f"{c:45} {len(findings[(c,'Iris')]):6} {len(findings[(c,'Lantana')]):8}")
json.dump({c: [(d['name'],d['k'],d['m'],d['ln'],d['al'],e) for d,e in findings[(c,'Lantana')]] for c in cats}, open('lan_findings.json','w'), indent=0)
json.dump({c: [(d['name'],d['k'],d['m'],d['ln'],d['al'],e) for d,e in findings[(c,'Iris')]] for c in cats}, open('iris_findings.json','w'), indent=0)
