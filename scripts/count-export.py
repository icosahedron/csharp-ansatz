#!/usr/bin/env python3
"""Count the records in a lean4export NDJSON file (formats 3.0.0 and 3.1.0).

Independent of Warrant: this is the oracle for the expected counts in the
tests (see tests/data/README.md).  Usage: count-export.py FILE [FILE ...]
"""
import sys, json, gzip, collections
for path in sys.argv[1:]:
    op = gzip.open if path.endswith('.gz') else open
    names=levels=exprs=0; consts=collections.Counter(); first=last=None; maxie=-1; nrec=0
    with op(path,'rt',encoding='utf-8') as f:
        for i,line in enumerate(f):
            o=json.loads(line)
            if i==0: continue
            if 'in' in o: names+=1
            elif 'il' in o: levels+=1
            elif 'ie' in o: exprs+=1; maxie=max(maxie,o['ie'])
            else:
                k=list(o)[0]; d=o[k]; nrec+=1
                if k=='inductive':
                    t=d.get('types',d.get('inductiveVals')); c=d.get('ctors',d.get('constructorVals')); r=d.get('recs',d.get('recursorVals'))
                    consts['induct']+=len(t); consts['ctor']+=len(c); consts['rec']+=len(r)
                elif k=='def' and isinstance(d,list):
                    for x in d: consts['opaque' if 'isUnsafe' in x else 'def']+=1
                elif isinstance(d,list): consts[k]+=len(d)
                else: consts[{'axiomInfo':'axiom','quotInfo':'quot'}.get(k,k)]+=1
    print(path, dict(names=names, levels=levels, exprs=exprs, records=nrec, consts=dict(sorted(consts.items())), total=sum(consts.values())))
