#!/usr/bin/env python3
"""Audit of the lag-max 19 matching-closure logs (E-356), 2026-10-03.

Checks that docs/data/issue73_20260916/matching_closure_lagmax19_shard{0..3}.txt
  (1) carry the same run header (flags) and the end line `excluded 409/409, consistent closure 0, cap hit 0`,
  (2) list, shard by shard and in order, exactly the minimal P2 words of lag 19 with index % 4 == shard
      (enumeration order of `bit_words` in experiments/issue73_20260916/matching_closure_search.py),
  (3) cover all 1,636 minimal lag-19 words once (no duplicate, nothing missing, nothing extra),
  (4) tag every word `excluded`.
Reproduction of individual words with the committed search (revision b8b970c) is a separate step:
  python3 experiments/issue73_20260916/matching_closure_search.py 19 40 5000000 --mrv --noaas --owners=19 --v=WORD
and its per-word line must equal the shard line (verdict, total nodes, span)."""
import re, sys
def mass(w): return sum(1 if b else -1 for b in w)
def moment(w): return sum((i+1)*(1 if b else -1) for i,b in enumerate(w))
def p2(w): return mass(w)==1 and moment(w)==0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1,len(w)))
def bit_words(n):
    ws=[()]
    for _ in range(n): ws=[(b,)+w for w in ws for b in (False,True)]
    return ws
def s(w): return ''.join('A' if b else 'S' for b in w)
allw=[s(w) for w in bit_words(19) if minimal(w)]
print(f'minimal lag-19 words: {len(allw)}')
base='docs/data/issue73_20260916/matching_closure_lagmax19_shard%d.txt'
seen={}; headers=set(); ok=True; nodes=[]
for sh in range(4):
    lines=open(base%sh).read().splitlines()
    headers.add(lines[0]); tail=lines[-1]
    ents=[re.match(r'\s+([AS]+): (\w+) \(total (\d+) nodes, span (-?\d+)\.\.(-?\d+)\)',l) for l in lines[1:-1]]
    bad=[l for l,m in zip(lines[1:-1],ents) if not m]
    ents=[(m.group(1),m.group(2),int(m.group(3))) for m in ents if m]
    exp=[w for i,w in enumerate(allw) if i%4==sh]
    order=[w for w,_,_ in ents]==exp
    tags=sorted(set(t for _,t,_ in ents))
    print(f'shard {sh}: entries {len(ents)}, expected {len(exp)}, same order {order}, tags {tags}, unparsed {len(bad)}, end: {tail.strip()}')
    ok&=order and tags==['excluded'] and not bad and tail.strip()=='=> excluded 409/409, consistent closure 0, cap hit 0'
    for w,_,n in ents: seen[w]=seen.get(w,0)+1; nodes.append(n)
print('headers:', *sorted(headers), sep='\n  ')
dups=sum(1 for v in seen.values() if v>1); missing=len(set(allw)-set(seen)); extra=len(set(seen)-set(allw))
print(f'distinct {len(seen)}, duplicates {dups}, missing {missing}, extra {extra}')
print(f'total nodes {sum(nodes)}, max {max(nodes)}, words excluded at the root of every own-branch (nodes == 9) {sum(1 for n in nodes if n==9)}')
ok&=len(headers)==1 and dups==0 and missing==0 and extra==0
print('AUDIT', 'PASS' if ok else 'FAIL'); sys.exit(0 if ok else 1)
