#!/usr/bin/env python3
"""Test equality-family and (SA)^k minWord words as periodic signs for E-070."""
from __future__ import annotations
import hashlib, json, subprocess
from pathlib import Path

def min_word(r):
    w=[1,1]
    for _ in range(r):
        w += [-1,1]
    w += [-1]
    return tuple(w)

def sa_k(k):
    w=[]
    for _ in range(k):
        w += [-1,1]
    return tuple(w)

def p2_lags(e, t, p, maxd=None):
    if maxd is None: maxd=p*(p+1)
    mass=moment=0
    hits=[]
    for d in range(1, maxd+1):
        s=e[(t-d) % p]
        mass += s
        moment += d*s
        if mass==1 and moment==0:
            hits.append(d)
            break
    return hits

def supplied_A(w, maxd=None):
    p=len(w)
    U=[]
    for t in range(p):
        if w[t]==1:
            hits=p2_lags(w, t, p, maxd)
            if hits:
                U.append((t, hits[0]))
    D=[t for t in range(p) if w[t]==-1]
    return U, D

def to_str(w):
    return ''.join('A' if s==1 else 'S' for s in w)

def main():
    print('protocol=H-20260910-37 E-070 probe on equality-family periods')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    # smallest equality pair old word
    v=tuple(-1 if c=='S' else 1 for c in 'SSAAASAASS')
    extra=min_word(9)
    old=v+extra
    new=(1,)+v
    words=[('old31', old), ('new11', new), ('minWord9', extra),
           ('sa25_min96', sa_k(25)+min_word(96)),
           ('minWord0', min_word(0)),
           ('minWord1', min_word(1)),
           ('AASAS', (1,1,-1,1,-1))]
    n_counter=0
    for name,w in words:
        U,D=supplied_A(w)
        mass=sum(w)
        rec=dict(name=name, p=len(w), mass=mass, A=sum(s==1 for s in w),
                 D=len(D), U=len(U), U_le_D=len(U)<=len(D),
                 all_A_supplied=len(U)==sum(s==1 for s in w),
                 word=to_str(w)[:80])
        print('WORD='+json.dumps(rec))
        if rec['all_A_supplied'] or not rec['U_le_D']:
            n_counter += 1
            print('COUNTER='+name)
    print('COUNTERS='+str(n_counter))

if __name__=='__main__':
    main()
