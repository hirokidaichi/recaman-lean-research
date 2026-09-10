#!/usr/bin/env python3
"""Search the E-140 equality extra minWord(|v|-1) glued to mass0 moment-1 SS=2 tails."""
from __future__ import annotations
import hashlib, itertools, json, subprocess
from pathlib import Path

def data(w):
    mass=moment=ss=0
    hits=[]
    prev=1
    for i,s in enumerate(w,1):
        mass+=s; moment+=i*s
        if s==prev==-1: ss+=1
        prev=s
        if mass==1 and moment==0: hits.append((i,ss))
    return mass,moment,ss,hits

def to_str(w):
    return ''.join('A' if s==1 else 'S' for s in w)

def min_word(r):
    # AA (SA)^r S
    w=[1,1]
    for _ in range(r):
        w += [-1,1]
    w += [-1]
    return tuple(w)

def main():
    print('protocol=H-20260910-32 case5 equality extra=minWord')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    found=0
    for n in (10,14,18):
        extra=min_word(n-1)
        em,eM,ess,_=data(extra)
        print('EXTRA='+json.dumps(dict(n_v=n,r=n-1,len_extra=len(extra),
              mass=em,moment=eM,ss=ess,need_moment=1-n)))
        n_v=0
        for bits in itertools.product((-1,1),repeat=n):
            mass,moment,ss,hits=data(bits)
            if mass==0 and moment==-1 and ss==2:
                n_v+=1
                old=bits+extra
                new=(1,)+bits
                om,oM,oss,oh=data(old)
                nm,nM,nss,nh=data(new)
                if om==1 and oM==0 and oss==2 and oh and oh[0][0]==len(old):
                    if nm==1 and nM==0 and nss==2 and nh and nh[0][0]==len(new):
                        found+=1
                        print('HIT='+json.dumps(dict(v=to_str(bits),old=to_str(old),new=to_str(new))))
        print('TAILS='+json.dumps(dict(n=n,mass0_moment_m1_ss2=n_v)))
    print('HITS='+str(found))

if __name__=='__main__':
    main()
