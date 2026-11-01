#!/usr/bin/env python3
"""H-05 auxiliary actual-word induction, frozen discovery and holdout."""
import argparse
import itertools
import json


def data(w):
    h = q = 0
    found = []
    for k, c in enumerate(w, 1):
        x = 1 if c == "A" else -1
        h += x
        q += k*x
        if k < len(w) and h == 1 and q == 0 and c == "S":
            found.append(k)
    return h, q, sum(a == b == "S" for a,b in zip(w,w[1:])), found


def generate(n):
    r = n//2 - 2
    for si in itertools.combinations_with_replacement(range(r), 2):
        runs = [1]*r
        for k in si:
            runs[k] += 1
        for ai in itertools.combinations_with_replacement(range(r+1), 3):
            gaps = [0]+[1]*(r-1)+[0]
            for k in ai:
                gaps[k] += 1
            if not gaps[-1]:
                continue
            yield "A"*gaps[0]+"".join("S"*runs[k]+"A"*gaps[k+1] for k in range(r))


ap=argparse.ArgumentParser()
ap.add_argument("--mode", choices=["discovery","holdout"], required=True)
args=ap.parse_args()
total=0
controls={}
for n in (range(1,19) if args.mode=="discovery" else (20,24)):
    words=(map("".join,itertools.product("AS",repeat=n)) if args.mode=="discovery" else generate(n))
    checked=0
    for w in words:
        mass,moment,ss,pre=data(w)
        if mass != 0 or moment+n > 0:
            continue
        if w[-1]=="A" and ss<=2:
            checked+=1
            assert pre, (w,mass,moment,ss)
        elif not pre:
            mode="drop_last_A" if ss<=2 else "drop_SS_bound" if w[-1]=="A" else None
            if mode and mode not in controls:
                controls[mode]=dict(word=w,mass=mass,moment=moment,ss=ss)
    total+=checked
    print(json.dumps(dict(length=n,checked=checked)),flush=True)
assert total>0
print(json.dumps(dict(status="PASS",mode=args.mode,checked=total,controls=controls)),flush=True)
