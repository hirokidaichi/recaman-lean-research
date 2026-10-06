#!/usr/bin/env python3
"""Independent direct enumeration of EVERY S-ended lowSS endpoint witness."""
import json
import sys
from verify_ss2_collision_pair import replay, first_p2

def direct(mask,p):
    out=[]
    for t in range(p):
        if not mask & (1<<t):
            continue
        mass=moment=ss=0
        last="A"
        for d in range(1,p*(p+1)+1):
            b="A" if mask & (1<<((t-d)%p)) else "S"
            v=1 if b=="A" else -1
            mass+=v;moment+=d*v
            ss+=last==b=="S"
            last=b
            if mass==1 and moment==0 and ss<=1 and b=="S":
                out.append(replay(mask,p,t,d))
    return sorted(out,key=lambda w:(w["phase"],w["lag"]))

def main():
    totals=[]
    for name in sys.argv[1:]:
        rows=[json.loads(line) for line in open(name)]
        pairs=[r for r in rows if r["kind"]=="pair"]
        summaries=[r for r in rows if r["kind"]=="summary"]
        for r in pairs:
            p,mask=r["p"],r["mask"]
            assert 2*bin(mask).count("1")>p
            witnesses=direct(mask,p)
            assert witnesses==sorted(r["all_lowSS_Sended_witnesses"],key=lambda w:(w["phase"],w["lag"]))
            E=0;nb=0
            for q in witnesses:E|=1<<((q["phase"]-q["lag"])%p)
            assert E==r["endpoint_mask"]
            assert len(r["donors"])==2
            for q in r["donors"]:
                assert mask&(1<<q["phase"]) and first_p2(mask,p,q["phase"])==q["lag"]
                assert replay(mask,p,q["phase"],q["lag"])==q and q["ss"]==2
                nb|=q["neighbors_mask"]
            a,b=r["donors"]
            assert a["phase"]!=b["phase"] and a["oldest"]==b["oldest"]
            free=nb&~E
            assert nb==r["donor_union_mask"] and free==r["uncovered_mask"]
            assert bin(free).count("1")==r["uncovered_count"]
            assert free&(1<<a["oldest"])
            period="".join("A" if mask&(1<<t) else "S" for t in range(p))
            assert ("SAAS" not in period*4)==r["nosaas"]
        for r in summaries:
            group=[x for x in pairs if x["p"]==r["p"]]
            assert len(group)==r["pairs"]
            assert sum(x["uncovered_count"]<2 for x in group)==r["violations"]
        totals.append(dict(file=name,pairs=len(pairs),all_endpoint_sets_exactly_verified=len(pairs),
                           violations=sum(r["uncovered_count"]<2 for r in pairs),
                           min_uncovered=min([r["uncovered_count"] for r in pairs] or [-999])))
    print(json.dumps(dict(status="PASS",files=totals),indent=2))

if __name__=="__main__":
    main()

