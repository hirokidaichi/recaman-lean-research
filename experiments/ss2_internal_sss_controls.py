#!/usr/bin/env python3
"""H-20261006-03 explicit controls; no census or proof by testing."""
import hashlib
import json
from pathlib import Path
import sys
from verify_ss2_collision_pair import first_p2, replay
from verify_ss2_pair_endpoints import direct

def model(name,period,times,expect_nosaas,expect_internal):
    p=len(period);mask=sum(1<<t for t,x in enumerate(period) if x=="A")
    assert 2*bin(mask).count("1")>p
    rows=[]
    for t,d in times:
        assert period[t%p]=="A"
        assert first_p2(mask,p,t)==d
        row=replay(mask,p,t,d)
        assert row["ss"]==2
        rows.append(row)
    assert rows[0]["oldest"]==rows[1]["oldest"]
    ns="SAAS" not in period*4
    assert ns==expect_nosaas
    A=next(x for x in rows if x["tail_A"]==1)
    S=next(x for x in rows if x["tail_A"]==0)
    s=A["phase"]-A["lag"]+1
    triples=[A["phase"]-i-3 for i in range(A["lag"]-2) if A["word"][i:i+3]=="SSS"]
    assert len(triples)==1
    q=triples[0]
    assert (s<q)==expect_internal
    endpoints=direct(mask,p)
    E=set((z["phase"]-z["lag"])%p for z in endpoints)
    N=set((z["phase"]-j)%p for z in rows for j,x in enumerate(z["word"],1) if x=="S")
    assert s%p not in E and q%p not in E
    if expect_internal:
        assert s%p!=q%p and len(N-E)>=2
    C=A["word"][:-1]
    k=S["lag"]-len(C)
    assert k>0 and S["word"][k:]==C
    X=S["word"][:k]
    return dict(name=name,p=p,period=period,mass=2*bin(mask).count("1")-p,
                NoSAAS=ns,donors=rows,C=C,X=X,s=s,q=q,
                oldest_phase=s%p,SSS_first_phase=q%p,
                lowSS_endpoint_phases=sorted(E),uncovered_phases=sorted(N-E),
                all_lowSS_Sended_witnesses=endpoints)

def generated(name,C,X,padding,ns,internal):
    V=X+C
    return model(name,V[::-1]+"A"*padding,[(len(C),len(C)+1),(len(V),len(V))],ns,internal)

def remaining(r):
    C="AS"*(9*r+5)+"AAA"+"SA"*(3*r+1)+"SSS"
    X="SA"*(8*r+6)+"A"
    return generated("remaining_family_r"+str(r),C,X,1,True,False)

def main():
    phase=sys.argv[1];assert phase in ("discovery","holdout")
    if phase=="discovery":
        models=[generated("pure_alternating_positive_p33","AAASSSASAS","AS"*10+"A",2,True,True),
                generated("drop_NoSAAS_q_equals_s","ASASAAASSS","AS"*10+"A",2,False,False),
                model("reused_NoSAAS_p22","ASAAAAASASASASASASASSS",[(5,19),(18,31)],True,True),
                remaining(0)]
    else:
        models=[remaining(1),remaining(2)]
    print(json.dumps(dict(protocol="H-20261006-03",phase=phase,status="PASS",
                          source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          models=models),indent=2))

if __name__=="__main__":
    main()

