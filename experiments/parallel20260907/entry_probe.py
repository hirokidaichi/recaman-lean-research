#!/usr/bin/env python3
"""Frozen exact tests for H-20260907-04/05; no discovery/holdout claim."""
import argparse, collections, hashlib, json, pathlib, subprocess
REV='612fcfaf74bfb49f3ae05a268057c82f70dcca26'

def step(n,v,H):
    c=v-n
    w=c if c>0 and c not in H else v+n
    H.add(w)
    return w

def pair(F,B,m,Q):
    n=max(B+2, len(F)+5, 4*Q+m+5, 10)
    while (2*n+m+3-n*(n+1)//2)%2: n+=1
    c=n+m+2; v=2*n+m+3
    assert c>B and c+3*Q<v
    common=set(F)|{0,v}
    H0=common|{c+Q,c+2*Q}
    H1=common|{c,c+3*Q}
    def summary(H):
        return (sorted(x for x in H if x<=B),len(H),max(H),sum(H),[sum(x%Q==r for x in H) for r in range(Q)])
    assert summary(H0)==summary(H1)
    assert len(H0)<=n+1 and max(H0)<=n*(n+1)//2 and m not in H0 and m not in H1
    hs0=H0.copy(); hs1=H1.copy(); x0=step(n+1,v,hs0); x1=step(n+1,v,hs1)
    y0=step(n+2,x0,hs0); y1=step(n+2,x1,hs1)
    assert (x0,y0)==(c,m) and y1!=m and x1!=m
    return dict(B=B,m=m,Q=Q,n=n,v=v,c=c,H0=sorted(H0),H1=sorted(H1),summary=summary(H0),path0=[v,x0,y0],path1=[v,x1,y1])

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--limit',type=int,default=1000000);args=ap.parse_args()
    print('source_revision='+REV)
    print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
    print('protocol=H-20260907-04/05; fixed algebraic and canonical regression; no new holdout')
    print('command=python3 experiments/parallel20260907/entry_probe.py --limit '+str(args.limit))
    a=[0];sign=['-'];birth={0:0};events=[];counts=collections.Counter();violA=[];violB=[]
    for t in range(1,args.limit+1):
        c=a[-1]-t; s=c>0 and c not in birth; w=c if s else a[-1]+t
        a.append(w);sign.append('S' if s else 'A')
        if w not in birth:
            if 1<=w<t:
                T=t;m=w
                assert s
                if T>=2 and m+1 in birth and birth[m+1]<T-2 and sign[T-1]=='A': violA.append((T,m))
                p=T-1;k=0
                while p>=2 and sign[p-1]=='A' and sign[p]=='S': p-=2;k+=1
                assert a[p]==T+m+k
                blockers=[];internal=[]
                for i in range(k):
                    cand=m+3*(k-i);use=p+2*i+1
                    assert a[use-1]-use==cand and sign[use]=='A' and birth.get(cand,10**30)<use
                    blockers.append((cand,birth[cand],use))
                    if birth[cand]>p:internal.append((cand,birth[cand],use))
                source=('initial' if p==0 else sign[p])
                counts[source]+=1
                counts[source+('_k0' if k==0 else '_kpos')]+=1
                if k>0 and source=='A': assert T<=m+5*k+3
                assert k<=p-1 if k>0 else True
                e=dict(T=T,m=m,p=p,k=k,source=source,source_word=''.join(sign[max(1,p-3):p+1]),base_value=a[p],previous=a[p-1] if p else None,blockers_count=len(blockers),first_blockers=blockers[:3],last_blockers=blockers[-3:],internal=internal[:4],nonoverlap=3*k<T)
                if internal:violB.append(e)
                if m in (1,2,4,19,61) or len(events)<8:events.append(e)
            birth[w]=t
    for e in events:print('late_hit='+json.dumps(e,sort_keys=True))
    print('classification='+json.dumps(dict(counts),sort_keys=True))
    print('claim_A_violations='+json.dumps(violA[:5])+' count='+str(len(violA)))
    print('claim_B_violations='+json.dumps(violB[:5],sort_keys=True)+' count='+str(len(violB)))
    cases=[(set(),1,1,1),({0,1,3,6,2},6,4,1),({0,1,3,6,2},6,4,6),(set(a[:100]),max(a[:100]),19,6)]
    for F,B,m,Q in cases:print('summary_pair='+json.dumps(pair(F,B,m,Q),sort_keys=True))
    print('PASS')
if __name__=='__main__':main()
