"""Forward cumulative-area audit; does not import the discovery evaluator."""
import json,time
from collections import defaultdict
from pathlib import Path
P=Path(__file__).resolve().parent
start=time.process_time()

def scan(w):
    H=[0];B=[0];sources={};free=[];index=defaultdict(list);positive=True;E=S=0
    for q,x in enumerate(w):
        if x=='A':
            sources[q]=list(index[(H[q]-1,B[q]-q*(H[q]-1))])
            if sources[q]:E+=1
            else:free.append(q)
        else:S+=1
        positive=positive and E+1<=S
        index[(H[q],B[q]-q*H[q])].append(q)
        H.append(H[q]+(1 if x=='A' else -1));B.append(B[q]+H[q+1])
    return H,B,sources,free,positive

records=[]
for h,r in [(2,6),(19,65)]:
    w='S'*(h+2)+'A'*(r+4)+'S'*r
    H,B,src,free,pos=scan(w);T=len(w);m=min(H);v=max(q for q in range(T+1) if H[q]==m)
    R=next(q for q in range(v+1,T+1) if H[q]==2-h)
    low=[q for q in free if H[q]<=1-h]
    assert pos and H[T]==2-h and len(low)==3 and len(free)==r+3
    assert sum(x=='A' for x in w[:v])==0 and w[:R].count('A')==4
    assert set(q for q in free if q<R)==set(low)
    records.append({'kind':'first-return-high-free','h':h,'r':r,'word':w,'sources':src,'low_free':low,'total_free':len(free),'m':m,'v':v,'R':R})

for h in (1,7,29):
    k=h+5;w='S'*k+'A'*7;H,B,src,free,pos=scan(w)
    assert pos and H[-1]==2-h and len(free)==6
    assert all(H[q]<=1-h for q in free)
    assert {q:s for q,s in src.items() if s}=={k+2:[k-1]}
    records.append({'kind':'impossible-depth-equality','h':h,'word':w,'sources':src,'low_free':free})

def visit_map(w,m):
    H,B,src,free,pos=scan(w);T=len(w);c=m+2
    assert min(H)>=m and H[T]>c
    visits=[q for q in range(T) if H[q]==c]
    direct=[q for q in visits if w[q]=='A' and not src[q]]
    down=[q for q in visits if w[q]=='S']
    actual=[q for q in visits if w[q]=='A' and src[q]]
    floorfree=[q for q in free if H[q]==m]
    down_map={q:next(t for t in range(q+1,T) if H[t]==c-1 and w[t]=='A') for q in down}
    assert len(set(down_map.values()))==len(down)
    assert set(down_map.values())<=set(free)
    # Small fixed certificates: exact bipartite matching to earlier floor free.
    def match(i,used,chosen):
        if i==len(actual):return chosen
        t=actual[i]
        for q in floorfree:
            if q<t and q not in used:
                result=match(i+1,used|{q},chosen+[(t,q)])
                if result is not None:return result
        return None
    amap=match(0,set(),[]);assert amap is not None
    images=direct+list(down_map.values())+[q for _,q in amap]
    assert len(images)==len(visits) and len(set(images))==len(images)
    assert all(q in free and H[q]<=c for q in images)
    return {'kind':'floor-visit-map','word':w,'m':m,'sources':src,'visits':visits,'free':free,'free_A_images':direct,'S_images':down_map,'actual_A_images':amap,'wallet_count':sum(H[q]<=c for q in free)}

for k in (2,7,31):
    row=visit_map('S'*k+'AAAA',-k)
    assert len(row['visits'])==row['wallet_count']==2
    records.append(row)
records.append(visit_map('S'*5+'AASAAA',-5))
H,B,src,free,pos=scan('S')
assert min(H)>=-2 and H[1]<0 and free==[]
records.append({'kind':'terminal-guard-counter','word':'S','T':1,'m':-2,'visits':[0],'free':[],'parent_counter':False})
result={'status':'pass','records':records,'cpu_seconds':time.process_time()-start,'scope':'fixed independently evaluated certificates; no universal computation claim'}
(P/'audit-certificates.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':result['status'],'certificate_count':len(records),'cpu_seconds':result['cpu_seconds'],'scope':result['scope']}))
