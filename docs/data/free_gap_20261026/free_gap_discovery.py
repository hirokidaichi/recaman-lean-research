from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
PREFIXES=['','A','AAA','SAAA','ASAAA','SAAAA','SAAASAAA','SSAAAASAAA']
DOMAIN=[1,2,3,4,6]

def ledger(w,n):
    F=P=E=S=R=0;heights=[0];areas=[0];events=[];seen={0:{0:0}};positive=True;zero=False
    for b,ch in enumerate(w):
        t=seen.get(F-1,{}).get(P-b*(F-1)) if ch=='A' else None
        end=t is not None
        if b==n:zero=(S==E)
        if ch=='S':S+=1;F-=1
        else:F+=1;E+=end;R+=b>=n and not end
        P+=F;heights.append(F);areas.append(P)
        seen.setdefault(F,{}).setdefault(P-(b+1)*F,b+1)
        events.append({'i':b,'c':ch,'end':end,'t':t,'deficit':S-E,'free_after_n':R})
        if b>=n and S-E<1:positive=False
    if n==len(w):zero=(S==E)
    return zero,positive,R,heights,areas,events

counts={'pairs':0,'zero_prefix':0,'positive_body':0,'supplied_gaps':0,'violations':0}
violations=[];max_by_r={};witnesses=[]
for beta in PREFIXES:
 for a,b,c,d in itertools.product(DOMAIN,repeat=4):
    counts['pairs']+=1
    tail='S'*a+'A'*b+'S'*c+'A'*d;w=beta+tail;n=len(beta);B=len(w)
    zero,pos,r,F,P,events=ledger(w,n)
    if not zero:continue
    counts['zero_prefix']+=1
    if not pos:continue
    counts['positive_body']+=1
    roots={}
    for t in range(B):
        mass=F[B]-F[t]
        area=P[B]-P[t]-(B-t)*F[t]
        if mass>0 and 2*area+mass*(mass-1)==0:roots.setdefault(mass-1,t)
    for j,t in roots.items():
        counts['supplied_gaps']+=1
        full=w+'S'*j+'A';z,p,rr,_,_,ev=ledger(full,n)
        assert ev[-1]['end'] and ev[-1]['t'] is not None
        assert r==ev[-2]['free_after_n'] if j or len(w)>n else True
        row={'prefix':beta,'parameters':[a,b,c,d],'tail':tail,'gap':j,'free':r,'start':t,'fullword':full}
        if j+1>r:
            counts['violations']+=1;violations.append(dict(row,ledger=ev))
        if j>max_by_r.get(str(r),-1):max_by_r[str(r)]=j;witnesses.append(row)
out={'protocol':'FREE_GAP_PROTOCOL.json','domain':DOMAIN,'prefixes':PREFIXES,'counts':counts,'max_gap_by_free':max_by_r,'violations':violations[:12],'extremal_updates':witnesses,'evidence':'finite exact discovery only; zero-key filtering uses full actual prefix and validates original-base EndN'}
(BASE/'free-gap-discovery.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'counts':counts,'max_gap_by_free':max_by_r,'first_violation':violations[:1]},indent=2))
