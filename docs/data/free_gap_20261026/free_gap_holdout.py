from pathlib import Path
import itertools,json
BASE=Path(__file__).parent
PREFIXES=['AASAAA','SAAAAA','SAAAASAAA','SSAAAASAAAA','ASSAAAASAAAA']
DOMAIN=[5,7,9]

def direct(w,n):
    height=0;area=0;E=S=R=0;events=[];zero=None;positive=True
    for b,ch in enumerate(w):
        mass=moment=0;start=None
        # Independent reversed suffix sum, no global F/P map and no imported discovery code.
        for t in range(b-1,-1,-1):
            sg=1 if w[t]=='A' else -1
            mass+=sg;moment+=(b-t)*sg
            if mass==1 and moment==0:start=t;break
        end=ch=='A' and start is not None
        if b==n:zero=S==E
        if ch=='S':S+=1
        else:E+=end;R+=b>=n and not end
        events.append({'i':b,'c':ch,'end':end,'t':start if end else None,'deficit':S-E,'free_after_n':R})
        if b>=n and S-E<1:positive=False
    return zero,positive,R,events

counts={'pairs':0,'zero_prefix':0,'positive_body':0,'supplied_gaps':0,'violations':0,'discovery_counterexamples_verified':0}
violations=[];maxr={}
for beta in PREFIXES:
 for a,b,c,d in itertools.product(DOMAIN,repeat=4):
    counts['pairs']+=1;tail='S'*a+'A'*b+'S'*c+'A'*d;w=beta+tail;n=len(beta)
    zero,pos,r,events=direct(w,n)
    if not zero:continue
    counts['zero_prefix']+=1
    if not pos:continue
    counts['positive_body']+=1
    # E407 finite half-count bound, applied to actual tail only. No restriction on free count.
    A=tail.count('A')
    for j in range(max(0,A//2)):
        z,p,rr,ev=direct(w+'S'*j+'A',n)
        if not ev[-1]['end']:continue
        counts['supplied_gaps']+=1
        maxr[str(r)]=max(j,maxr.get(str(r),-1))
        if j+1>r:counts['violations']+=1;violations.append({'prefix':beta,'parameters':[a,b,c,d],'gap':j,'free':r,'word':w+'S'*j+'A','ledger':ev})
discovery=json.loads((BASE/'free-gap-discovery.json').read_text())
for v in discovery['violations']:
 z,p,r,ev=direct(v['fullword'],len(v['prefix']))
 assert z and all(e['deficit']>=1 for e in ev[len(v['prefix']):-1]) and ev[-1]['end']
 assert ev[-2]['free_after_n']==v['free'] and v['gap']+1>v['free']
 counts['discovery_counterexamples_verified']+=1
out={'protocol':'FREE_GAP_PROTOCOL.json','domain':DOMAIN,'prefixes':PREFIXES,'counts':counts,'max_gap_by_free':maxr,'violations':violations[:12],'evidence':'independent direct suffix checker; disjoint parameter tuples/prefix-tuple pairs; known prefix words are not globally fresh'}
(BASE/'free-gap-holdout.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'counts':counts,'max_gap_by_free':maxr,'first_violation':violations[:1]},indent=2))
