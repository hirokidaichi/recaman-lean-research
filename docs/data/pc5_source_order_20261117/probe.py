import itertools,json,time,sys,hashlib
from pathlib import Path
from collections import defaultdict
P=Path(__file__).resolve().parent
START=time.process_time()

def evaluate(w,h):
    H=[0];B=[0];idx=defaultdict(list);src={};free=[];E=S=0;positive=True
    for q,x in enumerate(w):
        if x=='A':
            src[q]=list(idx[(H[q]-1,B[q]-q*(H[q]-1))])
            if src[q]:E+=1
            else:free.append(q)
        else:S+=1
        positive=positive and E+1<=S
        idx[(H[q],B[q]-q*H[q])].append(q)
        H.append(H[-1]+(1 if x=='A' else -1));B.append(B[-1]+H[-1])
    return H,src,free,positive

mode=sys.argv[1]
if mode=='discovery':hs,ds,rs,gs,ss=(2,5),(5,7),(0,1,2,3,4,7,31),(1,4,9),(0,1,2,3)
elif mode=='holdout':hs,ds,rs,gs,ss=(3,11),(6,10),(2,3,5,19,73),(2,7),(0,2)
else:raise ValueError(mode)
pres=['A'*r for r in rs]+['A'*a+'S'*g+'A'*b for a,b in [(1,1),(1,2),(2,1)] for g in gs]
seen=set();best={};counts={'words':0,'positive':0,'low4':0,'deep_low4':0,'auxiliary_A_counter':0,'auxiliary_B_counter':0,'parent_counter':0};counter=None
for h,d,pre,s in itertools.product(hs,ds,pres,ss):
    descent=pre.count('A')-pre.count('S')+d
    if descent<=0:continue
    n=d+2+2*s
    for slots in itertools.combinations(range(n),s):
        if time.process_time()-START>3.5:raise RuntimeError('cooperative3.5CPU stop')
        chosen=set(slots);tail=''.join('S' if i in chosen else 'A' for i in range(n))
        w='S'*h+pre+'S'*descent+tail
        if (h,w) in seen:continue
        seen.add((h,w));counts['words']+=1
        H,src,free,pos=evaluate(w,h);T=len(w)
        assert H[T]==2-h
        if not pos:continue
        counts['positive']+=1
        low=[q for q in free if H[q]<=1-h];m=min(H);v=max(q for q in range(T+1) if H[q]==m)
        visits=[q for q in range(T) if H[q]==-h-2]
        row={'word':w,'h':h,'d_parameter':d,'T':T,'min_height':m,'last_minimum':v,'A_before_minimum':w[:v].count('A'),'low_free':low,'total_free':len(free),'source_visits':visits,'sources':src,'word_sha256':hashlib.sha256(w.encode()).hexdigest()}
        if str(d) not in best or (len(low),T)<(len(best[str(d)]['low_free']),best[str(d)]['T']):best[str(d)]=row
        if len(low)<=4:
            counts['low4']+=1
            if m<=-h-5:counts['deep_low4']+=1
            a_bad=len(visits)>4;b_bad=m<=-h-5 and w[:v].count('A')>3
            counts['auxiliary_A_counter']+=a_bad;counts['auxiliary_B_counter']+=b_bad
            full=w+'ASSSSAAA'*5+'A';HH,fullsrc,ff,fullpos=evaluate(full,h)
            parent=fullpos and all(fullsrc[q] for q in range(T,len(full)) if full[q]=='A') and all(fullsrc[T+8*j]==[h-1] for j in range(6))
            counts['parent_counter']+=parent
            if a_bad or b_bad or parent:
                counter={**row,'auxiliary_A_counter':a_bad,'auxiliary_B_counter':b_bad,'parent_counter':parent,'full_word':full,'full_sources':fullsrc,'full_positive':fullpos}
                break
    if counter:break
for d,row in best.items():(P/(mode+'-best-d'+d+'.json')).write_text(json.dumps(row,indent=2)+'\n')
if counter:(P/(mode+'-counter.json')).write_text(json.dumps(counter,indent=2)+'\n')
out={'mode':mode,'counts':counts,'counterexample':counter is not None,'best':{d:{k:r[k] for k in ['h','T','min_height','last_minimum','A_before_minimum','total_free']}|{'low_free':len(r['low_free']),'source_visits':len(r['source_visits'])} for d,r in best.items()},'cpu_seconds':time.process_time()-START,'evidence':'COMPUTED finite family only'}
(P/(mode+'-summary.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
