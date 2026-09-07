#!/usr/bin/env python3
"""Frozen immutable-U7-map extension falsifier; H_extend, issue73."""
import argparse,hashlib,itertools,json,pathlib,subprocess

def rows(word):
    p=len(word);out={}
    for t,e in enumerate(word):
        if e<0:continue
        s=m=0
        for d in range(1,12):
            x=word[(t-d)%p];s+=x;m+=d*x
            if (s,m)==(1,0):
                out[t]=(d,sorted({(t-i)%p for i in range(1,d+1) if word[(t-i)%p]<0}))
                break
    return out

def shortmap(word, rr):
    p=len(word);out={}
    for t,(d,domain) in rr.items():
        if d>7:continue
        neg=[i for i in range(1,d+1) if word[(t-i)%p]<0]
        if d==3:
            assert neg==[3]
            s=(t-3)%p
        elif neg[0]==1:
            assert neg==[1,6,7]
            s=(t-7)%p
        else:
            assert neg==[2,5,7]
            s=(t-5)%p
        assert s in domain and s not in out.values()
        out[t]=s
    return out

def matching(domains):
    owner={}
    def augment(t,seen):
        for s in domains[t]:
            if s in seen:continue
            seen.add(s)
            if s not in owner or augment(owner[s],seen):
                owner[s]=t;return True
        return False
    success=all(augment(t,set()) for t in domains)
    return success, {t:s for s,t in owner.items()}

def hall_bad(domains):
    keys=list(domains)
    for size in range(1,len(keys)+1):
        for subset in itertools.combinations(keys,size):
            union=sorted({s for t in subset for s in domains[t]})
            if len(union)<size:return {'rows':subset,'neighbors':union,'deficiency':size-len(union)}
    return None

def independent_check(word,rr,fixed,residual):
    p=len(word);rr2={}
    for t in range(p):
        if word[t]!=1:continue
        candidates=[]
        for d in range(1,12):
            negatives=[i for i in range(1,d+1) if word[(t-i)%p]==-1]
            if d-2*len(negatives)==1 and d*(d+1)//2-2*sum(negatives)==0:
                candidates.append(d)
        if candidates:
            d=min(candidates)
            domain=sorted(set((t-i)%p for i in range(1,d+1) if word[(t-i)%p]==-1))
            rr2[t]=(d,domain)
    assert rr==rr2
    occupied=set(fixed.values())
    residual2={t:[s for s in domain if s not in occupied] for t,(d,domain) in rr2.items() if d==11}
    assert residual==residual2
    bad=hall_bad(residual)
    assert bad is not None
    full={t:domain for t,(d,domain) in rr2.items()}
    flex,assign=matching(full)
    assert flex==(hall_bad(full) is None)
    return bad,flex,assign

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--min-period',type=int,required=True);ap.add_argument('--max-period',type=int,required=True);args=ap.parse_args()
    print('protocol=issue73 H_extend immutable short-map extension to U11')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
    print('period_range=%r; new property on previously used word ranges' % ((args.min_period,args.max_period),))
    total=longrows=0
    for p in range(args.min_period,args.max_period+1):
        count=0
        for word in itertools.product((-1,1),repeat=p):
            if sum(word)<=0:continue
            total+=1;count+=1
            rr=rows(word);fixed=shortmap(word,rr);occupied=set(fixed.values())
            residual={t:[s for s in domain if s not in occupied] for t,(d,domain) in rr.items() if d==11}
            longrows+=len(residual)
            ok,assignment=matching(residual)
            if not ok:
                bad,flex,fullmatch=independent_check(word,rr,fixed,residual)
                payload={'period':p,'word':''.join('A' if e>0 else 'S' for e in word),'sign_sum':sum(word),'checked_words':total,'all_U11_rows':rr,'fixed_U7_map':fixed,'residual_lag11_domains':residual,'Hall_failure':bad,'flexible_U11_matching_exists':flex,'flexible_U11_matching':fullmatch}
                print('H_EXTEND_REFUTED='+json.dumps(payload,sort_keys=True),flush=True)
                print('independent_negative-offset_recalculation=PASS all_domains=PASS exhaustive_Hall=PASS')
                print('STOP: immutable short-map route only; weaker claims assessed separately')
                return
        print('period=%d words=%d cumulative_lag11_rows=%d PASS' % (p,count,longrows),flush=True)
    print('NO_EXTENSION_FAILURE total_words=%d lag11_rows=%d; no all-period claim' % (total,longrows))
if __name__=='__main__':main()
