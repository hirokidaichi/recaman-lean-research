"""Exact implicit FULL interval+high-set seed; all-word filter-language controls."""
import itertools,json,sys,time
start=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
lengths=range(6)if mode=='discovery'else[6,7]
words=[''.join(t)for Q in lengths for t in itertools.product('AS',repeat=Q)]
if mode=='holdout':words+=['S'*(2*n+2)+'ASAA'*n+'A'+'S'*(2*n+1)+'AA'for n in [1,3,7]]
counts={'words':0,'chronology_good':0,'chronology_bad':0,'all_filters_pass':0,'correct_exact_replay_or_negative':0}
examples=[];first_bad=[]
for w in words:
    Q=len(w);N=Q+1;b=1000*N*N;x=100*(b+N)*N;H=[0];B=[0]
    for z in w:H.append(H[-1]+(1 if z=='A'else-1));B.append(B[-1]+H[-1])
    free=[];bad=[]
    for q,z in enumerate(w):
        if z=='A':
            if mode=='discovery':
                sources=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
            else:
                sources=[];mass=area=0
                for u in range(q-1,-1,-1):
                    sg=1 if w[u]=='A'else-1;mass+=sg;area+=(q-u)*sg
                    if mass==1 and area==0:sources.append(u)
            if not sources:free.append(q)
        else:
            v=q+1
            for u in range(v):
                is_I=H[u]==H[v];is_II=w[u]=='A'and H[u]-1==H[v]
                if is_I or is_II:
                    area_zero=(B[v]-B[u]==(v-u)*H[v])if mode=='discovery'else(sum(H[t]-H[v]for t in range(u+1,v+1))==0)
                    if is_I and area_zero:bad.append(('I',u,v))
                    if is_II and area_zero:bad.append(('II',u,v))
    pairs={(H[q]-1,(q+1)*(H[q]-1)-B[q])for q in free};K=len(pairs);assert K<=Q
    high={x,*[x+b*h+k for h,k in pairs]};assert len(high)==K+1
    L=b//2-K-1;assert L>=0
    outputs=[x+(b+i+1)*H[i]-B[i]for i in range(Q+1)]
    all_candidates=[x+(b+q+1)*(H[q]-1)-B[q]for q,z in enumerate(w)if z=='A']
    assert min(outputs+all_candidates)>b and max(high)<=b*(b+1)//2
    assert min(high)>b and L<b//2
    card=L+1+len(high);s=card-1;tri=b*(b+1)//2
    assert card==b//2+1<=b+1 and s==b//2 and x%2==tri%2
    assert max(L,max(high))<=tri and tri<=x+s*(2*b-s+1)
    assert x+s*(2*b-s+1)-tri==x+b*b//4
    # Keep the entire interval from the start; future free blockers stay in high.
    seen=set(high);value=x;mismatch=None
    for q,z in enumerate(w):
        c=value-(b+q+1);visited=(0<=c<=L)or c in seen
        actual='S'if c>0 and not visited else'A'
        if actual!=z:mismatch={'clock':q,'actual':actual,'expected':z};break
        value+=(-1 if actual=='S'else 1)*(b+q+1);seen.add(value)
        assert value==outputs[q+1]
    assert (mismatch is None)==(not bad),{'word':w,'bad':bad,'mismatch':mismatch}
    counts['words']+=1;counts['chronology_good']+=not bad;counts['chronology_bad']+=bool(bad)
    counts['all_filters_pass']+=1;counts['correct_exact_replay_or_negative']+=1
    row={'word':w,'N':N,'base':b,'current':x,'K':K,'initial_seen_interval':[0,L],
         'complete_high_seed':sorted(high),'exact_seen_cardinality':card,'s':s,
         'all_four_filters':True,'chronology_bad':bad,'first_replay_mismatch':mismatch}
    if Q<=1 or w.startswith('S'*(2*7+2))or len(examples)<3:examples.append(row)
    if bad and len(first_bad)<3:first_bad.append(row)
assert time.process_time()-start<.6
print(json.dumps({'all_pass':True,'mode':mode,'counts':counts,'examples':examples,'negative_controls':first_bad,
 'scope':'COMPUTED finite all-word controls; complete huge seed is exact interval+high set, not enumerated or claimed canonical',
 'internal_cpu_seconds':time.process_time()-start}))
