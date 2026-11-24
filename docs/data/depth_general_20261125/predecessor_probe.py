"""One-step coherent predecessor language; complete immutable collisions and numerical witness."""
import itertools,json,sys,time
start=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
def data(w):
    H=[0];B=[0]
    for z in w:H.append(H[-1]+(1 if z=='A'else-1));B.append(B[-1]+H[-1])
    return H,B
def violations(w,direct=False):
    H,B=data(w);bad=[];qualified=[]
    for v in range(1,len(w)+1):
        if w[v-1]!='S':continue
        for u in range(v):
            kinds=[]
            if H[u]==H[v]:kinds.append('I')
            if w[u]=='A'and H[u]-1==H[v]:kinds.append('II')
            if kinds:
                area=sum(H[t]-H[v]for t in range(u+1,v+1))if direct else B[v]-B[u]-(v-u)*H[v]
                for k in kinds:
                    qualified.append((k,u,v,area))
                    if area==0:bad.append((k,u,v))
    return bad,qualified
w='AAS'+'S'*6+'A'*6+'SASS';H,B=data(w)
bad,qualified=violations(w,direct=mode=='holdout');assert len(w)==19 and H[-1]==-1 and B[-1]==-20
assert not bad,{'word':w,'bad':bad}
prep={c:violations(c+w,direct=mode=='holdout')[0]for c in 'AS'}
assert ('I',0,20)in prep['A'] and ('I',0,4)in prep['S']
criteria=[]
for q,z in enumerate(w):
    if z!='S':continue
    if H[q]==2 and B[q]==q+1:criteria.append(('S',q,H[q],B[q]))
    if (H[q]==0 and B[q]==-q-1)or(H[q]==-1 and B[q]==-2*q-2):criteria.append(('A',q,H[q],B[q]))
assert any(c[0]=='A'for c in criteria)and any(c[0]=='S'for c in criteria)

small={'words':0,'admissible':0,'both_prepend_bad':0}
if mode=='discovery':
    for Q in range(9):
        for letters in itertools.product('AS',repeat=Q):
            z=''.join(letters);bb,_=violations(z);small['words']+=1
            if bb:continue
            hh,ar=data(z);small['admissible']+=1
            predS=any(c=='S'and hh[q]==2 and ar[q]==q+1 for q,c in enumerate(z))
            predA=any(c=='S'and((hh[q]==0 and ar[q]==-q-1)or(hh[q]==-1 and ar[q]==-2*q-2))for q,c in enumerate(z))
            assert bool(violations('S'+z)[0])==predS and bool(violations('A'+z)[0])==predA
            small['both_prepend_bad']+=predS and predA

# Complete original ALL-source census, independently reversed in holdout.
free=[];sources={}
for q,z in enumerate(w):
    if z!='A':continue
    if mode=='discovery':us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
    else:
        us=[];mass=area=0
        for u in range(q-1,-1,-1):
            s=1 if w[u]=='A'else-1;mass+=s;area+=(q-u)*s
            if mass==1 and area==0:us.append(u)
        us.reverse()
    sources[q]=us
    if not us:free.append(q)
N=len(w)+1;b=(100 if mode=='discovery'else 1000)*N*N;x=100*(b+N)*N
C={q:x+(b+q+1)*(H[q]-1)-B[q]for q in free};high={x,*C.values()};K=len(high)-1
assert len({(H[q]-1,(q+1)*(H[q]-1)-B[q])for q in free})==K
L=b//2-K-1 if mode=='holdout'else-1
seen=set(high);seed_high=sorted(high);trace=[x];value=x
for q,z in enumerate(w):
    c=value-(b+q+1);actual='S'if c>0 and not(0<=c<=L)and c not in seen else'A'
    assert actual==z
    value+=(-1 if actual=='S'else 1)*(b+q+1);seen.add(value);trace.append(value)
if mode=='holdout':
    size=L+1+len(high);s=size-1;tri=b*(b+1)//2
    assert size==b//2+1<=b+1 and x%2==tri%2 and max(high)<=tri and L<min(high)
    assert tri<=x+s*(2*b-s+1)
else:size=len(high)
assert time.process_time()-start<.6
print(json.dumps({'all_pass':True,'mode':mode,'word':w,'H':H,'B':B,'qualified_chronology_residuals':qualified,
 'word_chronology_violations':bad,'prepend_violations':prep,'criterion_events':criteria,'small_control_counts':small,
 'original_ALL_sources':sources,'original_free_clocks':free,'base':b,'current':x,
 'complete_seed_interval':[0,L]if L>=0 else None,'complete_seed_high':seed_high,'seed_cardinality':size,'greedy_trace':trace,
 'scope':'coherent initialized finite continuation; impossible to have one previously EXECUTED coherent step. Positive base alone is not a constructed past. Not C1.',
 'internal_cpu_seconds':time.process_time()-start}))
