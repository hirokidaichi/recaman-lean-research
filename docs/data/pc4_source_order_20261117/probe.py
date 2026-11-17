"""Falsify two newly frozen structural lemmas, keeping every original source."""
import itertools,json,sys,time
from pathlib import Path
P=Path(__file__).resolve().parent
START=time.process_time()
COUNTS={'words':0,'depth_cases':0,'last_minimum_cases':0,'floor_visit_cases':0}
EXAMPLES={}

def literal(w):
    sign=[1 if x=='A' else -1 for x in w];H=[0];src={};free=[]
    for x in sign:H.append(H[-1]+x)
    for q,x in enumerate(w):
        if x!='A':continue
        mass=area=0;ss=[]
        for u in range(q-1,-1,-1):
            mass+=sign[u];area+=(q-u)*sign[u]
            if mass==1 and area==0:ss.append(u)
        src[q]=ss
        if not ss:free.append(q)
    return H,src,free

def fail(kind,w,**kw):
    out={'kind':kind,'word':w,**kw}
    (P/('counter-'+sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2)+'\n')
    raise AssertionError(json.dumps(out))

def check(w,hs):
    COUNTS['words']+=1
    H,src,free=literal(w);free=set(free)
    A=[0];positive=[True];S=E=0
    for q,x in enumerate(w):
        A.append(A[-1]+(x=='A'));S+=x=='S';E+=x=='A' and bool(src[q])
        positive.append(positive[-1] and E+1<=S)
    hs=[h for h in hs if h<=len(w) and w[:h]=='S'*h]
    low={h:[0] for h in hs}
    for h in hs:
        for q in range(len(w)):low[h].append(low[h][-1]+(q in free and H[q]<=1-h))
    for T in range(1,len(w)+1):
        m=min(H[:T+1])
        for floor in range(m-2,m+1):
            c=floor+2
            if H[T]<=c:continue
            visits=[q for q in range(T) if H[q]==c]
            wallet=[q for q in free if q<T and H[q]<=c]
            COUNTS['floor_visit_cases']+=1
            if len(visits)>len(wallet):fail('B-floor-visits',w,T=T,m=floor,visits=visits,wallet=wallet)
        for h in hs:
            if T<h or not positive[T] or H[T]!=2-h or low[h][T]>3:continue
            COUNTS['depth_cases']+=1
            if m<-h-4:fail('A-depth',w,T=T,h=h,m=m,low_free=low[h][T])
            if m<=-h-2:
                COUNTS['last_minimum_cases']+=1
                v=max(i for i in range(T+1) if H[i]==m)
                R=next(i for i in range(v+1,T+1) if H[i]==2-h)
                bad=[q for q in free if q<R and H[q]>1-h]
                if A[v]>1 or bad or A[R]>7:
                    fail('A-prefix-interface',w,T=T,h=h,m=m,v=v,R=R,A_before_min=A[v],high_free_before_return=bad,A_R=A[R])
                EXAMPLES.setdefault('last_minimum',{'word':w,'h':h,'T':T,'m':m,'v':v,'R':R,'A_before_min':A[v],'A_R':A[R],'low_free':low[h][T]})
    if time.process_time()-START>3.5:raise RuntimeError('cooperative3.5CPU stop')

mode=sys.argv[1]
if mode=='discovery':
    for bits in itertools.product('SA',repeat=12):check(''.join(bits),range(1,5))
elif mode=='holdout':
    for h,d,r in itertools.product((2,7,19),(0,4,5,8),(3,17,41)):
        for order in (0,1):
            deep='S'*d+'A'*(d+2);hill='A'*r+'S'*r
            check('S'*h+(deep+hill if order==0 else hill+deep),(h,))
    for h,r in itertools.product((2,7,19),(6,17,65,129)):
        w='S'*h+'A'*r+'S'*(r-2);check(w,(h,))
        H,src,free=literal(w)
        assert H[-1]==2-h and len([q for q in free if H[q]<=1-h])==2 and len(free)==r-1
    # Terminal-height guard is essential for B; this is not a parent counter.
    H,src,free=literal('S')
    assert min(H)>=-2 and sum(x==0 for x in H[:-1])==1 and len(free)==0 and H[-1]<0
    EXAMPLES['dropped_terminal_guard']={'word':'S','T':1,'m':-2,'visits':1,'wallet':0,'parent_counter':False}
    EXAMPLES['unbounded_high_free_family']='S^h A^r S^(r-2), h>=1/r>=3: low free2; total free r-1; no whole-prefix rank3 substitution'
else:raise ValueError(mode)
out={'mode':mode,'counts':COUNTS,'examples':EXAMPLES,'counterexample_found':False,'cpu_seconds':time.process_time()-START,'evidence':'COMPUTED finite controls, not an arbitrary-length proof'}
(P/(mode+'-summary.json')).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
