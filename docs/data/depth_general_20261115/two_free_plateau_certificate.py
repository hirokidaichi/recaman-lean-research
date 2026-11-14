"""Fixed certificates for an all-N PAPER construction, never a finite proof of no-go."""
import hashlib, json, math, sys, time
from collections import defaultdict

started=time.process_time()
def guard():
    if time.process_time()-started>0.70:
        raise RuntimeError('cooperative CPU stop before2-second OS limit')

def profile(w):
    h=[0];b=[0]
    for i,c in enumerate(w):
        h.append(h[-1]+(1 if c=='A' else -1));b.append(b[-1]+h[-1])
        if i%8192==0:guard()
    return h,b

def mass_area(w):
    h,b=profile(w);return h[-1],b[-1]

def construct(N):
    assert N>=1
    x='AAAA'; c0=-3; seeds=[]
    # The suffix-relative source areas are independent of the eventual prefix length.
    for j in range(N-1):
        for off,c,goal in [(7,-1,-8*j-6),(6,-2,-16*j-11),(5,-3,-24*j-15)]:
            connector='A'*(c0-c) if c<c0 else 'S'*(c-c0)
            x=connector+x;c0=c
            _,a=mass_area(x)
            loops=('AS'*(goal-a)) if a<=goal else ('SA'*(a-goal))
            x=loops+x
            assert mass_area(x)==(1-c,goal)
            seeds.append({'j':j,'offset':off,'distance_to_T':len(x),'height':c,'area':goal})
            guard()
    x='A'*(c0+3)+x;c0=-3
    hx,bx=profile(x);D=3*len(x)-bx[-1]
    assert D>=2 and hx[-1]==4
    m=max(2,math.isqrt(D+35))
    while m*m-7-D<28:m+=1
    E=m*m-7-D;bb=(3*E)%5;aa=(E-7*bb)//5
    assert aa>=0 and 5*aa+7*bb==E
    p='SAAAS'+'SA'*(D+3)+'S'*4+x
    assert mass_area(p)==(1,0)
    h=1;cut=2;T=h+len(p)
    word='S'*h+p+'ASSSSAAA'*(N-1)+'A'
    assert len(word)<600000
    return word,h,cut,T,seeds,{'N':N,'unused_old_hill_parameter':m,'D':D,'seed_length':len(x),'P_length':len(p),'length':len(word),'loader':'SAAAS(SA)^(D+3)S4','fixed_depth_cap':5}

def backward_sources(w,H,q):
    area=0;out=[]
    for u in range(q-1,-1,-1):
        area+=(q-u)*(1 if w[u]=='A' else -1)
        if H[u]==H[q]-1 and area==0:out.append(u)
        if u%8192==0:guard()
    return sorted(out)

def check(N,mode):
    w,h,cut,T,seeds,out=construct(N);H,B=profile(w)
    assert max(H[1:])<=1 and min(H)>=-5
    assert w[:4]=='SSAA' and backward_sources(w,H,2)==[] and backward_sources(w,H,3)==[]
    selected=[T+8*j for j in range(N)]
    plateau_A=[q for q in range(T,selected[-1]+1) if w[q]=='A']
    if mode=='discovery':
        index=defaultdict(list);sources={};free=[];A=S=E=0
        for q,c in enumerate(w):
            if c=='A':
                ss=index.get((H[q]-1,B[q]-q*(H[q]-1)),[])
                if ss:sources[q]=ss.copy();E+=1
                else:free.append(q)
                A+=1
            else:S+=1
            assert E+1<=S
            index[(H[q],B[q]-q*H[q])].append(q)
            if q%8192==0:guard()
        assert all(sources.get(q)==[h] for q in selected)
        assert not [q for q in free if T<=q<=selected[-1]]
        latest=max(q for q in free if q<T)
        out.update(A=A,S=S,actual=E,free=len(free),latest_free=latest,load=N)
    else:
        sources={q:backward_sources(w,H,q) for q in plateau_A}
        assert all(sources[q] for q in plateau_A)
        assert all(sources[q]==[h] for q in selected)
        out.update(plateau_A=len(plateau_A),exclusive_targets=len(selected),all_sources_reverse_checked=True)
    for seed in seeds:
        q=T+8*seed['j']+seed['offset'];u=T-seed['distance_to_T']
        assert H[u]==H[q]-1 and B[q]-B[u]-(q-u)*H[u]==0
    zeros=[q for q in range(h,selected[-1]+1) if H[q]==-h and B[q]-B[h]-(q-h)*(-h)==0]
    assert zeros==[h]
    out.update(source=h,cut=cut,T=T,targets=selected,word_sha256=hashlib.sha256(w.encode()).hexdigest(),prefix_height_cap_one_two_initialfree=True)
    print(json.dumps(out),flush=True);guard()

for D in [2,3,11,100]:
    jword='SAAAS'+'SA'*(D+3)+'S'*4
    jh,jb=profile(jword)
    assert (jh[-1],jb[-1])==(-3,D)
    assert min(jh)>=-3 and max(jh)<=2
    assert [i for i in range(len(jh)) if jh[i]==0 and jb[i]==0]==[0]
mode=sys.argv[1]
for N in ([1,2] if mode=='discovery' else [3]):check(N,mode)
print(json.dumps({'mode':mode,'worker_process_cpu_seconds':time.process_time()-started,'scope':'fixed finite certificate; all-N proof is PAPER, not a fresh-prefix holdout'}))
