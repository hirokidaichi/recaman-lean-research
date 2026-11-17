"""Independent reverse literal source audit; no constructor or Z3 imports."""
import json,hashlib,time,itertools
from pathlib import Path
P=Path(__file__).resolve().parent
start=time.process_time()

def scan(w):
    signs=[1 if c=='A' else -1 for c in w]
    H=[0]
    for a in signs:H.append(H[-1]+a)
    src={};free=[]
    for q,c in enumerate(w):
        if c!='A':continue
        mass=area=0;ss=[]
        for s in range(q-1,-1,-1):
            mass+=signs[s];area+=(q-s)*signs[s]
            if mass==1 and area==0:ss.append(s)
        src[q]=list(reversed(ss))
        if not ss:free.append(q)
    return H,src,free

def domain(w,h,T,M):
    H,src,free=scan(w)
    assert w[:h]=='S'*h and w[T:]=='ASSSSAAA'*M+'A'
    E=S=0
    for q,c in enumerate(w):
        S+=c=='S';E+=c=='A' and bool(src[q]);assert E+1<=S
    assert all(src[T+8*j]==[h-1] for j in range(M+1))
    assert all(src[q] for q in range(T,len(w)) if w[q]=='A')
    low=[q for q in free if q<T and H[q]<=1-h]
    return H,src,free,low

checked=[]
for name in ['discovery-best-M3.json','discovery-best-M4.json','holdout-best-M5.json','holdout-best-M7.json']:
    r=json.loads((P/name).read_text());w=r['word'];h,T,M=r['h'],r['T'],r['M']
    H,src,free,low=domain(w,h,T,M)
    assert low==r['low_free_clocks'] and len(low)==r['low_free']
    assert len(free)==r['total_free'] and sum(q<T for q in free)==r['prehistory_free']
    assert hashlib.sha256(w.encode()).hexdigest()==r['word_sha256']
    for row in r['external']:assert src[row['q']]==row['sources']
    selected=sorted(src[T+8*j+5][0] for j in range(M))
    assert all(v-u>=12 and (v-u)%4==0 for u,v in zip(selected,selected[1:]))
    checked.append({'certificate':name,'length':len(w),'M':M,'low_free':len(low),'all_A_sources_reverse_checked':True,'first_family_source_gaps':[v-u for u,v in zip(selected,selected[1:])]})
    print(json.dumps(checked[-1]),flush=True)

# Boundary and weakened-history controls for the separate paper lemmas.
domain('SSAAA',2,4,0)
H,src,free=scan('SSSSAAAA')
assert min(H)==-4 and H[8]==0 and len([q for q in free if H[q]<=-1])==3
assert free==[4,5,7]
for w,area in [('AAAASSSAASSS',24),('AAAASSSS',16)]:
    height=total=0
    for c in w:height+=1 if c=='A' else -1;total+=height
    assert height==0 and total==area

# A fixed small falsifier for the new crossing lemma, not a D/free census.
tested=0
for bits in itertools.product('SA',repeat=11):
    w='S'+''.join(bits);H,src,free=scan(w)
    for h in range(1,5):
        if w[:h]!='S'*h:continue
        for T in range(h,13):
            if H[T]>=2-h and min(H[:T])<=-h-2:
                tested+=1
                assert len([q for q in free if q<T and H[q]<=1-h])>=3
print(json.dumps({'small_crossing_instances':tested,'ranges':'all2048 length12 words startingS, h1..4, T<=12; reused prefix space, not fresh holdout','counterexample':False,'cpu_seconds':time.process_time()-start,'completed_certificates':len(checked),'controls':'M0; sharp3free S4A4; sharp12/8 source-spacing bridges'}),flush=True)
