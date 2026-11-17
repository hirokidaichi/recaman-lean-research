"""Verify a new explicit coupled-source family, not a numerical absence search."""
from pathlib import Path
import json,sys,time,hashlib
OUT=Path(__file__).resolve().parent

def construct(N):
    # Normalized original source0 has H=0; local source2 has H=-2.
    word='SSSAA';stage=[]
    for j in range(N):
        r=4+6*j;psi=len(word);q=psi+2*r-2
        assert psi==18*j*j+18*j+5
        first='A'*r+'S'*(r-2)
        word+=first
        assert len(word)==q
        # This AS makes q a genuine original A without changing its window.
        word+='AS'
        a=(r-4)//2
        # Remaining descent from H=1 to H=-r-3, with compensated key loops.
        for height in range(1,-r-3,-1):
            if height==-2:word+='AS'*a
            if height==-3:word+='AS'*(a+7)
            word+='S'
        word+='A'*(r+2)
        stage.append({'j':j,'r':r,'psi':psi,'target':q,'next_psi':len(word),'a':a})
        assert len(word)==18*(j+1)**2+18*(j+1)+5
    padding=6*N-2
    # Last recovery after the final target is unnecessary for the finite witness.
    end=stage[-1]['target']+1
    return 'S'*padding+word[:end],padding+1,stage,padding

def forward(w):
    H=[0];B=[0];bank={};src=[];free=[];S=E=0;positive=True
    for q,c in enumerate(w):
        ss=list(bank.get((H[q]-1,B[q]-q*(H[q]-1)),[])) if c=='A' else []
        src.append(ss)
        if c=='A':
            E+=bool(ss)
            if not ss:free.append(q)
        else:S+=1
        positive=positive and E+1<=S
        bank.setdefault((H[q],B[q]-q*H[q]),[]).append(q)
        H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
    return H,B,src,free,positive

def reverse(w,q):
    mass=area=0;src=[]
    for k,c in enumerate(reversed(w[:q]),1):
        s=1 if c=='A' else -1;mass+=s;area+=k*s
        if mass==1 and area==0:src.append(q-k)
    return sorted(src) if w[q]=='A' else []

def check(N):
    w,h,stages,P=construct(N);H,B,src,free,positive=forward(w)
    assert positive and max(H[1:])<=-1
    # Independent literal source scan at EVERY A, not selected-source checking.
    for q,c in enumerate(w):
        if c=='A':assert src[q]==reverse(w,q),(N,q,src[q],reverse(w,q))
    low=[q for q in free if H[q]<=H[h]+1]
    rows=[]
    for st in stages:
        j=st['j'];t=P+st['target'];a=P+st['psi'];b=a+1
        assert src[t]==[P] and H[t]==H[h]+2
        assert a==max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h])
        assert b==max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h]+1)
        short=lambda q:q>=h+3 and w[q-3:q]=='SAA'
        psi=b if short(a) else a
        if j:
            assert not short(a) and src[a]==[P+2]
            assert not [q for q in low if q<=P+2]
            rho=min(q for q in low if q<psi)
            assert rho==P+3
        else:
            assert short(a) and not src[b];rho=b
        rows.append({'j':j,'target':t,'target_sources':src[t],'a':a,'b':b,
                     'psi':psi,'psi_sources':src[psi],'rho':rho})
    result={'N':N,'length':len(w),'h':h,'padding':P,'rows':rows,
            'shared_rho':P+3,'shared_load':N-1,'F_low':len(low),'total_free':len(free),
            'positive':positive,'max_nonempty_height':max(H[1:]),
            'word_sha256':hashlib.sha256(w.encode()).hexdigest()}
    if N==3:result.update(word=w,H=H,B=B,all_sources={q:ss for q,ss in enumerate(src) if ss},low_free=low)
    return result

mode=sys.argv[1];start=time.process_time()
rows=[check(n) for n in ([1,2,3] if mode=='discovery' else [4,7,11])]
(OUT/('coupled-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-start},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':[{k:r[k] for k in ['N','length','h','shared_load','F_low','positive']} for r in rows],'cpu_seconds':time.process_time()-start},indent=2))
