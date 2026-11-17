"""Independent stronger input: h ends the genuine initial S run; no fallback."""
from pathlib import Path
import ast,json,sys,time,hashlib
OUT=Path(__file__).resolve().parent
tree=ast.parse((OUT/'coupled_source_family.py').read_text())
keep=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'forward','reverse'}]
exec(compile(ast.Module(body=keep,type_ignores=[]),'frozen-forward-reverse','exec'))

def construct(N):
    word='SASSSAA'+'A'*3+'S'*8+'A'*5
    rows=[]
    for j in range(N):
        r=7+8*j;a=r-7;psi=len(word)
        assert psi==32*j*j+48*j+23
        word+='AA'+'AS'*2+'A'*(r-2)+'S'*(r-2)
        q=len(word);assert q==32*j*j+64*j+39
        word+='AS'
        for height in range(1,-r-3,-1):
            if height==-2:word+='AS'*a
            if height==-3:word+='AS'*(a+21)
            word+='S'
        word+='A'*(r+2)
        rows.append(dict(j=j,r=r,psi=psi,target=q,next_psi=len(word)))
        assert len(word)==32*(j+1)**2+48*(j+1)+23
    P=8*N-1
    return 'S'*P+word[:rows[-1]['target']+1],P+1,rows,P

def check(N):
    w,h,stages,P=construct(N);H,B,src,free,positive=forward(w)
    assert w[h]=='A' and all(c=='S' for c in w[:h])
    assert positive and max(H[1:])<=-1 and len(w)==32*N*N+8*N+7
    for q,c in enumerate(w):
        if c=='A':assert src[q]==reverse(w,q),(N,q,src[q],reverse(w,q))
    low=[q for q in free if H[q]<=H[h]+1]
    target_set=[q for q,c in enumerate(w) if q>=h and c=='A' and H[q]-H[h]==2
                and src[q] and all(u<h for u in src[q])]
    rows=[]
    for st in stages:
        t=P+st['target'];a=P+st['psi'];b=a+1
        assert src[t]==[P] and src[a]==[P+4]
        assert a==max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h])
        assert b==max(q for q in range(h,t) if w[q]=='A' and H[q]==H[h]+1)
        assert w[a-3:a]!='SAA'
        before=[q for q in low if q<=P+4]
        assert before==[P+1]
        rows.append(dict(target=t,target_sources=src[t],a=a,b=b,psi_sources=src[a],rho=max(before)))
    assert target_set==[r['target'] for r in rows]
    assert len(low)>=N+1
    result={'N':N,'length':len(w),'h':h,'genuine_initial_run':True,'D_near':N,
            'source':P,'shared_local_source':P+4,'shared_rho':P+1,'load':N,
            'F_low':len(low),'total_free':len(free),'rows':rows,'positive':True,
            'word_sha256':hashlib.sha256(w.encode()).hexdigest()}
    if N==2:result.update(word=w,H=H,B=B,all_sources={q:ss for q,ss in enumerate(src) if ss},low_free=low)
    return result

mode=sys.argv[1];t=time.process_time()
rows=[check(n) for n in ([1,2] if mode=='discovery' else [3,5])]
(OUT/('genuine-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-t},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':[{k:r[k] for k in ['N','length','h','load','F_low','genuine_initial_run']} for r in rows],'cpu_seconds':time.process_time()-t},indent=2))
