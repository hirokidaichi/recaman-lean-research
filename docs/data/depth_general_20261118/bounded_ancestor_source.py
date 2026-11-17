"""Fixed depth4/top2/h1 source-prefix wallet obstruction, all-N formula."""
from pathlib import Path
import ast,json,sys,time,hashlib
OUT=Path(__file__).resolve().parent
tree=ast.parse((OUT/'coupled_source_family.py').read_text())
keep=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'forward','reverse'}]
exec(compile(ast.Module(body=keep,type_ignores=[]),'frozen-original-source-checkers','exec'))

def construct(N):
    w='SASSSAA';stages=[]
    for j in range(N):
        psi=len(w);assert psi%3==1 and psi%4==3
        k=(2*psi-8)//3;assert k>=2 and 3*k==2*psi-8
        next0=psi+52+16*k
        a=next(a for a in range(3) if (next0+4*a)%3==1)
        w+='AA'+'AS'*k+'AS'
        q=len(w);assert q==psi+4+2*k
        w+='AS'
        for height in range(1,-4,-1):
            if height==-2:w+='AS'*a
            if height==-3:w+='AS'*(19+7*k+a)
            w+='S'
        w+='AAA'
        assert len(w)==next0+4*a
        stages.append({'j':j,'psi':psi,'k':k,'a':a,'target':q,'next_psi':len(w)})
    return w[:stages[-1]['target']+1],stages

def check(N):
    w,st=construct(N);H,B,src,free,positive=forward(w)
    assert positive and w[:2]=='SA' and min(H)>=-4 and max(H)<=2
    assert [q for q in free if q<=4]==[1]
    low=[q for q in free if H[q]<=0]
    D=[q for q,c in enumerate(w) if c=='A' and H[q]==1 and src[q] and all(u<1 for u in src[q])]
    assert D==[r['target'] for r in st]
    rows=[];queries=set([1,5,6])
    for row in st:
        q=row['target'];a=row['psi'];b=a+1
        assert src[q]==[0] and src[a]==[4]
        assert a==max(x for x in range(1,q) if w[x]=='A' and H[x]==-1)
        assert b==max(x for x in range(1,q) if w[x]=='A' and H[x]==0)
        short=w[a-3:a]=='SAA'
        assert short==(row['j']==0)
        if row['j']:
            assert not short;rho=1
        else:
            assert not src[b];rho=b
        queries.update([q,a,b])
        rows.append(dict(row,low_image=a,high_image=b,image_sources=src[a],target_sources=src[q],rho=rho))
    full=len(w)<=3000
    if full:
        queries.update(q for q,c in enumerate(w) if c=='A')
    for q in queries:assert src[q]==reverse(w,q)
    assert len(low)>=N+2
    result={'N':N,'length':len(w),'genuine_h':1,'height_band':[min(H),max(H)],
            'positive':positive,'D_near':len(D),'F_low':len(low),'prefix_wallet':[1],
            'common_local_source':4,'source_prefix_load':N-1,'rows':rows,
            'literal_reverse_queries':len(queries),'all_A_reverse_checked':full,
            'word_sha256':hashlib.sha256(w.encode()).hexdigest()}
    if N==2:result.update(word=w,H=H,B=B,all_sources={q:ss for q,ss in enumerate(src) if ss},low_free=low)
    return result

mode=sys.argv[1];start=time.process_time();rows=[check(n) for n in ([2,3] if mode=='discovery' else [4])]
(OUT/('bounded-ancestor-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-start},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':[{k:r[k] for k in ['N','length','genuine_h','height_band','D_near','F_low','source_prefix_load','all_A_reverse_checked']} for r in rows],'cpu_seconds':time.process_time()-start},indent=2))
