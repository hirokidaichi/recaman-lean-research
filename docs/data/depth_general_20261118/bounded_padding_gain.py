"""New four-free loader; old finite suffix preloading is cited input."""
from pathlib import Path
import ast,json,sys,time,hashlib
OUT=Path(__file__).resolve().parent
tree=ast.parse((OUT/'coupled_source_family.py').read_text())
keep=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'forward','reverse'}]
exec(compile(ast.Module(body=keep,type_ignores=[]),'frozen-independent-source-checkers','exec'))

def mass_area(w):
    h=b=0
    for c in w:h+=1 if c=='A' else -1;b+=h
    return h,b

def seed(N):
    x='AAAA';c0=-3
    for j in range(N-1):
        for off,c,goal in [(7,-1,-8*j-6),(6,-2,-16*j-11),(5,-3,-24*j-15)]:
            x=('A'*(c0-c) if c<c0 else 'S'*(c-c0))+x;c0=c
            _,area=mass_area(x)
            x=('AS'*(goal-area) if area<=goal else 'SA'*(area-goal))+x
            assert mass_area(x)==(1-c,goal)
    x='A'*(c0+3)+x
    _,area=mass_area(x);D=3*len(x)-area
    assert D>=2
    return x,D

def check(N):
    x,D=seed(N);k=(D+10)%3;l=(D+10-k)//3
    prefix='SSAASAA'+'SA'*k+'AS'*l+'S'*4+x
    g=prefix+'ASSSSAAA'*(N-1)+'A';f=g[1:];T=len(prefix)
    assert len(g)<600000
    Hg,Bg,sg,fg,pg=forward(g);Hf,Bf,sf,ff,pf=forward(f)
    assert pf and pg and min(Hg)>=-4 and max(Hg)<=2
    assert f[:6]=='SAASAA' and g[:7]=='SSAASAA'
    assert not any(sg[q] for q in [2,3,5,6])
    assert not any(sf[q] for q in [1,2,4,5])
    zeros=[q for q in range(len(g)) if Hg[q]==0 and Bg[q]==0]
    assert zeros==[0]
    boundaries=[T+8*j for j in range(N)]
    assert all(sg[q]==[0] and not sf[q-1] for q in boundaries)
    gains=[q for q,c in enumerate(g) if q and c=='A' and sg[q] and not sf[q-1]]
    assert len(ff)-len(fg)==len(gains)>=N
    # Every plateau A and every source0-only gain is independently exhausted.
    queries=set([q for q in range(T,len(g)) if g[q]=='A']+gains+[2,3,5,6])
    for q in queries:
        assert sg[q]==reverse(g,q)
        if q:assert sf[q-1]==reverse(f,q-1)
    full_scan=len(g)<=3000
    if full_scan:
        for w,src in [(f,sf),(g,sg)]:
            for q,c in enumerate(w):
                if c=='A':assert src[q]==reverse(w,q)
    lowf=[q for q in ff if Hf[q]<=0]
    lowg=[q for q in fg if Hg[q]<=-1]
    assert [q+1 for q in lowf]==lowg
    result={'N':N,'f_length':len(f),'g_length':len(g),'seed_D':D,'loader_SA':k,'loader_AS':l,
            'height_g':[min(Hg),max(Hg)],'height_f':[min(Hf),max(Hf)],'positive_f':pf,'positive_g':pg,
            'free_f':len(ff),'free_g':len(fg),'gain_count':len(gains),'boundary_targets':boundaries,
            'gain_targets':gains,'low_free_equal':len(lowf),'literal_reverse_queries':len(queries),
            'every_A_reverse_checked':full_scan,'source0_all_clock_classification':zeros,
            'f_sha256':hashlib.sha256(f.encode()).hexdigest(),'g_sha256':hashlib.sha256(g.encode()).hexdigest()}
    if N==1:result.update(f=f,g=g)
    return result

mode=sys.argv[1];start=time.process_time();rows=[check(n) for n in ([1,2] if mode=='discovery' else [3])]
(OUT/('bounded-padding-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-start},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-start},indent=2))
