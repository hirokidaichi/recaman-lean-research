"""New exact source-gain construction; both original histories are positive."""
from pathlib import Path
import ast,json,sys,time
OUT=Path(__file__).resolve().parent
tree=ast.parse((OUT/'coupled_source_family.py').read_text())
keep=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'construct','forward','reverse'}]
exec(compile(ast.Module(body=keep,type_ignores=[]),'frozen-coupled-family','exec'))

def check(N):
    padded,_,stage,P=construct(N)
    g=padded[P:];f=g[1:]
    Hg,Bg,sg,fg,pg=forward(g);Hf,Bf,sf,ff,pf=forward(f)
    assert pf and pg
    assert all(c=='S' for c in f[:2]) and f[2]=='A'
    assert all(c=='S' for c in g[:3]) and g[3]=='A'
    for w,src in [(f,sf),(g,sg)]:
        for q,c in enumerate(w):
            if c=='A':assert src[q]==reverse(w,q)
    gains=[q for q,c in enumerate(g) if q and c=='A' and sg[q] and not sf[q-1]]
    assert gains==[r['target'] for r in stage]
    assert all(sg[q]==[0] for q in gains)
    assert len(ff)-len(fg)==N
    # Strong prefix reserve predicted by the paper high-run/new-minimum argument.
    for k in range(2,len(g)+1):
        F=sum(q<k for q in fg)
        assert F-Hg[k]>=2,(N,k,F,Hg[k])
    lowf=[q for q in ff if Hf[q]<=Hf[2]+1]
    lowg=[q for q in fg if Hg[q]<=Hg[3]+1]
    assert [q+1 for q in lowf]==lowg
    result={'N':N,'f_length':len(f),'g_length':len(g),'genuine_initial_runs':[2,3],
            'f_positive':pf,'g_positive':pg,'f_free':len(ff),'g_free':len(fg),
            'supply_gain':N,'new_source':0,'gain_targets':gains,
            'low_free_unchanged':len(lowf),'min_g_deficit_after_second_clock':
                min(sum(q<k for q in fg)-Hg[k] for k in range(2,len(g)+1))}
    if N==2:result.update(f=f,g=g,f_sources={q:ss for q,ss in enumerate(sf) if ss},g_sources={q:ss for q,ss in enumerate(sg) if ss})
    return result

mode=sys.argv[1];t=time.process_time()
rows=[check(n) for n in ([2,3] if mode=='discovery' else [4,7])]
(OUT/('padding-gain-'+mode+'-summary.json')).write_text(json.dumps({'mode':mode,'rows':rows,'cpu_seconds':time.process_time()-t},indent=2)+'\n')
print(json.dumps({'mode':mode,'rows':[{k:v for k,v in r.items() if k not in ['f','g','f_sources','g_sources']} for r in rows],'cpu_seconds':time.process_time()-t},indent=2))
