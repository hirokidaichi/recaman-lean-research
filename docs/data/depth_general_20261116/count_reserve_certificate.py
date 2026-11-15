"""Finite checks of a new all-h reserve no-go. The all-h proof is paper."""
import sys,time,json
beg=time.process_time();mode=sys.argv[1];data=[]
for h in (range(2,25) if mode=='reverse' else range(25,65)):
    if time.process_time()-beg>.7:raise RuntimeError('cooperative stop before1 CPU OS cap')
    w='S'*h+'A'*(2*h)+'S'*(h-1)+'A';H=[0];B=[0]
    for a in w:H.append(H[-1]+(1 if a=='A' else -1));B.append(B[-1]+H[-1])
    srcs={};bykey={}
    for q,a in enumerate(w):
        if mode=='forward':
            src=bykey.get((H[q]-1,B[q]-q*(H[q]-1)),[]).copy()
        else:
            src=[];acc=0
            for t in range(q-1,-1,-1):
                acc+=H[t+1]
                if H[q]==H[t]+1 and acc-(q-t)*H[t]==0:src.append(t)
        if a=='A' and src:srcs[q]=src
        bykey.setdefault((H[q],B[q]-q*H[q]),[]).append(q)
    assert srcs=={h+2:[h-1],4*h-1:[0]},(h,srcs)
    E=S=0;U=V=0
    for k,a in enumerate(w,1):
        E+=int(k-1 in srcs);S+=int(a=='S');assert E+1<=S
        if k>h:U=max(U,E+1-(S-h))
    for q,src in srcs.items():
        assert all(t<h for t in src);V=max(V,H[q]-H[h]-1)
    assert U==2 and V==h
    F=w.count('A')-E;assert F==2*h-1 and E==2 and B[4*h-1]==0
    # All possible retained C: exact original supplier set, not a chosen witness.
    cuts=[]
    for C in range(h+1):
        retained=[q for q,src in srcs.items() if any(t>=h-C for t in src)]
        lost=2-len(retained)
        assert lost==(0 if C==h else 2 if C==0 else 1)
        ee=ss=0;positive=True
        for q in range(h-C,4*h):
            ee+=int(q in retained);ss+=int(w[q]=='S');positive&=ee+1<=ss
        assert positive==(C>=2), (h,C,positive)
        cuts.append({'C':C,'lost':lost,'positive':positive})
    data.append({'h':h,'actual':2,'free':F,'D':2,'U':U,'V':V,'unique_sources':srcs,'all_cuts_checked':len(cuts),'C2_lost':cuts[2]['lost']})
print(json.dumps({'mode':mode,'h_range':[data[0]['h'],data[-1]['h']],'cases':len(data),'all_formulas_passed':True,'examples':[data[0],data[-1]],'cpu_body_seconds':time.process_time()-beg,'scope':'finite verification; all-h analytic proof separate; no standard orbit or C1 counterexample'}),flush=True)
