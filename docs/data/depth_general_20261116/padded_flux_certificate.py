import sys,time,json
beg=time.process_time();mode=sys.argv[1];out=[]
for m in (range(1,9) if mode=='reverse' else range(9,25)):
 if time.process_time()-beg>.7:raise RuntimeError('cooperative CPU stop')
 pair=[]
 for w in ['SAAA'+'SSSSAAAA'*m,'SAAA'+'SSSAAAA'+'SSSSAAAA'*(m-1)]:
  H=[0];B=[0]
  for a in w:H.append(H[-1]+(1 if a=='A' else -1));B.append(B[-1]+H[-1])
  key={};E=[];srcs={}
  for q,a in enumerate(w):
   if mode=='forward':src=key.get((H[q]-1,B[q]-q*(H[q]-1)),[]).copy()
   else:
    src=[];area=0
    for t in range(q-1,-1,-1):
     area+=H[t+1]
     if H[q]==H[t]+1 and area-(q-t)*H[t]==0:src.append(t)
   if a=='A' and src:E.append(q);srcs[q]=src
   key.setdefault((H[q],B[q]-q*H[q]),[]).append(q)
  ee=ss=0
  for q in range(4,len(w)):
   ee+=int(q in E);ss+=int(w[q]=='S');assert ee+1<=ss
  pair.append((E,srcs,w[4:].count('A')-ee,H,B))
 ef,sf,ff,hf,bf=pair[0];eg,sg,fg,hg,bg=pair[1]
 assert [q for q in ef if q>=4]==[x for j in range(m) for x in [10+8*j,11+8*j]]
 assert [q for q in eg if q>=4]==[9+8*j for j in range(m)]
 assert ff==2*m and fg==3*m
 assert all(sf[11+8*j]==[0] for j in range(m))
 assert max(hf[8:])<=hf[8]+4 and max(hg[4:])<=hg[4]+1
 out.append({'m':m,'original_tail_actual':2*m,'new_tail_actual':m,'old_free':ff,'new_free':fg,'free_jump':m,'all_original_fourth_sources_0':True,'both_relative_positive':True})
print(json.dumps({'mode':mode,'m_range':[out[0]['m'],out[-1]['m']],'all_formulas_passed':True,'examples':[out[0],out[-1]],'cpu_body_seconds':time.process_time()-beg,'scope':'finite support for complete all-m paper, related fixed period not fresh holdout; not C1/standard orbit counter'}),flush=True)
