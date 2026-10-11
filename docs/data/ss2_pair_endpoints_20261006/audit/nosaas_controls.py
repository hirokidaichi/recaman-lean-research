import json
examples=[('p22','ASAAAAASASASASASASASSS',[(5,19),(18,31)],4),('p33','SASASSSAAAASASASASASASASASASASAAA',[(10,11),(31,31)],32)]
out=[]
for name,e,donors,clean in examples:
 p=len(e);assert all(''.join(e[(t+j)%p] for j in range(4))!='SAAS' for t in range(p))
 ds=[]
 for t,d in donors:
  assert e[t]=='A'; w=''.join(e[(t-j)%p] for j in range(1,d+1));m=M=0;hits=[]
  for j,b in enumerate(w,1):
   s=1 if b=='A' else -1;m+=s;M+=j*s
   if (m,M)==(1,0):hits.append(j)
  ss=sum(a==b=='S' for a,b in zip(w,w[1:]));old=max(j for j,b in enumerate(w,1) if b=='S')
  assert hits==[d] and ss==2
  ds.append(dict(phase=t,lag=d,word=w,P2_prefixes=hits,ss=ss,sigma=(t-old)%p,tail=d-old))
 assert ds[0]['sigma']==ds[1]['sigma']
 C=ds[0]['word'][:-1];X=ds[1]['word'][:-len(C)]
 assert ds[0]['tail']==1 and ds[1]['tail']==0 and ds[1]['word']==X+C
 assert X==('SA'*6+'A' if name=='p22' else 'AS'*10+'A')
 assert e[clean]=='A' and ''.join(e[(clean-j)%p] for j in (1,2,3))=='AAS'
 assert clean not in [t for t,_ in donors]
 out.append(dict(name=name,p=p,period=e,mass=e.count('A')-e.count('S'),cyclic_NoSAAS=True,donors=ds,X=X,clean_source=clean))
print(json.dumps(dict(status='PASS',controls=out),indent=2))
