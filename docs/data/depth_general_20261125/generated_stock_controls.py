"""Fixed OLD controls and independent literal first-birth provenance, NEW predicates only."""
import json,random,time
t0=time.process_time();out=[]
w='SAAA'+'SSSSAAAASA';H=[0];B=[0];F=[0];S=E=0;first_bad=None;src={}
for q,e in enumerate(w):
 if e=='A':
  us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];src[q]=us;E+=bool(us);F.append(F[-1]+(not us))
 else:S+=1;F.append(F[-1])
 if S-E<1 and first_bad is None:first_bad=q+1
 H.append(H[-1]+(1 if e=='A'else-1));B.append(B[-1]+H[-1])
assert first_bad==4 and H[-1]==2 and F[4]==2
out.append({'control':'OLD E660 complete word, NEW whole-prefix-domain audit','word':w,'h':1,'first_bad_original_positive_state':first_bad,'final_H':H[-1],'required_return':1,'ALLfree_before_suffix':F[4],'original_actual_sources':src,'meaning':'Its suffix-positive A/free counter is not a whole-prefix-positive/return input to H01; never reset source/free at4'})
# Independent first-birth extraction from the largest discovery input; direct replay, all sources retained.
x0=96;b=0;density=.375;seed=101;Q=38;cut=17;cp=38;rng=random.Random(seed+1000003*x0+10007*b);V0={0,x0}
for v in range(1,2*x0+1):
 if v!=x0-b-1 and rng.random()<density:V0.add(v)
X=[x0];H=[0];B=[0];seen=set(V0);first={};F=[0];src={};word=[];S=E=0
for q in range(Q):
 n=b+q+1;c=X[-1]-n;e='S'if c>0 and c not in seen else'A';word.append(e)
 if e=='A':
  us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]];src[q]=us;E+=bool(us);F.append(F[-1]+(not us))
 else:S+=1;F.append(F[-1])
 assert S-E>=1;y=X[-1]+(n if e=='A'else-n)
 if y not in V0 and y not in first:first[y]=q+1
 seen.add(y);X.append(y);H.append(H[-1]+(1 if e=='A'else-1));B.append(B[-1]+H[-1])
h=word.index('A');lost={v:u for v,u in first.items()if u<=cut and X[cp]<=v<X[cut]}
assert h==6 and F[cut]==5 and len(lost)==7 and H[-1]==2-h and min(H[cut:])>=H[cut]
# Supporting age producer: any generated value below X(c) predates the last lower-height state.
r=max(q for q in range(cut)if H[q]<H[cut]);assert all(u<=r for u in lost.values())
out.append({'control':'largest NEW discovery input checked by independent literal first births','V0':sorted(V0),'word':''.join(word),'cut':cut,'nextcut':cp,'h':h,'F_before':F[cut],'Lgen':len(lost),'generated_lost_births':lost,'last_lower_state_before_cut':r,'supporting_age_producer':'holds here, not free-charge proof or fresh holdout'})
# OLD E774 strongest seed-padding family at head-end cut: generated loss is exactly empty.
k=15;l=3*k;b=5*k*k-k-2;x=10*l*l;I=x+2*b-1;y=x-(4*k*k-5*k+1);base=b-2
C=lambda j:x+(j-2)*b+j*(j-3)//2
V0={0,I,*[C(j)for j in range(1,l+1)if j!=3],x-l*l-b-2*l-1,x-l*l-1,*range(y,x)}
head=[I,I-(base+1),I-(base+1)-(base+2)];assert head[-1]==x
G={v for v in head[1:]if v not in V0};assert not any(y<=v<x for v in G)
out.append({'control':'OLD E774 k15, NEW generated-versus-seed-loss predicate','generated_loss_at_cut2':0,'whole_stock_loss':4*k*k-5*k-1,'meaning':'old whole-stock no-go does not refute the seed-separated candidate'})
print(json.dumps({'all_pass':True,'controls':out,'scope':'finite fixed-control audit, OLD evidence reused only for NEW provenance/scope predicate; no new general proof','worker_internal_cpu_seconds':time.process_time()-t0},indent=2))
