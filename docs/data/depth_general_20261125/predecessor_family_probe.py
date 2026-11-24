"""Frozen all-r predecessor family controls; complete affine chronology inventory and FULL four-filter seed."""
import json,sys,time
start=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
rs=[6,7,9,10]if mode=='discovery'else[12,13,15,16]
out=[]
for r in rs:
    t=(r*r-4*r-9)//3;assert r>=6 and r%3 in [0,1] and 3*t==r*r-4*r-9
    w='AAS'+'S'*r+'A'*r+'SA'*t+'SS';Q=len(w);H=[0];B=[0]
    for ch in w:H.append(H[-1]+(1 if ch=='A'else-1));B.append(B[-1]+H[-1])
    assert Q==2*r+2*t+5 and H[-1]==-1 and B[-1]==-(Q+1)
    bad=[];free=[];sources={};pairs_S=[]
    for q,ch in enumerate(w):
        if ch=='A':
            if mode=='discovery':us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
            else:
                us=[];mass=area=0
                for u in range(q-1,-1,-1):
                    z=1 if w[u]=='A'else-1;mass+=z;area+=(q-u)*z
                    if mass==1 and area==0:us.append(u)
                us.reverse()
            sources[q]=us
            if not us:free.append(q)
        else:
            v=q+1;pairs_S.append((H[v],(v+1)*H[v]-B[v]))
            for u in range(v):
                same_I=H[u]==H[v];same_II=w[u]=='A'and H[u]-1==H[v]
                if same_I or same_II:
                    area=B[v]-B[u]-(v-u)*H[v]if mode=='discovery'else sum(H[k]-H[v]for k in range(u+1,v+1))
                    if area==0:bad.append((u,v,same_I,same_II))
    assert not bad and sum(bool(v)for v in sources.values())==1 and len(free)==r+t+1
    assert (1,0)in pairs_S and pairs_S[-1]==(-1,0)
    # Exact all-prior height-1 and candidate height-1 inventory, not selected suppliers only.
    last=Q
    old_output_keys=[(u,(u+1)*H[u]-B[u])for u in range(last)if H[u]==-1]
    old_A_keys=[(q,(q+1)*(H[q]-1)-B[q])for q,ch in enumerate(w)if ch=='A'and H[q]-1==-1]
    assert sorted(k for u,k in old_output_keys)==[-9,3*t+4]
    assert sorted(k for q,k in old_A_keys)==[-1,*[3*j for j in range(1,t+1)],3*t+3]
    N=Q+1;b=1000*N*N;x=100*(b+N)*N
    C={q:x+(b+q+1)*(H[q]-1)-B[q]for q in free};high={x,*C.values()};K=len(high)-1;L=b//2-K-1
    assert L>=0 and min(high)>b
    seen=set(high);value=x;minimum_S=None
    for q,ch in enumerate(w):
        c=value-(b+q+1);actual='S'if c>0 and not(0<=c<=L)and c not in seen else'A';assert actual==ch
        value+=(-1 if actual=='S'else 1)*(b+q+1);seen.add(value)
        if ch=='S':minimum_S=value if minimum_S is None else min(minimum_S,value)
    size=L+1+len(high);s=size-1;tri=b*(b+1)//2
    assert size==b//2+1<=b+1 and x%2==tri%2 and max(high)<=tri and tri<=x+s*(2*b-s+1)
    assert minimum_S>b>L
    out.append({'r':r,'t':t,'Q':Q,'word':w,'original_E':1,'original_ALLfree':len(free),
      'S_pair_plus1_zero':True,'final_pair_minus1_zero':True,'all_I_II_pass':True,
      'prior_output_keys_at_minus1':old_output_keys,'prior_candidate_keys_at_minus1':old_A_keys,
      'original_ALL_sources':sources,'base':b,'current':x,'complete_seen_interval':[0,L],
      'complete_high_seed':sorted(high),'exact_seed_size':size,'minimum_S_landing':minimum_S,'four_filters':True})
assert time.process_time()-start<.6
print(json.dumps({'all_pass':True,'mode':mode,'records':out,'internal_cpu_seconds':time.process_time()-start,
 'scope':'finite parameter controls, all-r proof separate; old r6 reused not fresh. Full numerical seed has no coherent executed predecessor.'}))
