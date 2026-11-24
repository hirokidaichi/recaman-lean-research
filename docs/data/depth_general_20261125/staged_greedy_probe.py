"""H04 literal chronological tests and FULL future-free seed; no canonical assumption."""
import json,sys,time
start=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
ns=range(1,6)if mode=='discovery'else[7,11,17,23]
records=[]
for n in ns:
    m=2*n+2;w='S'*m+'ASAA'*n+'A'+'S'*(2*n+1)+'AA';Q=len(w);assert Q==8*n+6
    H=[0];B=[0]
    for z in w:H.append(H[-1]+(1 if z=='A'else-1));B.append(B[-1]+H[-1])
    free=[];suppliers={};I=[];II=[];tests=0
    for q,ch in enumerate(w):
        if ch=='A':
            if mode=='discovery':
                us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
            else:
                us=[];mass=area=0
                for u in range(q-1,-1,-1):
                    s=1 if w[u]=='A'else-1;mass+=s;area+=(q-u)*s
                    if mass==1 and area==0:us.append(u)
                us.reverse()
            suppliers[q]=us
            if not us:free.append(q)
        else:
            v=q+1
            for u in range(v):
                tests+=1
                if H[u]==H[v]and B[v]-B[u]==(v-u)*H[v]:I.append((u,v))
                if w[u]=='A'and H[u]-1==H[v]and B[v]-B[u]==(v-u)*H[v]:II.append((u,v))
    assert not I and not II and len(free)==2*n+3 and sum(bool(u)for u in suppliers.values())==n
    b=100*(Q+1)**2;x=100*(b+Q+1)*(Q+1)
    X=[x+(b+i+1)*H[i]-B[i]for i in range(Q+1)]
    C={q:X[q]-(b+q+1)for q in suppliers}
    seed={0,x,*[C[q]for q in free]};seen=set(seed);value=x;trace=[]
    assert min(X)>0 and min(C.values())>0 and value in seen
    for q,ch in enumerate(w):
        candidate=value-(b+q+1);actual='S'if candidate>0 and candidate not in seen else'A'
        assert actual==ch,{'n':n,'clock':q,'actual':actual,'expected':ch}
        value+=(-1 if actual=='S'else 1)*(b+q+1);seen.add(value);assert value==X[q+1]
        trace.append(value)
    # Explicit paper coefficient formulas at EVERY S of the two non-head kinds.
    for i in range(n):
        v=m+4*i+2;u=m-2*i;rel=H[v]
        assert H[u]==rel and B[v]-B[u]-(v-u)*rel==1-6*i*i-i!=0
    for k in range(2*n+1):
        v=m+4*n+1+(2*n+1-k);u=m-k;rel=k-m
        assert H[v]==H[u]==rel
        assert B[v]-B[u]-(v-u)*rel==6*n*n+3*n+1-(6*n+2)*k!=0
    for i in range(n):
        u=m+4*i+1;k=2*i+1;r=n-i
        v=m+4*n+1+(2*n+1-k);rel=k-m
        assert H[v]==H[u]==rel
        assert B[v]-B[u]-(v-u)*rel==3*r*(2*r-1)>0
    pairs={(H[q]-1,(q+1)*(H[q]-1)-B[q])for q in free}
    records.append({'n':n,'Q':Q,'head':m,'actual_A':3*n+3,'original_E':n,'original_ALLfree':len(free),
      'distinct_free_candidate_classes':len(pairs),'coherent_seed_size_with_zero':len(seed),'base':b,'current':x,
      'complete_initial_seen':sorted(seed),'greedy_S_count':w.count('S'),'all_output_positive':True,
      'I_violations':I,'II_violations':II,'chronological_pair_tests':tests,
      'paper_area_formulas_checked':True,'source_sets':suppliers,
      'scope':'exact finite coherent greedy replay, complete future blockers, not canonical prehistory'})
assert time.process_time()-start<.6
print(json.dumps({'mode':mode,'all_pass':True,'records':records,'internal_cpu_seconds':time.process_time()-start,
 'scope':'COMPUTED fixed finite controls; all-n I/II proof is separate PAPER obligation; E759 constructor OLD input'}))
