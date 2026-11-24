"""NEW complete-State inverse and paid A-lookbehind on OLD stock-loss family; no old search rerun."""
import json,sys,time,itertools
start=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
tiny=0
if mode=='discovery':
    for mask in range(1,64):
        V={j for j in range(6)if mask>>j&1}
        for I in V:
            for a in [1,2,3]:
                predA=I>=a and I-a in V and(I-2*a<=0 or I-2*a in V)
                predS=I>0 and I+a in V;found=set()
                for pmask in range(64):
                    P={j for j in range(6)if pmask>>j&1}
                    if not P<=V or P|{I}!=V:continue
                    for J in P:
                        c=J-a;ch='S'if c>0 and c not in P else'A';Y=J+(-a if ch=='S'else a)
                        if Y==I and P|{Y}==V:found.add(ch)
                assert ('A'in found)==bool(predA)and('S'in found)==bool(predS)
                tiny+=1
cases=[(15,L)for L in [0,1,3,5]]if mode=='discovery'else[(35,L)for L in [2,10,35]]
records=[]
for k,L in cases:
    assert k%20==15 and k>=max(15,L)
    l=3*k;b=5*k*k-k-2;a=b-2;x=(10*L+90)*k*k;I=x+2*b-1
    gap=4*k*k-5*k+1;y=x-gap
    C=lambda j:x+(j-2)*b+j*(j-3)//2
    V0={0,I,*[C(j)for j in range(1,l+1)if j!=3],x-l*l-b-2*l-1,x-l*l-1,*range(y,x)}
    assert len(V0)==4*k*k-2*k+3 and I-a not in V0 and I+a not in V0
    p=lambda j:I-j*a+j*(j-1)//2
    extra={*[p(j)for j in range(1,L+1)],*[p(j+1)-1 for j in range(1,L+1)]}
    V=V0|extra;clock=a-L;current=p(L);assert current in V and min(extra,default=1)>0
    assert all(z>x or z<y for z in extra)
    N=len(V);s=N-1;tri=clock*(clock+1)//2
    assert N<=clock+1 and current%2==tri%2 and min(V)>=0 and max(V)<=tri
    assert tri<=current+s*(2*clock-s+1)
    word='A'*L+'SS'+'A'*l+'S'*l+'AA';seen=set(V);value=current;snapshots={}
    for q,ch in enumerate(word):
        c=value-(clock+q+1);actual='S'if c>0 and c not in seen else'A';assert actual==ch
        value+=(-1 if actual=='S'else 1)*(clock+q+1);seen.add(value)
        if q+1 in [L+2,L+2*l+3]:snapshots[q+1]=(value,sum(z<value for z in seen))
    X,Kold=snapshots[L+2];Y,Knext=snapshots[L+2*l+3]
    assert X==x and Y==y and Kold-Knext==gap-2
    H=[0];B=[0]
    for ch in word:H.append(H[-1]+(1 if ch=='A'else-1));B.append(B[-1]+H[-1])
    all_sources={};E=0
    for q,ch in enumerate(word):
        if ch!='A':continue
        if mode=='discovery':us=[u for u in range(q)if H[q]==H[u]+1 and B[q]-B[u]==(q-u)*H[u]]
        else:
            us=[];mass=area=0
            for u in range(q-1,-1,-1):
                sg=1 if word[u]=='A'else-1;mass+=sg;area+=(q-u)*sg
                if mass==1 and area==0:us.append(u)
            us.reverse()
        all_sources[q]=us;E+=bool(us)
    assert E==1 and all_sources[L+4]==[L+1]
    assert len(all_sources)-E==L+l+1
    St=Et=0
    for q,ch in enumerate(word[L:],L):
        if ch=='S':St+=1
        elif all_sources[q]:Et+=1
        assert St-Et>=1
    records.append({'k':k,'lookbehind_L':L,'starting_clock':clock,'starting_current':current,
       'complete_seed_recipe':'OLD translated V0 plus ALL p_j/c_j, interval retained','base_counter_clock':a,'x':x,
       'seed_count':N,'old_seed_count':len(V0),'extra_complete_values':sorted(extra),'four_filters_at_start':True,
       'all_greedy_steps':len(word),'whole_original_E':E,'whole_original_free':L+l+1,'tail_original_free':l+1,
       'Kold':Kold,'Knext':Knext,'stock_loss':Kold-Knext,'old_V0_predecessor_values':[I-a,I+a],
       'old_V0_has_neither_predecessor_current':True,'all_original_sources':all_sources})
assert time.process_time()-start<.6
print(json.dumps({'all_pass':True,'mode':mode,'tiny_inverse_cases':tiny,'records':records,
 'internal_cpu_seconds':time.process_time()-start,
 'scope':'NEW full-stock inverse/prefix predicate on OLD family. Whole A-prefix retained; strict positive is tail afterL, not whole0; no canonical past.'}))
