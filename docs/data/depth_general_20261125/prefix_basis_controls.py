"""H02 new primal-basis transport, ALL-prefix tests; declarations explicitly separate from EndN."""
from fractions import Fraction as Q
import json,time
t0=time.process_time()
def rs(H):
    r=[1]
    for h in range(1,H+1):r.append(sum((2*d-3)*r[h-d] for d in range(2,h+1)))
    return r
def construct(H,t,M):
    r=rs(H);A=[1+M*r[h-t] if h>=t else 1 for h in range(H+1)]
    F=[1+M*(h==t) for h in range(H+1)];E=[A[h]-F[h]for h in range(H+1)]
    w=list('S'*(H+2));marks={}
    for h in range(H+1):
        for j in range(A[h]):
            marks[len(w)]=(h,j>=F[h]);w.append('A')
            if j<A[h]-1:w.append('S')
    w.extend('S'*(H+1));marks[len(w)]=(0,False);marks[len(w)+1]=(1,False);w.extend('AA')
    aa=[0]*(H+1);ff=[0]*(H+1);ee=[0]*(H+1);height=0;S=0;checks=0
    for q,c in enumerate(w):
        if c=='S':height-=1;S+=1
        else:
            h,sp=marks[q];assert height+(H+2)==h
            aa[h]+=1;ff[h]+=not sp;ee[h]+=sp;height+=1
        assert height<=-1 and S-sum(ee)>=1
        for h in range(H+1):
            assert ee[h]<=sum((2*(h-s)-3)*aa[s]for s in range(h-1));checks+=1
    assert height==-H and sum(ff)==H+3+M
    assert aa==[A[h]+(h in [0,1])for h in range(H+1)]
    assert ff==[F[h]+(h in [0,1])for h in range(H+1)] and ee==E
    return ''.join(w),aa,ff,ee,checks

count=checks=0
for H in range(2,6):
    for t in range(H+1):
        for M in [1,3,11]:
            w,A,F,E,n=construct(H,t,M);count+=1;checks+=n
            for weights in [[Q(1)]*(H+1),[Q(h+1)for h in range(H+1)],[Q(1,3**h)for h in range(H+1)]]:
                C=Q(3,2);r=rs(H);delta=sum(weights[h]*r[h-t]for h in range(t,H+1))-C*weights[t]
                B=sum(weights)+weights[0]+weights[1]
                actual_excess=sum(weights[h]*(A[h]-C*F[h])for h in range(H+1))
                assert actual_excess==M*delta-(C-1)*B

negative=[]
for H,weights in [(2,[Q(1)]*3),(4,[Q(h+1)for h in range(5)])]:
    t=0;C=Q(3,2);r=rs(H);delta=sum(weights[h]*r[h]for h in range(H+1))-C*weights[0];assert delta>0
    B=sum(weights)+weights[0]+weights[1];threshold=(C-1)*B/delta;M=threshold.numerator//threshold.denominator+1
    w,A,F,E,n=construct(H,t,M);assert sum(weights[h]*A[h]for h in range(H+1))>C*sum(weights[h]*F[h]for h in range(H+1))
    # Actual source ledger for the smallest declared counter only, all old source clocks retained.
    ledger=None
    if H==2:
        hh=[0];area=[0];actualE=0;falsely_supplied=[];currentH=0;marks=[]
        # Recover declared marking by the same explicit first-free ordering per stage.
        stage_A=[1+M*r[h]for h in range(H+1)];stage_F=[1+M*(h==0)for h in range(H+1)]
        q=H+2;declared={}
        for h in range(H+1):
            for j in range(stage_A[h]):declared[q]=j>=stage_F[h];q+=1+(j<stage_A[h]-1)
        declared[len(w)-2]=declared[len(w)-1]=False
        for q,ch in enumerate(w):
            if ch=='A':
                us=[u for u in range(q)if hh[q]==hh[u]+1 and area[q]-area[u]==(q-u)*hh[u]]
                actualE+=bool(us)
                if declared[q]and not us:falsely_supplied.append(q)
            currentH+=1 if ch=='A'else-1;hh.append(currentH);area.append(area[-1]+currentH)
        ledger={'actual_E':actualE,'actual_F':sum(A)-actualE,'falsely_declared_supplied_clocks':falsely_supplied}
        assert falsely_supplied
    negative.append({'H':H,'weights':list(map(str,weights)),'M':M,'word':w,'A':A,'declared_F':F,'declared_E':E,'actual_ledger':ledger})
assert time.process_time()-t0<.6
print(json.dumps({'all_pass':True,'basis_walks':count,'prefix_inequality_checks':checks,'weighted_negative_controls':negative,
 'scope':'finite weak-history/primal-basis controls, declared supply is not original EndN, no C1 counter',
 'internal_cpu_seconds':time.process_time()-t0}))
