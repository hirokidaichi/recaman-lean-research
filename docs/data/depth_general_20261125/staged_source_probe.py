"""H03 ALL original sources; forward discovery and independently reverse-weighted holdout."""
import itertools,json,random,sys,time

started=time.process_time();mode=sys.argv[1];assert mode in ['discovery','holdout']
def make(a):
    H=len(a)-1;m=H+2;word=list('S'*m);starts=[];targets={}
    for h,count in enumerate(a):
        starts.append(len(word))
        for j in range(count):
            targets[len(word)]=(h,j);word.append('A')
            if j<count-1:word.append('S')
    word.extend('S'*(H+1));word.extend('AA')
    return ''.join(word),targets,starts

def check(a,reverse=False,prehistory=''):
    H=len(a)-1;m=H+2;tail,targets,starts=make(a);n=len(prehistory);cut=n+m
    w=prehistory+tail;targets={q+n:v for q,v in targets.items()};starts=[q+n for q in starts];height=[0];B=[0]
    for ch in w:
        height.append(height[-1]+(1 if ch=='A'else-1));B.append(B[-1]+height[-1])
    assert max(x-height[n]for x in height[n+1:])==-1 and height[-1]-height[n]==2-m
    L=[0]*(H+1);delta=[0]*(H+1);E=D=S=0;literal=[]
    for q,ch in enumerate(w):
        if q<n:continue
        if ch=='S':S+=1;assert S-E>=1;continue
        if reverse:
            mass=area=0;us=[]
            for u in range(q-1,-1,-1):
                z=1 if w[u]=='A'else-1;mass+=z;area+=(q-u)*z
                if mass==1 and area==0:us.append(u)
            us.reverse()
        else:
            us=[u for u in range(q)if height[q]==height[u]+1 and B[q]-B[u]==(q-u)*height[u]]
        prediction=[]
        if q in targets:
            h,j=targets[q]
            if h>=2:
                K=sum((2*(h-t)-3)*a[t]for t in range(h-1));r=a[h-1]+3*j
                if r==K:
                    if not prehistory:prediction.append(m-h+1)
                    delta[h]+=1
                if r<a[h-2]:
                    i=a[h-2]-r-1;assert 0<=i<a[h-2]-1
                    prediction.append(starts[h-2]+2*i+1);L[h]+=1
        if prehistory:
            assert [u for u in us if u>=cut]==prediction,{'prehistory':prehistory,'a':a,'clock':q,'actual':us,'local_prediction':prediction}
        else:
            assert us==prediction,{'a':a,'clock':q,'target':targets.get(q),'actual':us,'prediction':prediction}
        E+=bool(us);D+=bool(us)and all(u<cut for u in us)
        assert S-E>=1
        literal.append({'q':q,'source_clocks':us,'stage':targets.get(q),'exclusive_before_cut':bool(us)and all(u<cut for u in us)})
    At=sum(a)+2;F=At-E
    assert E==sum(L)+D
    if not prehistory:assert D==sum(delta)
    assert F+D>=H+3 and 2*At<=3*(F+D)-a[-1]-2
    assert 3*sum(L)<=sum(a[:-1])
    return {'a':a,'prehistory':prehistory,'cut':cut,'word':w,'A':At,'actual_E':E,'actual_F':F,'exclusive_before_cut_O':D,'exclusive_initial_head_O':D if not prehistory else None,'local_L':L,'head_delta':delta,'all_sources':literal}

if mode=='discovery':
    inputs=[list(a)for H in [2,3,4]for a in itertools.product(range(1,4),repeat=H+1)]
else:
    rng=random.Random(2026112503)
    inputs=[[rng.randrange(1,8)for _ in range(H+1)]for H in [5,6,7,8]for _ in range(10)]
count=targets_checked=Dzero=0;minimum_gap=None
for a in inputs:
    z=check(a,reverse=mode=='holdout');count+=1;targets_checked+=sum(a)+2;Dzero+=z['exclusive_initial_head_O']==0
    gap=z['actual_F']+z['exclusive_initial_head_O']-(len(a)+2)
    minimum_gap=gap if minimum_gap is None else min(gap,minimum_gap)
sharp=[]
for n in (range(1,9)if mode=='discovery'else range(9,17)):
    a=[2,1]*n+[1];z=check(a,reverse=mode=='holdout')
    assert z['actual_E']==n and z['actual_F']==2*n+3 and z['A']==3*n+3 and z['exclusive_initial_head_O']==0
    assert z['actual_F']==len(a)+2 and 2*z['A']==3*z['actual_F']-3
    sharp.append({k:z[k]for k in ['a','A','actual_E','actual_F','exclusive_initial_head_O']})
controls=[]
for a in [[7,1,7],[1,1,1,2,1,1],[2,1,1]]:
    z=check(a,reverse=mode=='holdout');controls.append(z)
assert controls[0]['actual_E']==3
assert controls[1]['actual_F']==6 and controls[1]['exclusive_initial_head_O']==2
assert controls[2]['actual_F']==5 and controls[2]['exclusive_initial_head_O']==0
prehistory_controls=[]
if mode=='holdout':
    for U in ['A','SAA','AASAS','SSAAA','SAAASSSSAAAASA']:
        for a in [[1,1,1],[7,1,7],[2,1,2,1,1]]:
            z=check(a,reverse=True,prehistory=U)
            prehistory_controls.append(z)
assert time.process_time()-started<.6
print(json.dumps({'all_pass':True,'mode':mode,'complete_words_checked':count,'original_A_targets_checked':targets_checked,
 'Ozero_words':Dzero,'minimum_debt_gap':minimum_gap,'sharp_family_controls':sharp,'negative_and_boundary_controls':controls,
 'full_prehistory_controls':prehistory_controls,
 'scope':'COMPUTED fixed structured word ranges, ALL original Nat0 sources; not canonical reachability or arbitrary padded histories',
 'internal_cpu_seconds':time.process_time()-started}))
