"""Exact finite primal/dual controls independent of the saturation-walk program."""
from fractions import Fraction as Q
import json, random, time

start = time.process_time()
def kernel(d): return 0 if d < 2 else 2*d-3
def inverse_column(H):
    r = [Q(1)]
    for h in range(1,H+1):
        r.append(sum((kernel(d)*r[h-d] for d in range(1,h+1)),Q(0)))
    return r
def optimal(H,C,r):
    v=[Q(1)]
    for n in range(1,H+1):
        v.append(max(Q(1),sum((r[d]*v[n-d] for d in range(2,n+1)),Q(0))/(C-1)))
    return v
def required_capacity(w,r):
    return max(sum((w[h]*r[h-t] for h in range(t,len(w))),Q(0))/w[t] for t in range(len(w)))

r=inverse_column(40)
assert r[:7]==[1,0,1,3,6,13,29]
assert all(r[n]==2*r[n-1]+r[n-3] for n in range(3,41))
records=[]; perturbations=0; primal_checks=0
for C in [Q(5,4),Q(3,2),Q(2),Q(5),Q(20),Q(4,3),Q(7,3),Q(11,2)]:
    v=optimal(24,C,r)
    assert all(v[n]>=v[n-1] for n in range(1,len(v)))
    for H in range(2,13):
        w=list(reversed(v[:H+1]))
        assert min(w)==1 and max(w)==v[H] and required_capacity(w,r)<=C
        if v[H]>1:
            wp=w.copy();wp[0]*=Q(99,100)
            assert required_capacity(wp,r)>C
            perturbations+=1
        # Every basis F=e_t is a nonnegative integer primal cone input.
        for t in range(H+1):
            A=[Q(0)]*t+r[:H-t+1]
            F=[Q(int(h==t)) for h in range(H+1)]
            assert all(A[h]-F[h]==sum((kernel(h-s)*A[s] for s in range(h)),Q(0)) for h in range(H+1))
            assert sum(w[h]*A[h] for h in range(H+1))<=C*w[t]
            primal_checks+=1
    records.append({'C':str(C),'optimal_distortion_H12':str(v[12]),
                    'v_first_10':list(map(str,v[:10]))})
v=optimal(40,Q(3,2),r)
assert v[:7]==[1,1,2,8,22,66,200]
assert all(v[n]==2*v[n-1]+2*v[n-2]+3*v[n-3] for n in range(5,41))
assert all(Q(2,9)*3**n<=v[n]<=Q(8,27)*3**n for n in range(2,41))

# Independent nongeometric weight profiles: infer their EXACT finite capacity from ALL primal basis columns.
rng=random.Random(2026112502);weights_checks=[]
for H in [2,5,8,11]:
    for _ in range(5):
        w=[Q(rng.randrange(1,30)) for h in range(H+1)]
        C=required_capacity(w,r);vv=optimal(H,C,r)
        assert max(w)/min(w)>=vv[H]
        weights_checks.append({'H':H,'weights':list(map(int,w)),'exact_capacity':str(C),
                               'spread':str(max(w)/min(w)),'lower_bound':str(vv[H])})

# Reverse weighted-area source test, separate formula from height_kernel_probe's forward prefix sums.
H=3;g=[1,1,1,4];w='S'*(H+2)+''.join('AS'*(g[h]-1)+'A' for h in range(H+1))+'S'*(H+1)+'AA'
height=[0]
for ch in w:height.append(height[-1]+(1 if ch=='A' else -1))
actual=[]
for q,ch in enumerate(w):
    if ch!='A':continue
    sources=[]
    for u in range(q):
        suffix=w[u:q]
        mass=sum(1 if c=='A' else -1 for c in suffix)
        area=sum((q-i)*(1 if w[i]=='A' else -1) for i in range(u,q))
        if mass==1 and area==0:sources.append(u)
    actual.append({'clock':q,'sources':sources})
assert sum(bool(z['sources']) for z in actual)==2
assert any(z['clock']==8 and z['sources']==[] for z in actual)
assert time.process_time()-start<.6
print(json.dumps({'all_pass':True,'records':records,'perturbed_optimal_profiles_refuted':perturbations,
 'primal_basis_checks':primal_checks,'nongeometric_checks':weights_checks,'reverse_EndN_H3':actual,
 'scope':'COMPUTED exact finite dual/basis controls and literal EndN negative control; all-height proof remains PAPER',
 'internal_cpu_seconds':time.process_time()-start}))
