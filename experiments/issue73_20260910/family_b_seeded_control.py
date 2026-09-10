#!/usr/bin/env python3
import hashlib,pathlib,subprocess,json
b=10;x=100;seed=[100,64,76,86,83,80];seen=set(seed);values=[x];signs=[];steps=[]
for t in range(12):
 n=b+t+1;c=x-n;S=c>0 and c not in seen
 signs.append(-1 if S else 1);reason='fresh' if S else 'nonpositive' if c<=0 else 'seen'
 x=x-n if S else x+n;seen.add(x);values.append(x);steps.append(dict(clock=n,candidate=c,sign='S' if S else 'A',reason=reason,value=x))
assert ''.join('A' if s==1 else 'S' for s in signs)=='SSAAASASASAA'
w=tuple(reversed(signs[:11]));m=M=0;lags=[]
for d,s in enumerate(w,1):
 m+=s;M+=d*s
 if m==1 and M==0:lags.append(d)
assert lags==[11]
print('protocol=H-20260910-24')
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
print('WITNESS='+json.dumps(dict(base=b,initial=100,seed=seed,values=values,steps=steps,word=''.join('A' if s==1 else 'S' for s in w),minimum_lag=lags[0])))
print('REFUTED: family B is compatible with exact finite-state greedy updates; canonical reachability unclaimed')
