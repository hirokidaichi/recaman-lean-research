#!/usr/bin/env python3
"""Independent dense-byte replay of the fixed H25 canonical witness."""
import collections,hashlib,json,pathlib,subprocess,time
TARGET=96911838
start=time.monotonic();seen=bytearray(1);seen[0]=1;x=0;ring=collections.deque(maxlen=20);A=S=0
print('protocol=H-20260910-25 independent fixed-witness verification',flush=True)
print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
for n in range(1,TARGET+1):
 c=x-n;subtract=c>0 and (c>=len(seen) or not seen[c])
 old=x
 if subtract:x=c;S+=1
 else:x+=n;A+=1
 if x>=len(seen):
  new=max(x+1,len(seen)*2)
  if new>2_000_000_000:raise RuntimeError('declared dense-byte cap exceeded')
  seen.extend(bytearray(new-len(seen)))
 seen[x]=1
 if n>TARGET-20:ring.append(dict(sign_time=n-1,clock=n,old=old,candidate=c,new=x,sign='S' if subtract else 'A'))
 if n==10_000_000:assert (x,A,S)==(20438710,5000014,4999986)
 if n%10_000_000==0:print('CHECKPOINT='+json.dumps(dict(through=n,value=x,A=A,S=S,elapsed_seconds=round(time.monotonic()-start,3))),flush=True)
trace=list(ring);t=TARGET-1
window=[r['sign'] for r in trace if t-11<=r['sign_time']<t][::-1]
assert ''.join(window)=='ASASASAAASS'
m=M=0;hits=[]
for d,s in enumerate(window,1):
 v=1 if s=='A' else -1;m+=v;M+=d*v
 if m==1 and M==0:hits.append(d)
assert hits==[11] and trace[-1]['sign']=='A' and trace[-1]['old']==299100441
old_supplier=next(r['old'] for r in trace if r['sign_time']==t-11)
assert trace[-1]['candidate']==old_supplier
print('VERIFIED='+json.dumps(dict(target_step=TARGET,minimum_lag=11,word=''.join(window),supplier_time=t-11,supplier_value=old_supplier,trace=trace,elapsed_seconds=round(time.monotonic()-start,3))),flush=True)
print('PASS: independent Python dense-byte replay agrees with C++ bitset witness',flush=True)
