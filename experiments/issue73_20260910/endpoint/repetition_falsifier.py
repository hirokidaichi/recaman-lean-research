#!/usr/bin/env python3
import hashlib,json,subprocess
from pathlib import Path

def data(w):
    m=M=ss=0;hits=[]
    for i,c in enumerate(w,1):
        s=1 if c=='A' else -1;m+=s;M+=i*s
        ss+=i>1 and w[i-2:i]=='SS'
        if m==1 and M==0:hits.append(i)
    return m,M,ss,hits

def main():
    print('protocol=H-20260910-29')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    print('command=python3 experiments/issue73_20260910/endpoint/repetition_falsifier.py')
    V='AASASASASSSA'
    assert data(V)[:3]==(0,-12,2)
    for K in range(33):
        W=V*K+'AAS';history='A'+W
        assert len(W)==12*K+3 and 'SAAS' not in history
        for k in range(K+1):
            small=V*k+'AAS';m,M,ss,hits=data(small)
            assert (m,M,ss)==(1,0,2*k)
            assert history[12*(K-k)]=='A'
            assert W[12*(K-k):]==small
            assert hits[0]==3
        print(('DISCOVERY=' if K<=8 else 'HOLDOUT=')+json.dumps(dict(K=K,sources=K+1,SS=2*K,length=len(W),minimum_lag_of_every_source=3,violations=0)))
    print('PASS: shared-endpoint multiplicity attains 1+SS/2; these chosen witnesses are not minimum for k>0')
if __name__=='__main__':main()
