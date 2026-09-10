#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess

def main():
    print('protocol=H-20260910-27 union-map semantic control')
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest())
    word='SSAAASASASAAA';p=len(word)
    assert all(''.join(word[(t+i)%p] for i in range(4))!='SAAS' for t in range(p))
    records=[]
    for t in (11,12):
        m=M=0;hits=[]
        for d in range(1,p*(p+1)+1):
            sign=1 if word[(t-d)%p]=='A' else -1
            m+=sign;M+=d*sign
            if m==1 and M==0:hits.append(d)
        d=hits[0];back=''.join(word[(t-i)%p] for i in range(1,d+1))
        charge=(t-(2 if t==11 else 3))%p
        records.append(dict(phase=t,minimum_lag=d,backward_word=back,charge=charge,charge_sign=word[charge]))
    assert records[0]['minimum_lag']==11 and records[0]['backward_word']=='ASASASAAASS'
    assert records[1]['minimum_lag']==3 and records[1]['backward_word']=='AAS'
    assert records[0]['charge']==records[1]['charge']==9 and word[9]=='S'
    print('CONTROL='+json.dumps(dict(period=p,word=word,mass=word.count('A')-word.count('S'),sources=records)))
    print('PASS: the separate one-SS and clean maps collide; total capacity is not refuted')

if __name__=='__main__':main()
