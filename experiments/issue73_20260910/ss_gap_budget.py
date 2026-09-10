#!/usr/bin/env python3
import hashlib, itertools, json, pathlib, subprocess

def main():
    print('protocol=H-20260910-26',flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
    print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
    control=None
    for d in range(1,20):
        checked=language=overlap=0
        for bits in itertools.combinations(range(d),(d+1)//2):
            if d%2==0:break
            w=['S']*d
            for i in bits:w[i]='A'
            w=''.join(w)
            if 'S' not in w:continue
            gaps=[len(s) for s in w.split('S')]
            assert 'S'.join('A'*g for g in gaps)==w
            a,v=gaps[0],gaps[-1];inner=gaps[1:-1]
            k=sum(w[i:i+2]=='SS' for i in range(d-1))
            assert k==inner.count(0)
            extra=sum(max(g-1,0) for g in inner)
            assert a+v+extra==k+2
            big=sum(g>=3 for g in inner)
            assert a+v+2*big<=k+2
            checked+=1;overlap+='SSS' in w
            enlarged=sum(g>=2 for g in inner)
            if 'SAAS' not in w:
                assert all(g!=2 for g in inner)
                assert a+v+2*enlarged<=k+2
                language+=1
            elif a+v+2*enlarged>k+2 and control is None:
                control=dict(word=w,gaps=gaps,SS=k,enlarged=enlarged,lhs=a+v+2*enlarged,rhs=k+2)
        print(('DISCOVERY=' if d<=13 else 'HOLDOUT=')+json.dumps(dict(length=d,mass_one=checked,noSAAS=language,overlappingSS=overlap)),flush=True)
    assert control is not None
    print('NEGATIVE_CONTROL='+json.dumps(control),flush=True)
    print('PASS: exact budget without NoSAAS; all enlarged gaps cost two under NoSAAS',flush=True)
if __name__=='__main__':main()
