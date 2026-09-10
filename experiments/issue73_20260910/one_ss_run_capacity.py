#!/usr/bin/env python3
import hashlib, itertools, json, pathlib, subprocess

def test(word):
    p=len(word);sources=[];image={}
    for t,c in enumerate(word):
        if c<0:continue
        mass=moment=ss=0;previous=None
        for d in range(1,2*p+1):
            s=word[(t-d)%p];mass+=s;moment+=d*s
            ss+=previous==s==-1;previous=s
            if mass==1 and moment==0:
                if ss==1:
                    k=1
                    while word[(t-k)%p]==1:k+=1
                    q=(t-k)%p
                    source=dict(t=t,lag=d,run_offset=k,run_start_S=q)
                    if q in image:return (image[q],source)
                    image[q]=source;sources.append(source)
                break
    assert len(sources)<=word.count(-1)
    return sources

def main():
    print('protocol=H-20260910-27',flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),flush=True)
    print('source_sha256='+hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),flush=True)
    control=None
    for p in range(1,18):
        eligible=phases=balanced=negative=maximum=0
        for word in itertools.product((-1,1),repeat=p):
            noSAAS=all(tuple(word[(t+i)%p] for i in range(4))!=(-1,1,1,-1) for t in range(p))
            if not noSAAS and (p>13 or control is not None):continue
            result=test(word)
            if not noSAAS:
                if isinstance(result,tuple):control=dict(period=p,word=''.join('A' if c==1 else 'S' for c in word),collision=result)
                continue
            assert isinstance(result,list),(word,result)
            assert all(x['run_offset'] in (1,2) for x in result)
            eligible+=1;phases+=len(result);balanced+=sum(word)==0;negative+=sum(word)<0
            maximum=max(maximum,max((x['lag'] for x in result),default=0))
        print(('DISCOVERY=' if p<=11 else 'HOLDOUT=')+json.dumps(dict(period=p,NoSAAS_words=eligible,one_SS_phases=phases,balanced_words=balanced,negative_mass_words=negative,max_minimum_lag=maximum)),flush=True)
    print('NO_SAAS_CONTROL='+json.dumps(control),flush=True)
    print('PASS: at most one minimum one-SS source per cyclic A run through period17',flush=True)
if __name__=='__main__':main()
