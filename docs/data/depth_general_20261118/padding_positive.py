"""Frozen independent question: original-positive closure under one prefix S."""
from pathlib import Path
import itertools,json,sys,time
OUT=Path(__file__).resolve().parent

def profile(w):
    H=B=S=E=0;bank={};free=[];src=[];rows=[];positive=True
    for q,c in enumerate(w):
        ss=list(bank.get((H-1,B-q*(H-1)),[])) if c=='A' else []
        if c=='A':
            E+=bool(ss)
            if not ss:free.append(q)
        else:S+=1
        src.append(ss);bank.setdefault((H,B-q*H),[]).append(q)
        H+=1 if c=='A' else -1;B+=H
        positive=positive and E+1<=S
        rows.append({'clock':q+1,'S':S,'E':E,'F':len(free),'H':H,'deficit':S-E})
    return {'positive':positive,'rows':rows,'sources':src,'free':free}

def main():
    mode=sys.argv[1];start=time.process_time();checked=eligible=0;counter=None;maxgain=0
    lengths=range(1,13) if mode=='discovery' else range(13,15)
    for n in lengths:
        for tail in itertools.product('SA',repeat=n-1):
            w='S'+''.join(tail);f=profile(w);checked+=1
            if not f['positive']:continue
            eligible+=1;g=profile('S'+w)
            assert all(not ss or set(u+1 for u in ss)<=set(g['sources'][q+1]) for q,ss in enumerate(f['sources']))
            maxgain=max(maxgain,g['rows'][-1]['E']-f['rows'][-1]['E'])
            if not g['positive']:
                first=next(i for i,r in enumerate(g['rows']) if r['deficit']<1)
                counter={'original':w,'padded':'S'+w,'K':len(w),'first_failed_clock':first+1,'f':f,'g':g}
                break
        if counter:break
    result={'mode':mode,'checked':checked,'eligible_original_positive':eligible,'max_gain':maxgain,'counter':counter,'cpu_seconds':time.process_time()-start,'scope':'finite falsification only, not a general positive-domain theorem'}
    (OUT/('padding-'+mode+'-summary.json')).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='counter'},indent=2))
    if counter:print(json.dumps({'word':counter['original'],'first_failed_clock':counter['first_failed_clock'],'f_end':counter['f']['rows'][-1],'g_end':counter['g']['rows'][-1]},indent=2))

if __name__=='__main__':main()
