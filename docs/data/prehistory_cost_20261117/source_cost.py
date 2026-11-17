"""New two-key construction; exact original-source/free evaluation, bounded orders."""
import hashlib,json,math,random,sys,time
from collections import defaultdict
from pathlib import Path

BASE=Path(__file__).resolve().parent
START=time.process_time()
LIMIT=12000
def guard():
    if time.process_time()-START>4.5:raise RuntimeError('cooperative4.5CPU stop')

def profile(w):
    H=[0];B=[0]
    for c in w:
        H.append(H[-1]+(1 if c=='A' else -1));B.append(B[-1]+H[-1])
    return H,B

def orders(M,count,seed):
    tasks=[(j,off) for j in range(M) for off in (5,6)]
    proposals=[tasks,list(reversed(tasks)),sorted(tasks,key=lambda p:(p[1],p[0])),sorted(tasks,key=lambda p:(p[1],-p[0])),sorted(tasks,key=lambda p:(-p[1],p[0])),sorted(tasks,key=lambda p:(-p[1],-p[0]))]
    rng=random.Random(seed+M);seen=set();out=[]
    while len(out)<count:
        if proposals:p=proposals.pop(0)
        else:p=rng.sample(tasks,len(tasks))
        key=tuple(p)
        if key not in seen:seen.add(key);out.append(p)
    return out

def construct(M,order):
    x='AAAA';c0=-3
    for j,off in order:
        c=-3 if off==5 else -2
        goal=-24*j-15 if off==5 else -16*j-11
        connector='A'*(c0-c) if c<c0 else 'S'*(c-c0)
        y=connector+x
        H,B=profile(y);area=B[-1]
        loops=abs(goal-area)
        if len(y)+2*loops>LIMIT:return None
        x=('AS' if area<=goal else 'SA')*loops+y;c0=c
        assert profile(x)[1][-1]==goal
        guard()
    x='A'*(c0+3)+x
    H,B=profile(x);D=3*len(x)-B[-1]
    assert H[-1]==4 and D>=2
    m=max(2,math.isqrt(D+7))
    while True:
        E=m*m-7-D
        if E>=0:
            b=(3*E)%5;a=(E-7*b)//5
            if a>=0:break
        m+=1
    h=m+1
    total=h+1+(m+1)+(m+3)+2*(a+b)+len(x)+8*M+1
    if total>LIMIT:return None
    p='S'+'A'*(m+1)+'S'*(m+3)+'AS'*a+'SA'*b+x
    HP,BP=profile(p)
    assert (HP[-1],BP[-1])==(1,0)
    T=h+len(p);word='S'*h+p+'ASSSSAAA'*M+'A'
    assert len(word)==total
    return word,h+1,T,{'D':D,'hill':m,'fill_AS':a,'fill_SA':b,'seed_length':len(x)}

def evaluate(w,h,T,M):
    H,B=profile(w);idx=defaultdict(list);src={};free=[];low=[];E=S=0
    for q,c in enumerate(w):
        if c=='S':S+=1
        else:
            ss=idx.get((H[q]-1,B[q]-q*(H[q]-1)),[])
            if ss:E+=1;src[q]=tuple(ss)
            else:
                free.append(q)
                if q<T and H[q]<=H[h]+1:low.append(q)
        assert E+1<=S
        idx[(H[q],B[q]-q*H[q])].append(q)
    assert w[:h]=='S'*h
    assert w[T:]=='ASSSSAAA'*M+'A'
    assert all(q in src for q in range(T,len(w)) if w[q]=='A')
    assert all(src[T+8*j]==(h-1,) for j in range(M+1))
    external=[]
    for j in range(M):
        for off in (5,6):
            q=T+8*j+off
            assert all(u<T for u in src[q])
            external.append({'q':q,'sources':src[q]})
    assert len({r['sources'][0] for r in external})==2*M
    return {'M':M,'h':h,'T':T,'length':len(w),'low_free':len(low),'low_free_clocks':low,'prehistory_free':sum(q<T for q in free),'total_free':len(free),'original_actual':E,'S':S,'external':external,'min_height':min(H),'max_height':max(H),'word_sha256':hashlib.sha256(w.encode()).hexdigest(),'word':w}

def main(mode):
    values,count,seed=([3,4],48,20261117) if mode=='discovery' else ([5,7],24,17001117)
    output={'mode':mode,'parameters':{'M':values,'orders_per_M':count,'seed':seed,'length_cap':LIMIT},'records':[],'counterexample':False}
    for M in values:
        best=None;accepted=skipped=0;min_raw=None
        for order in orders(M,count,seed):
            guard();built=construct(M,order)
            if built is None:skipped+=1;continue
            w,h,T,meta=built;r=evaluate(w,h,T,M);accepted+=1
            r.update(construction=meta,order=order)
            if best is None or (r['low_free'],r['length'])<(best['low_free'],best['length']):best=r
            if r['low_free']<M:output['counterexample']=True;break
        if best is not None:
            filename=mode+'-best-M'+str(M)+'.json'
            (BASE/filename).write_text(json.dumps(best,indent=2)+'\n')
            summary={k:best[k] for k in ['M','h','T','length','low_free','prehistory_free','min_height','max_height','word_sha256']}
            summary.update(certificate=filename,accepted=accepted,skipped_over_length=skipped)
        else:summary={'M':M,'accepted':accepted,'skipped_over_length':skipped,'certificate':None}
        output['records'].append(summary);print(json.dumps(summary),flush=True)
        if output['counterexample']:break
    output['worker_python_cpu_seconds']=time.process_time()-START
    (BASE/(mode+'-summary.json')).write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output),flush=True)

if __name__=='__main__':main(sys.argv[1])
