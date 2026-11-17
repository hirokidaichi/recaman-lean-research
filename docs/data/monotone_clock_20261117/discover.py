"""Bounded discovery only; an independent verifier must check any witness."""
import json, random, time

start=time.process_time()
rng=random.Random(20261117)
# signs, weights, heights before each step plus final, weighted positions, E, S
beam=[('',(),(0,),(0,),0,0)]
expanded=0
for length in range(1,33):
    candidates=[]
    for signs,weights,H,X,E,S in beam:
        prev=weights[-1] if weights else 0
        supplies={X[-1]-X[s] for s in range(len(signs)) if H[-1]-H[s]==1 and X[-1]-X[s]>prev}
        for c in ('A','S'):
            choices={prev+1,prev+2} | (supplies if c=='A' else set())
            for weight in sorted(choices):
                e=E+int(c=='A' and weight in supplies)
                ss=S+int(c=='S')
                state=(signs+c,weights+(weight,),H+(H[-1]+(1 if c=='A' else -1),),X+(X[-1]+(weight if c=='A' else -weight),),e,ss)
                expanded+=1
                if e>ss:
                    print(json.dumps({'status':'witness','word':state[0],'weights':state[1],'E':e,'S':ss,'expanded':expanded,'cpu_seconds':time.process_time()-start}),flush=True)
                    raise SystemExit(0)
                candidates.append((e-ss,e,rng.random(),state))
        if time.process_time()-start>4.5:
            print(json.dumps({'status':'cooperative_stop','length':length,'expanded':expanded,'cpu_seconds':time.process_time()-start}),flush=True)
            raise SystemExit(0)
    candidates.sort(key=lambda x:x[:3],reverse=True)
    chosen=candidates[:150]
    rest=candidates[150:]
    chosen+=rng.sample(rest,min(150,len(rest)))
    beam=[x[3] for x in chosen]
print(json.dumps({'status':'no_witness_in_frozen_beam','expanded':expanded,'cpu_seconds':time.process_time()-start}))
