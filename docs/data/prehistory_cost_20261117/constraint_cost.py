"""Exact bounded original-EndN constraints; unknown never means UNSAT."""
import hashlib,json,sys,time
from pathlib import Path
import z3
BASE=Path(__file__).resolve().parent

def problem(h,T,M,budget,pinned=None,timeout=1600):
    N=T+8*M+1
    f=[z3.Bool('f'+str(i)) for i in range(N)]
    H=[z3.Int('H'+str(i)) for i in range(N+1)]
    B=[z3.Int('B'+str(i)) for i in range(N+1)]
    E=[z3.Bool('E'+str(i)) for i in range(N)]
    deficit=[z3.Int('d'+str(i)) for i in range(N+1)]
    solver=z3.Solver();solver.set(timeout=timeout,random_seed=170117,rlimit=800000)
    solver.add(H[0]==0,B[0]==0,deficit[0]==0)
    sources=[]
    for q in range(N):
        solver.add(H[q+1]==H[q]+z3.If(f[q],1,-1),B[q+1]==B[q]+H[q+1])
        row=[z3.And(H[q]-H[u]==1,B[q]-B[u]-(q-u)*H[u]==0) for u in range(q)]
        sources.append(row)
        solver.add(E[q]==z3.And(f[q],z3.Or(*row)))
        solver.add(deficit[q+1]==deficit[q]+z3.If(f[q],0,1)-z3.If(E[q],1,0),deficit[q+1]>=1)
        if q<h:solver.add(z3.Not(f[q]))
        if q>=T:
            c=('ASSSSAAA'*M+'A')[q-T]
            solver.add(f[q]==(c=='A'),z3.Implies(f[q],E[q]))
        if pinned is not None:solver.add(f[q]==(pinned[q]=='A'))
    for j in range(M+1):
        q=T+8*j
        for u,s in enumerate(sources[q]):solver.add(s==(u==h-1))
    low=[z3.If(z3.And(f[q],z3.Not(E[q]),H[q]<=1-h),1,0) for q in range(T)]
    solver.add(z3.Sum(*low)<=budget)
    return solver,f,low

def run(tag,h,T,M,budget,pinned=None):
    start=time.process_time();solver,f,low=problem(h,T,M,budget,pinned)
    result=solver.check()
    record={'tag':tag,'h':h,'T':T,'M':M,'low_free_budget':budget,'status':str(result),'cpu_seconds':time.process_time()-start,'reason_unknown':solver.reason_unknown() if result==z3.unknown else None,'solver_version':z3.get_version_string()}
    if result==z3.sat:
        model=solver.model();record['word']=''.join('A' if z3.is_true(model.eval(x)) else 'S' for x in f)
        record['model_low_free']=model.eval(z3.Sum(*low)).as_long()
        record['word_sha256']=hashlib.sha256(record['word'].encode()).hexdigest()
    (BASE/(tag+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record),flush=True)
    return result

mode=sys.argv[1]
if mode=='controls':
    P='S'+'A'*11+'S'*13+'S'*3+'A'*3+'S'*3+'A'*4+'S'+'A'+'S'*4+'A'*7
    w='S'*11+P+'A'+'S'*4+'A'*3+'A'
    assert run('control-positive',12,62,1,12,w)==z3.sat
    assert run('control-negative',12,62,1,11,w)==z3.unsat
elif mode=='discovery':
    for T in (40,56):
        if run('constraint-M3-T'+str(T),2,T,3,2)==z3.sat:break
elif mode=='holdout':
    run('constraint-M4-T65',3,65,4,3)
