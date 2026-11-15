"""Frozen new old-source-reserve question, all original keys retained; no generic height beam."""
import sys,time,json
mode=sys.argv[1];beg=time.process_time();nodes=checks=0;done=[];best=None;counter=None
class BudgetStop(Exception):pass

def guard():
    if time.process_time()-beg>2.15:raise BudgetStop

def forward(h,lim):
    global nodes,checks,best,counter
    old={(-i,i*(i-1)//2) for i in range(h)}
    local={};tail=[]
    def dfs(q,H,B,E,F,S):
        global nodes,checks,best,counter
        nodes+=1
        if nodes%4096==0:guard()
        key=(H-1,B-q*(H-1));lo=key in local;ol=key in old
        if ol and not lo:
            checks+=1;d=H+h-1
            item={'h':h,'K':q-h,'prefix':'S'*h+''.join(tail),'target':q,'d':d,'free_before_endpoint':F,'d_minus_free':d-F}
            if best is None or d-F>best['d_minus_free']:best=item
            if d>F:counter=item;raise BudgetStop
        if q==h+lim:return
        src=(H,B-q*H);local[src]=local.get(src,0)+1
        for a in [False,True]:
            ee=E+int(a and (ol or lo));ff=F+int(a and not (ol or lo));ss=S+int(not a)
            if ee+1>ss:continue
            HH=H+(1 if a else -1);tail.append('A' if a else 'S')
            dfs(q+1,HH,B+HH,ee,ff,ss);tail.pop()
        local[src]-=1
        if not local[src]:del local[src]
    dfs(h,-h,-h*(h+1)//2,0,0,h)

# Independent evaluator uses literal backwards area, not forward keys.
def reverse(h,lim):
    global nodes,checks,best,counter
    tail=[];H=[-i for i in range(h+1)]
    def sources(q):
        area=0;out=[];end=H[q]
        for t in range(q-1,-1,-1):
            area+=H[t+1]
            if end==H[t]+1 and area-(q-t)*H[t]==0:out.append(t)
        return out
    def dfs(q,E,F,S):
        global nodes,checks,best,counter
        nodes+=1
        if nodes%1024==0:guard()
        src=sources(q)
        if src and all(t<h for t in src):
            checks+=1;d=H[q]+h-1
            item={'h':h,'K':q-h,'prefix':'S'*h+''.join(tail),'target':q,'d':d,'free_before_endpoint':F,'d_minus_free':d-F,'all_sources':src}
            if best is None or d-F>best['d_minus_free']:best=item
            if d>F:counter=item;raise BudgetStop
        if q==h+lim:return
        for a in [False,True]:
            ee=E+int(a and bool(src));ff=F+int(a and not src);ss=S+int(not a)
            if ee+1>ss:continue
            tail.append('A' if a else 'S');H.append(H[-1]+(1 if a else -1))
            dfs(q+1,ee,ff,ss);H.pop();tail.pop()
    dfs(h,0,0,h)

try:
    ranges=[(h,16) for h in range(1,9)] if mode=='discovery' else [(h,12) for h in [9,10,12]]
    for h,lim in ranges:
        (forward if mode=='discovery' else reverse)(h,lim);done.append([h,lim])
    status='all frozen ranges complete'
except BudgetStop:status='exact counterexample' if counter else 'cooperative CPU stop; incomplete ranges unclaimed'
print(json.dumps({'mode':mode,'status':status,'completed_ranges':done,'nodes':nodes,'exclusive_source_endpoint_checks':checks,'best':best,'counterexample':counter,'cpu_body_seconds':time.process_time()-beg,'scope':'finite original initial-S positive histories, endpoint q included, all old/local keys retained; no infinite absence theorem or standard orbit reachability'}),flush=True)
