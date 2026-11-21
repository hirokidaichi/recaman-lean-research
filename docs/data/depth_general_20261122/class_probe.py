"""Frozen finite-word census. Cooperative single-process exact source/chronology tests."""
import argparse, json, time

ap = argparse.ArgumentParser()
ap.add_argument('--h-lo', type=int, required=True)
ap.add_argument('--h-hi', type=int, required=True)
ap.add_argument('--core-lo', type=int, required=True)
ap.add_argument('--core-hi', type=int, required=True)
ap.add_argument('--soft-cpu', type=float, default=.65)
a = ap.parse_args()
start = time.process_time()
nodes = 0
counts = {}
witness = None
near = None

def census(h, n):
    global nodes, witness, near
    H = list(range(0, -h-1, -1))
    B = [0]
    for v in H[1:]: B.append(B[-1]+v)
    outputs = {(H[u], (u+1)*H[u]-B[u]) for u in range(h+1)}
    acands = set()
    lows = set()
    word = ['S']*h
    row = {'complete':0, 'min_slack':None, 'sample':None}
    counts[f'h{h}/core{n}'] = row
    def dfs(added, supplied, lowcount, minimum):
        global nodes, witness, near
        nodes += 1
        if nodes % 128 == 0 and time.process_time()-start > a.soft_cpu:
            raise TimeoutError('cooperative CPU budget; partial census is not exhaustive')
        k = len(word)-h
        q = len(word)
        if k == n:
            if H[-1] != 2-h: return
            D = max(0,-h-minimum)
            slack = len(lows)-D
            item = {'word':''.join(word), 'h':h, 'depth':D, 'K_LOW':len(lows), 'F_LOW':lowcount, 'total_free':added-supplied, 'classes':sorted(lows)}
            row['complete'] += 1
            if row['min_slack'] is None or slack < row['min_slack']:
                row['min_slack']=slack;row['sample']=item
            if near is None or slack < near['slack']: near=dict(item,slack=slack)
            if slack<0: witness=item;raise ValueError('counter found')
            return
        remaining = n-k
        need = 2-h-H[-1]
        if abs(need)>remaining or (remaining-need)%2:return
        for sign in [1,-1]:
            if k==0 and sign<0:continue # maximal initial S run
            c = (H[-1]-1, (q+1)*(H[-1]-1)-B[-1])
            is_actual = sign==1 and c in outputs
            new_supplied = supplied+int(is_actual)
            new_added = added+int(sign==1)
            if (q+1-new_added)-new_supplied < 1:continue
            hp=H[-1]+sign;bp=B[-1]+hp
            op=(hp,(q+2)*hp-bp)
            if sign<0 and (op in outputs or op in acands):continue
            add_o=op not in outputs; add_c=sign==1 and c not in acands
            is_lowfree=sign==1 and not is_actual and H[-1]<=1-h
            add_l=is_lowfree and c not in lows
            if add_o:outputs.add(op)
            if add_c:acands.add(c)
            if add_l:lows.add(c)
            H.append(hp);B.append(bp);word.append('A' if sign>0 else 'S')
            dfs(new_added,new_supplied,lowcount+int(is_lowfree),min(minimum,hp))
            word.pop();H.pop();B.pop()
            if add_l:lows.remove(c)
            if add_c:acands.remove(c)
            if add_o:outputs.remove(op)
    dfs(0,0,0,-h)

stopped=None
try:
    for h in range(a.h_lo,a.h_hi+1):
        for n in range(a.core_lo,a.core_hi+1,2):census(h,n)
except (TimeoutError,ValueError) as e:stopped=str(e)
print(json.dumps({'parameters':vars(a),'nodes':nodes,'census':counts,'witness':witness,'nearest':near,'stopped':stopped,'worker_internal_cpu_seconds':time.process_time()-start},indent=2))
