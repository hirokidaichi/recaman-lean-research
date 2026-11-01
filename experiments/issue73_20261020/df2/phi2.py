# Phi': groups by q in increasing q; members t desc; each takes latest S with F>=h+1, position in [t,q], not clean start, not used.
from lib import endables
def phi2(s, order='q'):
    F,E=endables(s)
    tg={}; groups={}; used=set()
    for e in E:
        if e['clean']: tg[e['b']]=e['t']; used.add(e['t'])
        else: groups.setdefault(e['q'],[]).append(e)
    if len(used)!=len([e for e in E if e['clean']]): return None,'cleancollide'
    for q in sorted(groups):
        mem=groups[q]; h=mem[0]['h']; mem.sort(key=lambda e:(-e['t'],e['b']))
        for e in mem:
            c=q
            while c>=e['t'] and not (s[c]=='S' and F[c]>=h+1 and c not in used): c-=1
            if c<e['t']: return None,('noexist',q,e)
            tg[e['b']]=c; used.add(c)
    return tg,None
