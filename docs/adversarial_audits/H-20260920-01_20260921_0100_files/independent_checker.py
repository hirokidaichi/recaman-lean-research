#!/usr/bin/env python3
from itertools import combinations
import json

A, S = True, False

def bits(s): return [c == "A" for c in s]
def text(w): return "".join("A" if b else "S" for b in w)
def p2(w):
    sg = [1 if b else -1 for b in w]
    return sum(sg) == 1 and sum((i + 1) * x for i, x in enumerate(sg)) == 0
def minimal(w): return p2(w) and not any(p2(w[:d]) for d in range(1, len(w)))
def past(cycle, t, d): return [cycle[(t - 1 - i) % len(cycle)] for i in range(d)]
def soff(w): return [i + 1 for i,b in enumerate(w) if not b]
def oldest(w): return max(soff(w), default=0)

aas = bits("AAS")
w1 = bits("SAAAASS")
w2 = bits("ASAASAS")
donors = list(map(bits, ["AAASSSASASA", "ASAAASSSASA", "ASASAAASSSA",
                         "ASSAAAASSAS", "ASSAAASAASS", "SAAASAASSSA", "SAAASSAAASS"]))

def merge_word(env, endpoint, word):
    out = dict(env)
    if endpoint in out and out[endpoint] is not A: return None
    out[endpoint] = A
    for j,b in enumerate(word):
        x = endpoint - 1 - j
        if x in out and out[x] != b: return None
        out[x] = b
    return out

def local_owners(target):
    root = merge_word({}, 0, w1)
    ans=[]
    for name,w in [("AAS",aas),("w1",w1),("w2",w2)]:
        for k in soff(w):
            v=target+k
            if merge_word(root,v,w) is not None:
                ans.append((name,v,k))
    return ans

def donor_w1_placements(d):
    env=merge_word({},0,d)
    target=-oldest(d)
    out=[]
    for k in soff(w1):
        t=target+k
        merged=merge_word(env,t,w1)
        if merged is not None:
            out.append((t,k,"A" if merged.get(t+1,A) else "S"))
    return out

def minimal_lag(c,t,cap=None):
    cap=cap or 4*len(c)
    for d in range(1,cap+1):
        if p2(past(c,t,d)): return d
    return None
def supply(s):
    c=bits(s); out={}
    for t,b in enumerate(c):
        if b:
            d=minimal_lag(c,t)
            if d is not None:
                w=past(c,t,d)
                out[t]=(d,text(w),sorted({(t-k)%len(c) for k in soff(w)}))
    return out
def neigh(U,B): return sorted(set().union(*(set(U[b][2]) for b in B))) if B else []
def hall(U):
    keys=list(U)
    return all(len(B)<=len(neigh(U,B)) for r in range(len(keys)+1) for B in combinations(keys,r))

results={}
results["donor_offsets"]=[oldest(d) for d in donors]
results["fixed11_bits"]=[text(d)[10] for d in donors]
results["older_S_owners"] = local_owners(-7)
results["newest_S_owners"] = local_owners(-1)
results["donor_w1_placements"]=[(text(d),oldest(d),donor_w1_placements(d)) for d in donors]

controls = {
  "falseoffset11": ("AAAASAAASASASSS", [2,3,5,7]),
  "E240": ("AAAASSAAAASAAASASS", [2,8,11,13]),
  "noSS2": ("AAAASAAASSSS", [7]),
  "notight": ("AAAASASASSS", [5]),
  "Wnotight": ("SSAAAASA", [7]),
  "properU": ("SSAAAASAAAAAAAAASAAA", [4,7,9]),
}
for label,(s,B) in controls.items():
    U=supply(s)
    results[label]={"p":len(s),"U":U,"hall":hall(U),"B":B,"N":neigh(U,B),"tight":len(neigh(U,B))==len(B)}

# Exact assertions are the negative-control acceptance gate.
assert results["donor_offsets"] == [10,10,10,11,11,10,11]
assert results["fixed11_bits"] == ["A","A","A","S","S","A","S"]
assert results["older_S_owners"] == [("w1",0,7)]
assert results["newest_S_owners"] == [("AAS",2,3),("w1",0,1),("w2",6,7)]
assert [(x[0],x[1],x[2]) for x in results["donor_w1_placements"] if x[2]] == [
 ("AAASSSASASA",10,[(-9,1,"S")]),
 ("ASAAASSSASA",10,[(-9,1,"S")]),
 ("ASSAAAASSAS",11,[(-10,1,"S")])]
assert results["falseoffset11"]["U"][3][0:2] == (11,"AAASSSASASA")
assert results["E240"]["N"] == [4,5,10,17] and results["E240"]["tight"]
assert results["noSS2"]["U"][3][1] == "AAASSSSAAAS"
assert results["noSS2"]["N"] == [4] and results["noSS2"]["tight"]
assert results["notight"]["tight"] is False
assert results["Wnotight"]["U"][7][1] == "SAAAASS" and bits("SSAAAASA")[(7+1)%8] is S
assert results["properU"]["tight"] and len(results["properU"]["U"]) == 4
print(json.dumps(results, sort_keys=True))
print("PASS independent local/periodic controls")
