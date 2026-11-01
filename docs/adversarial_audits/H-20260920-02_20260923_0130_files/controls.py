#!/usr/bin/env python3
"""Literal controls and counterfactual premise tests, independent of repo scripts."""

import json


def past(cycle, t, d):
    p = len(cycle)
    return ''.join(cycle[(t-k) % p] for k in range(1, d+1))


def p2(word):
    signs = tuple(1 if x == 'A' else -1 for x in word)
    return sum(signs) == 1 and sum(k*x for k, x in enumerate(signs, 1)) == 0


def nhood(cycle, members):
    p = len(cycle)
    return sorted({(u-k) % p for u, d in members for k in range(1, d+1)
                   if cycle[(u-k) % p] == 'S'})


def oldest_phase(cycle, t, d):
    w = past(cycle, t, d)
    return (t-max(k for k, x in enumerate(w, 1) if x == 'S')) % len(cycle)


def controls():
    c = 'AAAASSAAAASAAASASS'
    B = ((2, 3), (8, 3), (11, 7), (13, 3))
    N = nhood(c, B)
    assert len(N) == len(B) == 4 and N == [4,5,10,17]
    assert all(c[u] == 'A' and p2(past(c,u,d)) for u,d in B)
    assert past(c,11,7) == 'SAAAASS' and oldest_phase(c,7,11) == 14
    c69 = 'SSSSAAAASAAA'
    p69 = len(c69)
    least = {u: next(d for d in range(1,p69*(p69+1)+1) if p2(past(c69,u,d))) for u in (7,11)}
    assert least == {7:11,11:3} and oldest_phase(c69,7,11) == oldest_phase(c69,11,3) == 8
    c345 = 'AAAASAAASSSS'
    B345 = ((2,3),(5,7),(7,3))
    w345 = past(c345,3,11)
    n345 = nhood(c345,B345)
    assert p2(w345) and sum(w345[i:i+2]=='SS' for i in range(10)) == 3
    assert len(n345) == len(B345) and oldest_phase(c345,3,11) == 4 in n345
    print(json.dumps({'kind':'known_controls', 'E240':{'B':B,'N':N,'w1':past(c,11,7)},
                      'E069':{'least_lags':least,'shared_oldest':8},
                      'E345':{'donor_window':w345,'ss':3,'oldest':4,'N':n345}},sort_keys=True))


def counterfactuals():
    # Existing length-15 countermodel, used only to test a changed donor length.
    c15 = 'SAAASSSASASASAAA'
    B15 = ((3,3),)
    w15 = past(c15,15,15)
    n15 = nhood(c15,B15)
    true_s = oldest_phase(c15,15,15)
    fake_s = (15-11)%16
    assert p2(w15) and sum(w15[i:i+2]=='SS' for i in range(14)) == 2
    assert c15[15]=='A' and past(c15,3,3)=='AAS'
    assert n15==[0] and true_s==0 in n15 and fake_s==4 not in n15
    assert p2(w15[:3])
    print(json.dumps({'kind':'length15_and_fake_offset', 'donor_window':w15,
                      'proper_prefixes':[d for d in range(1,15) if p2(w15[:d])],
                      'true_oldest':true_s,'fixed_offset11':fake_s,'N':n15},sort_keys=True))
    # OwnerFamily with onto deleted: lone w1 member t=0 owns oldest -7.
    bits={0:'A',-1:'S',-2:'A',-3:'A',-4:'A',-5:'A',-6:'S',-7:'S',1:'S',2:'S'}
    assert ''.join(bits[-k] for k in range(1,8))=='SAAAASS'
    assert bits[1]=='S'
    assert -7 in (-1,-6,-7) and not any(v== -1 for v in (-7,))
    print(json.dumps({'kind':'weakened_ownerfamily', 'mem':[0], 'own_function':{'0':-7},
                      'window':'SAAAASS','next_sign':bits[1],
                      'onto_fails_at':-1,
                      'relation_control':{'own_relation_0':[-7,-6,-1],
                                          'onto_held_with_multivalued_relation':True}},sort_keys=True))
    # Find a genuine local counterexample when tightness is removed, preserving
    # all other H-02 hypotheses in a small periodic sign word.
    for p in range(5,15):
        for mask in range(1<<p):
            cycle=''.join('A' if mask>>j&1 else 'S' for j in range(p))
            members=[]
            for b in range(p):
                if cycle[b]=='A':
                    d=next((d for d in (3,7,11) if p2(past(cycle,b,d))),None)
                    if d is not None:
                        members.append((b,d))
            for u in range(p):
                w=past(cycle,u,11)
                if not p2(w) or sum(w[i:i+2]=='SS' for i in range(10))!=2:
                    continue
                s=oldest_phase(cycle,u,11)
                for member in members:
                    N=nhood(cycle,(member,))
                    if len(N)>1 and s in N:
                        print(json.dumps({'kind':'without_tightness','p':p,'cycle':cycle,
                                          'u0':u,'donor_window':w,'B':[member],
                                          'N':N,'true_oldest':s},sort_keys=True))
                        return
    raise AssertionError('missing no-tightness control')


controls()
counterfactuals()
