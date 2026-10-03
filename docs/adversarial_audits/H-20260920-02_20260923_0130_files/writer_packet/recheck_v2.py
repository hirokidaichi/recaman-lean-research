#!/usr/bin/env python3
"""Small, independent regression for H-20260920-02; known data, not holdout."""
import itertools
import json


def p2(w):
    z = [1 if c == 'A' else -1 for c in w]
    return sum(z) == 1 and sum(i * x for i, x in enumerate(z, 1)) == 0


def ss(w):
    return sum(w[i:i+2] == 'SS' for i in range(len(w)-1))


def past(word, clock, lag):
    return ''.join(word[(clock-i) % len(word)] for i in range(1, lag+1))


def facts(w, clock, member):
    out = {clock-i: c for i, c in enumerate(w, 1)}
    if member:
        out[clock] = 'A'
    return out


def merge_ok(*maps):
    out = {}
    for m in maps:
        for k, v in m.items():
            if k in out and out[k] != v:
                return False
            out[k] = v
    return True


donors = [''.join(t) for t in itertools.product('AS', repeat=11)
          if p2(''.join(t)) and ss(''.join(t)) == 2]
assert len(donors) == 12
counts = {'minimal': 0, 'nonminimal': 0, 'aas': 0, 'w1': 0, 'w2': 0,
          'w1_future_clashes': 0}
rows = []
for w in donors:
    minimal = not any(p2(w[:i]) for i in range(1, 11))
    counts['minimal' if minimal else 'nonminimal'] += 1
    old = max(i for i, c in enumerate(w, 1) if c == 'S')
    assert old in (10, 11)
    root = facts(w, 0, False)
    covers = []
    for kind, word in [('aas', 'AAS'), ('w1', 'SAAAASS'), ('w2', 'ASAASAS')]:
        for k, c in enumerate(word, 1):
            if c != 'S':
                continue
            t = k-old
            if merge_ok(root, facts(word, t, True)):
                counts[kind] += 1
                covers.append([kind, t, k])
                if kind == 'w1':
                    assert k == 1
                    assert not merge_ok(root, facts(word, t, True), facts('AAS', t+2, True))
                    counts['w1_future_clashes'] += 1
                    for shift in (-101, -1, 0, 1, 101):
                        assert not merge_ok(facts(w, shift, False), facts(word, shift+t, True),
                                            facts('AAS', shift+t+2, True))
    rows.append({'word': w, 'minimal': minimal, 'oldest': old, 'covers': covers})
assert counts == {'minimal': 7, 'nonminimal': 5, 'aas': 0, 'w1': 5, 'w2': 2,
                  'w1_future_clashes': 5}
print(json.dumps({'kind': 'local', 'counts': counts, 'rows': rows}, sort_keys=True))

cycle = 'AASSSAAAASSSS'
u, b = 10, 7
w = past(cycle, u, 11)
bw = past(cycle, b, 3)
old = (u-max(i for i, c in enumerate(w, 1) if c == 'S')) % len(cycle)
neighbor = {(b-i) % len(cycle) for i, c in enumerate(bw, 1) if c == 'S'}
assert w == 'SAAAASSSAAS' and p2(w) and ss(w) == 2 and p2(w[:7])
assert cycle[u] == 'S' and cycle[b] == 'A' and bw == 'AAS'
assert old == 0 and neighbor == {4} and old not in neighbor
print(json.dumps({'kind': 'nonminimal_example', 'cycle': cycle, 'donor': u,
                  'donor_word': w, 'donor_current': cycle[u], 'B': [b],
                  'B_word': bw, 'N': sorted(neighbor), 'true_oldest': old}, sort_keys=True))

# Weakening onto allows a single w1 member with no future AAS owner.
weak = facts('SAAAASS', 0, True)
assert merge_ok(weak, {1: 'S', 2: 'S'})
print(json.dumps({'kind': 'weak_onto', 'members': [0], 'future': 'SS'}, sort_keys=True))
