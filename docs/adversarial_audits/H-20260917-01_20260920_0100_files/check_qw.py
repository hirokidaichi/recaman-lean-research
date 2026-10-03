#!/usr/bin/env python3
from itertools import combinations, product
import hashlib

DONORS = {
    "d1": "AAASSSASASA",
    "d2": "ASAAASSSASA",
    "d3": "ASASAAASSSA",
    "d4": "ASSAAAASSAS",
    "d5": "ASSAAASAASS",
    "d6": "SAAASAASSSA",
    "d7": "SAAASSAAASS",
}
W1 = "SAAAASS"


def bit(c):
    return c == "A"


def sign(b):
    return 1 if b else -1


def past(word, t, d):
    p = len(word)
    return tuple(word[(t - i) % p] for i in range(1, d + 1))


def p2(w):
    return sum(map(sign, w)) == 1 and sum(i * sign(b) for i, b in enumerate(w, 1)) == 0


def ss_count(w):
    return sum(not a and not b for a, b in zip(w, w[1:]))


def complete_u(word):
    p = len(word)
    lags = {}
    for u, b in enumerate(word):
        if not b:
            continue
        for d in range(1, p * (p + 1) + 1):
            if p2(past(word, u, d)):
                lags[u] = d
                break
    return tuple(lags), lags


def nbd(word, subset, lags):
    p = len(word)
    return frozenset(
        (u - i) % p
        for u in subset
        for i in range(1, lags[u] + 1)
        if not word[(u - i) % p]
    )


def subsets(xs):
    for k in range(len(xs) + 1):
        yield from combinations(xs, k)


def hall(word, U, lags):
    return all(len(A) <= len(nbd(word, A, lags)) for A in subsets(U))


def donor_info(word, u, lags):
    if lags.get(u) != 11:
        return None
    w = past(word, u, 11)
    if ss_count(w) != 2:
        return None
    oldest = max(i for i, b in enumerate(w, 1) if not b)
    return ''.join('A' if b else 'S' for b in w), oldest, (u - oldest) % len(word)


def inspect(label, text):
    word = tuple(bit(c) for c in text)
    p = len(word)
    U, lags = complete_u(word)
    hall_ok = hall(word, U, lags)
    donors = []
    q_targets = 0
    q_violations = []
    q_examples = []
    w_targets = 0
    w_violations = []
    w_examples = []
    for u0 in U:
        di = donor_info(word, u0, lags)
        if di is None:
            continue
        donors.append((u0,) + di)
        for B in subsets(tuple(u for u in U if u != u0)):
            if not all(lags[b] in (3, 7, 11) for b in B):
                continue
            if len(nbd(word, B, lags)) != len(B):
                continue
            q_targets += 1
            if di[2] in nbd(word, B, lags):
                q_violations.append((u0, B, di[2]))
            elif B:
                q_examples.append((u0, B, di[2]))
    for B in subsets(U):
        if not all(lags[b] in (3, 7) for b in B):
            continue
        if len(nbd(word, B, lags)) != len(B):
            continue
        for t in B:
            if lags[t] == 7 and ''.join('A' if b else 'S' for b in past(word, t, 7)) == W1:
                w_targets += 1
                row = (B, t, 'A' if word[(t + 1) % p] else 'S')
                if not word[(t + 1) % p]:
                    w_violations.append(row)
                else:
                    w_examples.append(row)
    print(f"MODEL {label} p={p} word={text}")
    print(f" signSum={sum(map(sign, word))} U={U} lags={','.join(f'{u}:{lags[u]}' for u in U)} D={tuple(i for i,b in enumerate(word) if not b)} Hall={hall_ok}")
    print(f" donors={donors}")
    print(f" Q_targets={q_targets} Q_violations={q_violations[:3]} Q_nonempty_examples={q_examples[:3]}")
    print(f" W_targets={w_targets} W_violations={w_violations[:3]} W_examples={w_examples[:3]}")


def compatibility():
    for name, text in DONORS.items():
        possible = []
        for p in range(1, 12):
            assigned = {}
            ok = True
            for i, c in enumerate(text, 1):
                phase = (-i) % p
                if phase in assigned and assigned[phase] != c:
                    ok = False
                assigned[phase] = c
            if ok:
                possible.append(p)
        oldest = max(i for i, c in enumerate(text, 1) if c == "S")
        offset11 = text[10]
        print(f"DONOR {name} word={text} oldest={oldest} offset11={offset11} compatible_p_lt12={possible}")


def controls():
    for label, text, u0, B in (
        ('ss3-control', 'AAAASAAASSSS', 3, (2, 5, 7)),
        ('false-offset11-control', 'AAAASAAASASASSS', 3, (2, 5, 7)),
    ):
        vals = tuple(bit(c) for c in text)
        U, lags = complete_u(vals)
        w = past(vals, u0, 11)
        oldest = max(i for i, b in enumerate(w, 1) if not b)
        true_phase = (u0 - oldest) % len(vals)
        offset11_phase = (u0 - 11) % len(vals)
        print(f"CONTROL {label} p={len(vals)} word={text} U={U} lags={lags} Hall={hall(vals,U,lags)}")
        print(f" u0={u0} donor={''.join('A' if b else 'S' for b in w)} ss={ss_count(w)} oldest={oldest} true_phase={true_phase} offset11_phase={offset11_phase} offset11_bit={'A' if vals[offset11_phase] else 'S'}")
        print(f" B={B} tight={len(nbd(vals,B,lags)) == len(B)} N={tuple(sorted(nbd(vals,B,lags)))} true_covered={true_phase in nbd(vals,B,lags)} offset11_covered={offset11_phase in nbd(vals,B,lags)}")


def exhaustive_small():
    totals = dict(words=0, positive=0, hall=0, qtargets=0, qviol=0, wtargets=0, wviol=0)
    first_q = None
    first_w = None
    first_w_without_tight = None
    for p in range(1, 12):
        pt = dict(words=0, positive=0, hall=0, qtargets=0, qviol=0, wtargets=0, wviol=0)
        for vals in product((False, True), repeat=p):
            pt['words'] += 1
            if sum(map(sign, vals)) <= 0:
                continue
            pt['positive'] += 1
            U, lags = complete_u(vals)
            if first_w_without_tight is None:
                for t in U:
                    if (lags[t] == 7 and
                        tuple(vals[(t-i)%p] for i in range(1,8)) == tuple(bit(c) for c in W1) and
                        not vals[(t+1)%p]):
                        first_w_without_tight = (p, ''.join('A' if b else 'S' for b in vals), U, lags.copy(), t,
                                                 len(nbd(vals, (t,), lags)))
            if not hall(vals, U, lags):
                continue
            pt['hall'] += 1
            for u0 in U:
                di = donor_info(vals, u0, lags)
                if di is None:
                    continue
                for B in subsets(tuple(u for u in U if u != u0)):
                    if all(lags[b] in (3, 7, 11) for b in B) and len(nbd(vals, B, lags)) == len(B):
                        pt['qtargets'] += 1
                        pt['qviol'] += di[2] in nbd(vals, B, lags)
                        if first_q is None and B:
                            first_q = (p, ''.join('A' if b else 'S' for b in vals), U, lags.copy(), u0, B, di)
            for B in subsets(U):
                if not all(lags[b] in (3, 7) for b in B) or len(nbd(vals, B, lags)) != len(B):
                    continue
                for t in B:
                    if lags[t] == 7 and tuple(vals[(t-i)%p] for i in range(1,8)) == tuple(bit(c) for c in W1):
                        pt['wtargets'] += 1
                        pt['wviol'] += not vals[(t+1)%p]
                        if first_w is None:
                            first_w = (p, ''.join('A' if b else 'S' for b in vals), U, lags.copy(), B, t, vals[(t+1)%p])
        for k in totals: totals[k] += pt[k]
        print("SMALL", p, " ".join(f"{k}={v}" for k,v in pt.items()))
    print("SMALL_TOTAL", " ".join(f"{k}={v}" for k,v in totals.items()))
    print("FIRST_SMALL_NONEMPTY_Q", first_q)
    print("FIRST_SMALL_W", first_w)
    print("FIRST_W_WITHOUT_TIGHT", first_w_without_tight)


if __name__ == '__main__':
    compatibility()
    controls()
    inspect('E240-text', 'AAAASSAAAASAAASASS')
    inspect('p15-card', 'AAAASAAASASASSS')
    exhaustive_small()
