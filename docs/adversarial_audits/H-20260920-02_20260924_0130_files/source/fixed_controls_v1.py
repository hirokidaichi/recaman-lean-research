#!/usr/bin/env python3
"""Independent fixed-control audit for the 2026-09-24 weekly summary."""

import json


def sign(c):
    return 1 if c == "A" else -1


def mass(w):
    return sum(map(sign, w))


def moment(w):
    return sum(i * sign(c) for i, c in enumerate(w, 1))


def p2(w):
    return mass(w) == 1 and moment(w) == 0


def ss_count(w):
    return sum(w[i:i + 2] == "SS" for i in range(len(w) - 1))


def bit(cycle, t):
    return cycle[t % len(cycle)]


def past(cycle, t, d):
    return "".join(bit(cycle, t - i) for i in range(1, d + 1))


def oldest_offset(w):
    return max(i for i, c in enumerate(w, 1) if c == "S")


def neighborhood(cycle, members, lags):
    p = len(cycle)
    return sorted({
        (b - i) % p
        for b in members
        for i in range(1, lags[b] + 1)
        if bit(cycle, b - i) == "S"
    })


def strict_s_ended_p2_prefixes(w):
    return [k for k in range(1, len(w)) if w[k - 1] == "S" and p2(w[:k])]


out = {}

# H-02: inhabited nonminimal/current-S lag-11 donor with tight minimal B.
c = "AASSSAAAASSSS"
u0 = 10
dw = past(c, u0, 11)
B = [7]
lags = {7: 3}
N = neighborhood(c, B, lags)
proper = [d for d in range(1, 11) if p2(past(c, u0, d))]
off = oldest_offset(dw)
phase = (u0 - off) % len(c)
assert dw == "SAAAASSSAAS"
assert p2(dw) and ss_count(dw) == 2 and bit(c, u0) == "S"
assert proper == [7]
assert past(c, 7, 3) == "AAS" and p2(past(c, 7, 3))
assert not any(p2(past(c, 7, d)) for d in range(1, 3))
assert N == [4] and len(N) == len(B)
assert off == 11 and phase == 12 and phase not in N
out["H02"] = dict(cycle=c, u0=u0, donor=dw, donor_mass=mass(dw),
    donor_moment=moment(dw), donor_ss=ss_count(dw), donor_current=bit(c, u0),
    proper_p2_prefixes=proper, B=B, B_word=past(c, 7, 3), N=N,
    tight=len(N) == len(B), true_oldest_offset=off, true_oldest_phase=phase,
    avoids=phase not in N)

# H-03: wide Lean-domain strict example and original-domain nontight control.
c4 = "AAAS"
B4 = [2]
n3 = neighborhood(c4, B4, {2: 3})
n4 = neighborhood(c4, B4, {2: 4})
w3 = past(c4, 2, 3)
w4 = past(c4, 2, 4)
assert bit(c4, 2) == "A" and w3 == "AAS" and p2(w3)
assert not p2(w4) and n3 == n4 == [3] and len(n4) == len(B4)

c9 = "ASAAASASS"
B9 = [4]
m3 = neighborhood(c9, B9, {4: 3})
l7 = neighborhood(c9, B9, {4: 7})
v3 = past(c9, 4, 3)
v7 = past(c9, 4, 7)
assert bit(c9, 4) == "A" and p2(v3) and p2(v7)
assert m3 == [1] and l7 == [1, 7, 8] and len(l7) != len(B9)
assert m3 != l7
out["H03"] = dict(
    p4=dict(cycle=c4, B=B4, m=3, lag=4, past_m=w3, past_lag=w4,
        P2_m=p2(w3), P2_lag=p2(w4), N_m=n3, N_lag=n4,
        tight=len(n4) == len(B4)),
    p9=dict(cycle=c9, B=B9, m=3, lag=7, past_m=v3, past_lag=v7,
        P2_m=p2(v3), P2_lag=p2(v7), N_m=m3, N_lag=l7,
        tight=len(l7) == len(B9), equality=m3 == l7))

# H-04: full literal premises and the negated avoidance/deletion conclusions.
c16 = "SAAASSSASASASAAA"
u15 = 15
d15 = past(c16, u15, 15)
B16 = [3]
N16 = neighborhood(c16, B16, {3: 3})
off15 = oldest_offset(d15)
phase15 = (u15 - off15) % len(c16)
fixed11 = (u15 - 11) % len(c16)
proper15 = [d for d in range(1, 15) if p2(past(c16, u15, d))]
assert d15 == "AASASASASSSAAAS"
assert mass(c16) == 2 and bit(c16, u15) == "A"
assert p2(d15) and ss_count(d15) == 2 and proper15 == [3]
assert past(c16, 3, 3) == "AAS" and p2(past(c16, 3, 3))
assert N16 == [0] and len(N16) == len(B16)
assert off15 == 15 and phase15 == 0 and phase15 in N16
assert [s for s in N16 if s != phase15] == []
assert fixed11 == 4 and fixed11 not in N16
out["H04"] = dict(cycle=c16, period_mass=mass(c16), u0=u15, donor=d15,
    donor_current=bit(c16, u15), donor_mass=mass(d15), donor_moment=moment(d15),
    donor_ss=ss_count(d15), proper_p2_prefixes=proper15, B=B16, N=N16,
    tight=len(N16) == len(B16), true_oldest_offset=off15,
    true_oldest_phase=phase15, oldest_in_N=phase15 in N16,
    deleted_N=[s for s in N16 if s != phase15], deletion_hall=False,
    fixed_offset11_phase=fixed11, fixed_offset11_in_N=fixed11 in N16)

# H-05: one inhabited premise case and one-at-a-time weakened controls.
words = {
    "positive": "AASASASASSSA",
    "drop_ending_A": "AAASSS",
    "drop_mass_zero": "SASASSSA",
    "drop_moment_bound": "SA",
    "drop_ss_bound": "AAASSSSA",
}
h05 = {}
for name, w in words.items():
    witnesses = strict_s_ended_p2_prefixes(w)
    h05[name] = dict(word=w, ending_A=w.endswith("A"), mass=mass(w),
        moment=moment(w), moment_plus_length=moment(w) + len(w),
        ss=ss_count(w), strict_s_ended_p2_prefix_lengths=witnesses)

assert h05["positive"] == dict(word="AASASASASSSA", ending_A=True, mass=0,
    moment=-12, moment_plus_length=0, ss=2,
    strict_s_ended_p2_prefix_lengths=[3])
assert not h05["drop_ending_A"]["ending_A"]
assert h05["drop_ending_A"]["mass"] == 0 and h05["drop_ending_A"]["moment_plus_length"] <= 0 and h05["drop_ending_A"]["ss"] <= 2
assert h05["drop_mass_zero"]["ending_A"] and h05["drop_mass_zero"]["mass"] != 0 and h05["drop_mass_zero"]["moment_plus_length"] <= 0 and h05["drop_mass_zero"]["ss"] <= 2
assert h05["drop_moment_bound"]["ending_A"] and h05["drop_moment_bound"]["mass"] == 0 and h05["drop_moment_bound"]["moment_plus_length"] > 0 and h05["drop_moment_bound"]["ss"] <= 2
assert h05["drop_ss_bound"]["ending_A"] and h05["drop_ss_bound"]["mass"] == 0 and h05["drop_ss_bound"]["moment_plus_length"] <= 0 and h05["drop_ss_bound"]["ss"] > 2
assert all(not row["strict_s_ended_p2_prefix_lengths"] for key, row in h05.items() if key != "positive")
out["H05"] = h05

print(json.dumps(out, indent=2, sort_keys=True))
