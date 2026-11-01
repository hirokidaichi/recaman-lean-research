#!/usr/bin/env python3
"""Recompute one frozen H-20260920-04 literal, without discovery inputs."""
import itertools
import json


WORD = "SAAASSSASASASAAA"
P = len(WORD)
DONOR = 15
B = (3,)
LAG = {3: 3}
CUTOFF = P * (P + 1)


def sign(t):
    return 1 if WORD[t % P] == "A" else -1


def past(t, d):
    return "".join(WORD[(t - i) % P] for i in range(1, d + 1))


def mass(w):
    return sum(1 if bit == "A" else -1 for bit in w)


def moment(w):
    return sum(i * (1 if bit == "A" else -1) for i, bit in enumerate(w, 1))


def p2(w):
    return mass(w) == 1 and moment(w) == 0


def ss_count(w):
    return sum(w[i:i + 2] == "SS" for i in range(len(w) - 1))


def neighborhood(assignments):
    return sorted({(u - i) % P for u, d in assignments.items()
                   for i in range(1, d + 1) if sign(u - i) == -1})


def first_supply(u):
    return next((d for d in range(1, CUTOFF + 1) if p2(past(u, d))), None)


assert P == 16
assert all(sign(t + P) == sign(t) for t in range(-2 * P, 2 * P + 1))
donor_word = past(DONOR, 15)
assert donor_word == "AASASASASSSAAAS"
assert sign(DONOR) == 1 and mass(donor_word) == 1 and moment(donor_word) == 0
assert ss_count(donor_word) == 2
prefixes = [d for d in range(1, 15) if p2(donor_word[:d])]
assert prefixes == [3]
assert B == (3,) and DONOR not in B and sign(3) == 1
assert past(3, 3) == "AAS" and p2(past(3, 3))
assert all(not p2(past(3, d)) for d in range(1, 3))
assert len(B) == len(neighborhood(LAG)) == 1
assert sum(sign(t) for t in range(P)) == 2
oldest_offset = max(i for i, bit in enumerate(donor_word, 1) if bit == "S")
oldest_phase = (DONOR - oldest_offset) % P
assert oldest_offset == 15 and oldest_phase == 0
N = neighborhood(LAG)
deleted = [s for s in N if s != oldest_phase]
assert N == [0] and deleted == []

full = {u: first_supply(u) for u in range(P) if sign(u) == 1}
full = {u: d for u, d in full.items() if d is not None}
assert full == {1: 11, 3: 3, 11: 39, 15: 3}
assert all(d <= CUTOFF for d in full.values())
hall_subsets = 0
for k in range(len(full) + 1):
    for subset in itertools.combinations(full, k):
        hall_subsets += 1
        assert k <= len(neighborhood({u: full[u] for u in subset}))
assert hall_subsets == 16
assert all(len(subset) <= len(neighborhood({u: LAG[u] for u in subset}))
           for k in range(len(B) + 1) for subset in itertools.combinations(B, k))

print(json.dumps({
    "word": WORD, "period": P, "period_mass": sum(sign(t) for t in range(P)),
    "donor": DONOR, "donor_current_A": True, "donor_past15": donor_word,
    "donor_mass": mass(donor_word), "donor_moment": moment(donor_word),
    "donor_ss_count": ss_count(donor_word), "donor_proper_P2_prefixes": prefixes,
    "B": list(B), "B_past3": past(3, 3), "B_current_A": True,
    "B_minimal_lag": 3, "B_tight": True, "B_neighborhood": N,
    "true_oldest_offset": oldest_offset, "true_oldest_phase": oldest_phase,
    "deleted_neighborhood": deleted, "avoidance_conclusion": oldest_phase not in N,
    "deletion_Hall_conclusion": len(B) <= len(deleted),
    "full_U_least_lag": full, "full_U_Hall_subsets_checked": hall_subsets,
    "cutoff_inclusive": CUTOFF, "fixed_offset11_phase": (DONOR - 11) % P,
    "fixed_offset11_is_true_oldest": (DONOR - 11) % P == oldest_phase,
}, sort_keys=True))
