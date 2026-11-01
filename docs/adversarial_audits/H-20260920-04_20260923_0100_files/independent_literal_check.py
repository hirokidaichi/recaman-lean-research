#!/usr/bin/env python3
"""Independent literal check of H-20260920-04, without repository checker imports."""

from itertools import combinations
import json

chronological = "SAAASSSASASASAAA"
p = len(chronological)


def bit(t):
    return chronological[t % p]


def past(t, d):
    return "".join(bit(t - i) for i in range(1, d + 1))


def mass(w):
    return sum(1 if c == "A" else -1 for c in w)


def moment(w):
    return sum(i * (1 if c == "A" else -1) for i, c in enumerate(w, 1))


def p2(w):
    return mass(w) == 1 and moment(w) == 0


def ss_count(w):
    return sum(w[i:i+2] == "SS" for i in range(len(w) - 1))


def neighborhood(members, lags):
    subtraction_phases = {s for s in range(p) if bit(s) == "S"}
    return sorted(subtraction_phases & {
        (u - i) % p for u in members for i in range(1, lags[u] + 1)
        if bit(u - i) == "S"
    })


def all_subsets(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


assert p == 16
assert all(bit(t + p) == bit(t) for t in range(-2*p, 2*p))
assert mass(past(0, p)) == 2
donor, length = 15, 15
w = past(donor, length)
prefixes = [d for d in range(1, length) if p2(past(donor, d))]
oldest_offset = max(i for i, c in enumerate(w, 1) if c == "S")
oldest_phase = (donor - oldest_offset) % p
assert bit(oldest_phase) == "S"
assert all(c == "A" for c in w[oldest_offset:])

B = (3,)
B_lags = {3: 3}
assert p > 0 and len(set(B)) == len(B)
assert all(0 <= u < p and bit(u) == "A" and B_lags[u] <= 11 for u in B)
assert donor not in B
N = neighborhood(B, B_lags)
deleted = [s for s in N if s != oldest_phase]
local_hall = all(len(sub) <= len(neighborhood(sub, B_lags)) for sub in all_subsets(B))

bound = p*(p+1)
add_phases = [u for u in range(p) if bit(u) == "A"]
least = {}
for u in add_phases:
    found = next((d for d in range(1, bound + 1) if p2(past(u, d))), None)
    if found is not None:
        least[u] = found
U = sorted(least)
hall = []
for sub in all_subsets(U):
    neighborhood_sub = neighborhood(sub, least)
    hall.append({"members": list(sub), "neighborhood": neighborhood_sub,
                 "holds": len(sub) <= len(neighborhood_sub)})

result = {
    "literal": chronological,
    "period": p,
    "periodic_sample": True,
    "period_mass": mass(chronological),
    "period_mass_backward": mass(past(0, p)),
    "donor": donor,
    "donor_current": bit(donor),
    "donor_past15": w,
    "donor_mass": mass(w),
    "donor_moment": moment(w),
    "donor_p2": p2(w),
    "donor_ss2": ss_count(w),
    "proper_p2_prefixes": prefixes,
    "proper_prefix_data": [{"d": d, "mass": mass(past(donor, d)),
                             "moment": moment(past(donor, d))} for d in range(1, length)],
    "oldest_offset": oldest_offset,
    "oldest_phase": oldest_phase,
    "B": list(B),
    "B_current": [bit(u) for u in B],
    "B_words": [past(u, B_lags[u]) for u in B],
    "B_p2": [p2(past(u, B_lags[u])) for u in B],
    "B_minimal": [not any(p2(past(u, d)) for d in range(1, B_lags[u])) for u in B],
    "B_local_hall": local_hall,
    "N": N,
    "tight": len(N) == len(B),
    "oldest_in_N": oldest_phase in N,
    "deleted_N": deleted,
    "deletion_hall": len(B) <= len(deleted),
    "fixed_offset11_phase": (donor - 11) % p,
    "fixed_offset11_deleted_N": [s for s in N if s != (donor - 11) % p],
    "fixed_offset11_avoidance": (donor - 11) % p not in N,
    "fixed_offset11_deletion_hall": len(B) <= len([s for s in N if s != (donor - 11) % p]),
    "full_U_bound": bound,
    "current_A_phases": add_phases,
    "current_A_count": len(add_phases),
    "full_U": U,
    "supplied_phase_count": len(U),
    "least_lags": least,
    "hall_subsets": len(hall),
    "hall_all": all(row["holds"] for row in hall),
    "hall_rows": hall,
}

assert result["period_mass"] == 2
assert result["donor_current"] == "A"
assert result["donor_p2"] and result["donor_ss2"] == 2
assert result["proper_p2_prefixes"] == [3]
assert result["B_words"] == ["AAS"] and result["B_p2"] == [True]
assert result["B_minimal"] == [True]
assert local_hall
assert N == [0] and result["tight"]
assert oldest_phase == 0 and result["oldest_in_N"]
assert deleted == [] and not result["deletion_hall"]
assert result["fixed_offset11_avoidance"] and result["fixed_offset11_deletion_hall"]
assert U == [1, 3, 11, 15]
assert len(add_phases) == 9 and len(U) == 4
assert least == {1: 11, 3: 3, 11: 39, 15: 3}
assert result["hall_all"]
print(json.dumps(result, ensure_ascii=False, sort_keys=True, indent=2))
