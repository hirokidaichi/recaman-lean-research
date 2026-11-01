#!/usr/bin/env python3
"""Independent Q/W premise and negated-conclusion controls.

Newest-first windows; A=True, S=False.  These are named regression examples,
not a holdout and not a mathematical proof.
"""

from itertools import combinations
import json


def bits(s):
    return tuple(c == "A" for c in s)


def text(w):
    return "".join("A" if b else "S" for b in w)


def past(cycle, t, d):
    return tuple(cycle[(t - 1 - i) % len(cycle)] for i in range(d))


def p2(w):
    signs = [1 if b else -1 for b in w]
    return sum(signs) == 1 and sum((i + 1) * x for i, x in enumerate(signs)) == 0


def minimal(w):
    return p2(w) and all(not p2(w[:d]) for d in range(1, len(w)))


def ss_count(w):
    return sum(not w[i] and not w[i + 1] for i in range(len(w) - 1))


def s_offsets(w):
    return [i + 1 for i, b in enumerate(w) if not b]


def oldest(w):
    return max(s_offsets(w), default=0)


def minimal_lag(cycle, t, cap=None):
    cap = cap or len(cycle) * (len(cycle) + 1)
    for d in range(1, cap + 1):
        if p2(past(cycle, t, d)):
            return d
    return None


def supply(cycle):
    out = {}
    for t, b in enumerate(cycle):
        if not b:
            continue
        d = minimal_lag(cycle, t)
        if d is None:
            continue
        w = past(cycle, t, d)
        out[t] = (d, text(w), sorted({(t - k) % len(cycle) for k in s_offsets(w)}))
    return out


def neigh(sup, bset):
    return sorted(set().union(*(set(sup[b][2]) for b in bset))) if bset else []


def hall(sup, universe):
    for r in range(len(universe) + 1):
        for subset in combinations(universe, r):
            if len(neigh(sup, subset)) < len(subset):
                return False
    return True


def q_case(name, cycle_text, bset, u0):
    c = bits(cycle_text)
    sup = supply(c)
    donor = past(c, u0, 11)
    n = neigh(sup, bset)
    true_oldest = (u0 - oldest(donor)) % len(c)
    return {
        "name": name,
        "period": len(c),
        "word": cycle_text,
        "B": bset,
        "N": n,
        "B_nodup": len(set(bset)) == len(bset),
        "tight": len(n) == len(bset),
        "B_lt_p": all(b < len(c) for b in bset),
        "B_additions": all(c[b] for b in bset),
        "B_lags": [sup[b][0] for b in bset],
        "B_lag_3_7_11": all(sup[b][0] in (3, 7, 11) for b in bset),
        "B_P2": all(p2(past(c, b, sup[b][0])) for b in bset),
        "B_minimal": all(minimal(past(c, b, sup[b][0])) for b in bset),
        "hall_B": hall(sup, bset),
        "donor": text(donor),
        "donor_P2": p2(donor),
        "donor_minimal": minimal(donor),
        "donor_ss_count": ss_count(donor),
        "oldest_offset": oldest(donor),
        "true_oldest_phase": true_oldest,
        "conclusion_avoids": true_oldest not in n,
    }


positive_q = q_case("Qp8", "SSAASAAA", [7], 3)
drop_ss2 = q_case("drop_ss2", "AAAASAAASSSS", [7], 3)
drop_tight = q_case("drop_tight", "AAAASASASSS", [5], 3)

assert all(positive_q[k] for k in (
    "B_nodup", "tight", "B_lt_p", "B_additions", "B_lag_3_7_11", "B_P2",
    "B_minimal", "hall_B", "donor_P2", "donor_minimal", "conclusion_avoids"
))
assert positive_q["donor_ss_count"] == 2
assert positive_q["B"] == [7] and positive_q["N"] == [4]
assert drop_ss2["donor"] == "AAASSSSAAAS"
assert drop_ss2["donor_ss_count"] == 3 and not drop_ss2["conclusion_avoids"]
assert drop_ss2["tight"] and drop_ss2["N"] == [4]
assert drop_tight["donor"] == "AAASSSASASA"
assert drop_tight["donor_ss_count"] == 2 and not drop_tight["tight"]
assert not drop_tight["conclusion_avoids"] and drop_tight["N"] == [4, 9, 10]

# W positive and deletion of tight/onto: the same w1 occurs at t=7.
w_pos_c = bits("SSAAAASAAA")
w_pos_sup = supply(w_pos_c)
w_pos_b = [4, 7, 9]
assert w_pos_sup[7][1] == "SAAAASS"
assert len(neigh(w_pos_sup, w_pos_b)) == len(w_pos_b)
assert w_pos_c[(7 + 1) % len(w_pos_c)]

w_neg_c = bits("SSAAAASA")
w_neg_sup = supply(w_neg_c)
assert w_neg_sup[7][1] == "SAAAASS"
assert not w_neg_c[(7 + 1) % len(w_neg_c)]
assert len(neigh(w_neg_sup, [7])) != 1

# A singleton w1 member with own(7)=0 satisfies window/addA/own_mem but not onto:
# its three S clocks are 6,1,0, while the one owner value is 0.
w_neg_offsets = s_offsets(bits("SAAAASS"))
assert w_neg_offsets == [1, 6, 7]
assert 7 - 7 == 0
assert {7 - k for k in w_neg_offsets} == {6, 1, 0}

# If ownership were a multivalued relation, the same singleton could relate to all
# three clocks, so function-valued ownership is a real dependency.
multivalued_relation = {(7, 7 - k) for k in w_neg_offsets}
assert {s for _, s in multivalued_relation} == {6, 1, 0}

# Direct nonempty line-model realization of all four OwnerFamily fields.
# Bits are fixed by AAS at -3, w1 at 0, and AAS at 2.
local_members = {-3: bits("AAS"), 0: bits("SAAAASS"), 2: bits("AAS")}
local_own = {-3: -6, 0: -7, 2: -1}
local_env = {}
for endpoint, window in local_members.items():
    placements = [(endpoint, True)] + [
        (endpoint - 1 - i, bit) for i, bit in enumerate(window)
    ]
    for clock, bit in placements:
        assert clock not in local_env or local_env[clock] == bit
        local_env[clock] = bit
for endpoint, window in local_members.items():
    assert local_env[endpoint]
    assert local_own[endpoint] in {endpoint - k for k in s_offsets(window)}
    for k in s_offsets(window):
        target = endpoint - k
        assert any(local_own[owner] == target for owner in local_members)
assert local_own[0] == -7 and local_env[1]

out = {
    "positive_Q": positive_q,
    "negative_Q_drop_ss2": drop_ss2,
    "negative_Q_drop_tight": drop_tight,
    "positive_W": {"period": 10, "B": w_pos_b, "N": neigh(w_pos_sup, w_pos_b), "next": "A"},
    "negative_W_drop_tight_onto": {
        "period": 8, "B": [7], "N": neigh(w_neg_sup, [7]), "next": "S",
        "window": w_neg_sup[7][1], "own_single": 0, "window_S_clocks": [6, 1, 0],
    },
    "negative_W_multivalued_owner": sorted(multivalued_relation),
    "positive_W_owner_family": {
        "members": sorted(local_members),
        "windows": {str(k): text(v) for k, v in local_members.items()},
        "own": local_own,
        "next": "A" if local_env[1] else "S",
    },
}

print(json.dumps(out, indent=2, sort_keys=True))
print("PASS: premise matrix and negated-conclusion controls")
