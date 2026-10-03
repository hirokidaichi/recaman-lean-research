#!/usr/bin/env python3
"""Fixed, seedless semantic checks for short_supply_donor_deletion.

This is independently written for the 02:30 audit.  It does not search for a new
conjecture and it does not reuse the earlier checker implementation.
"""
from itertools import combinations
import json


def cycle(word):
    return tuple(ch == "A" for ch in word)


def past(c, u, d):
    return tuple(c[(u - 1 - j) % len(c)] for j in range(d))


def p2(w):
    signs = tuple(1 if bit else -1 for bit in w)
    return sum(signs) == 1 and sum((j + 1) * x for j, x in enumerate(signs)) == 0


def minimal_p2_lag(c, u):
    # The declared fixed scan convention is inclusive d <= p(p+1).
    for d in range(1, len(c) * (len(c) + 1) + 1):
        if p2(past(c, u, d)):
            return d
    return None


def ss_count(w):
    return sum((not w[j]) and (not w[j + 1]) for j in range(len(w) - 1))


def s_phases(c):
    return tuple(j for j, bit in enumerate(c) if not bit)


def neighbors(c, entries, subset):
    p = len(c)
    covered = set()
    for u in subset:
        d = entries[u]
        for j in range(d):
            if not c[(u - 1 - j) % p]:
                covered.add((u - 1 - j) % p)
    return tuple(sorted(covered & set(s_phases(c))))


def true_oldest(c, u0):
    w = past(c, u0, 11)
    offsets = tuple(j + 1 for j, bit in enumerate(w) if not bit)
    return (u0 - max(offsets)) % len(c)


def oldest_offset(w):
    return max((j + 1 for j, bit in enumerate(w) if not bit), default=0)


def all_subsets(items):
    for size in range(len(items) + 1):
        yield from combinations(items, size)


def evaluate(label, word, u0=None, named_subset=()):
    c = cycle(word)
    entries = {
        u: minimal_p2_lag(c, u)
        for u, bit in enumerate(c)
        if bit and minimal_p2_lag(c, u) in (3, 7, 11)
    }
    U = tuple(sorted(entries))
    donor_word = past(c, u0, 11) if u0 is not None else ()
    donor_assumptions = {
        "specified": u0 is not None,
        "p2_at_11": u0 is not None and p2(donor_word),
        "minimal_at_11": u0 is not None and p2(donor_word)
            and all(not p2(donor_word[:d]) for d in range(1, 11)),
        "ss_count": ss_count(donor_word) if u0 is not None else None,
        "ss_eq_2": u0 is not None and ss_count(donor_word) == 2,
        "current_A": u0 is not None and c[u0],
        "u0_in_U": u0 in U if u0 is not None else False,
    }
    u_assumptions = {
        "positive_period": len(c) > 0,
        "nodup": len(U) == len(set(U)),
        "in_range": all(0 <= u < len(c) for u in U),
        "current_A": all(c[u] for u in U),
        "lags_3_7_11": all(entries[u] in (3, 7, 11) for u in U),
        "P2": all(p2(past(c, u, entries[u])) for u in U),
        "minimal": all(all(not p2(past(c, u, entries[u])[:d])
                           for d in range(1, entries[u])) for u in U),
    }
    target_premises = (
        all(u_assumptions.values())
        and donor_assumptions["p2_at_11"]
        and donor_assumptions["minimal_at_11"]
        and donor_assumptions["ss_eq_2"]
    )
    subset_rows = []
    if u0 is not None and donor_assumptions["p2_at_11"]:
        oldest = true_oldest(c, u0)
        for B in all_subsets(U):
            N = neighbors(c, entries, B)
            Nd = tuple(x for x in N if x != oldest)
            subset_rows.append({
                "B": B,
                "N": N,
                "deleted_N": Nd,
                "deletion_nonzero": len(Nd) < len(N),
                "hall_after_deletion": len(B) <= len(Nd),
                "contains_donor": u0 in B,
            })
    named_N = neighbors(c, entries, named_subset) if set(named_subset) <= set(U) else None
    return {
        "label": label,
        "word": word,
        "p": len(c),
        "u0": u0,
        "U": U,
        "lags": entries,
        "named_B": tuple(named_subset),
        "named_N": named_N,
        "oldest_phase": true_oldest(c, u0) if u0 is not None and donor_assumptions["p2_at_11"] else None,
        "oldest_offset": oldest_offset(donor_word) if u0 is not None else None,
        "fixed_offset_11_phase": (u0 - 11) % len(c) if u0 is not None else None,
        "fixed_offset_11_is_S": (not c[(u0 - 11) % len(c)]) if u0 is not None else None,
        "donor": donor_assumptions,
        "U_assumptions": u_assumptions,
        "target_premises": target_premises,
        "all_subsets_count": len(subset_rows),
        "all_deleted_hall": bool(subset_rows) and all(row["hall_after_deletion"] for row in subset_rows),
        "nonzero_deletion_rows": tuple(row for row in subset_rows if row["deletion_nonzero"]),
        "donor_containing_rows": tuple(row for row in subset_rows if row["contains_donor"]),
        "violations": tuple(row for row in subset_rows if not row["hall_after_deletion"]),
    }


cases = (
    ("Qp8", "SSAASAAA", 3, (7,)),
    ("Wp10", "SSAAAASAAA", None, (4, 7, 9)),
    ("properUp20", "SSAAAASAAAAAAAAASAAA", None, (4, 7, 9)),
    ("E240p18", "AAAASSAAAASAAASASS", 7, (2, 8, 11, 13)),
    ("falseoffsetp15", "AAAASAAASASASSS", 3, ()),
    ("SS3p12", "AAAASAAASSSS", 3, (7,)),
    ("nontightp11", "AAAASASASSS", 3, (5,)),
    ("Wnontightp8", "SSAAAASA", None, (7,)),
)

results = [evaluate(*case) for case in cases]

donor_words = tuple(map(cycle, (
    "AAASSSASASA", "ASAAASSSASA", "ASASAAASSSA", "ASSAAAASSAS",
    "ASSAAASAASS", "SAAASAASSSA", "SAAASSAAASS",
)))
donor_offset_control = tuple(oldest_offset(w) for w in donor_words)

# Exact fixed-control gates from the audit request.
q = results[0]
assert q["named_N"] == (4,) and q["oldest_phase"] == 0
assert q["target_premises"] and q["all_deleted_hall"] and not q["violations"]
assert q["donor"]["u0_in_U"]
assert any(row["contains_donor"] and row["deletion_nonzero"] for row in q["donor_containing_rows"])
e240 = results[3]
assert e240["named_N"] == (4, 5, 10, 17) and e240["oldest_phase"] == 14
assert e240["target_premises"] and e240["all_deleted_hall"]
false_offset = results[4]
assert false_offset["oldest_phase"] == 8 and (3 - 11) % 15 == 7
assert false_offset["oldest_offset"] == 10 and not false_offset["fixed_offset_11_is_S"]
assert donor_offset_control == (10, 10, 10, 11, 11, 10, 11)
assert all(results[5]["U_assumptions"].values())
assert results[5]["donor"]["p2_at_11"] and results[5]["donor"]["minimal_at_11"]
assert results[5]["donor"]["ss_count"] == 3 and not results[5]["target_premises"]
assert results[6]["target_premises"] and results[6]["all_deleted_hall"]

print(json.dumps({"all_seven_donor_oldest_offsets": donor_offset_control}, sort_keys=True))
print(json.dumps(results, sort_keys=True, indent=2))
print("PASS fixed deletion semantics: positive target instances, negative premise control, donor-containing subsets, and nonzero deletions")
