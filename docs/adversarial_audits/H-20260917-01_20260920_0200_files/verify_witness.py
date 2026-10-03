#!/usr/bin/env python3
"""Independent verifier/search for the slot0200 partial-U model."""

from itertools import combinations, product
import json
import sys


def choices(xs):
    xs = tuple(xs)
    for n in range(len(xs) + 1):
        yield from combinations(xs, n)


def sign(c):
    return 1 if c == "A" else -1


def history(word, clock, length):
    return tuple(word[(clock - j) % len(word)] for j in range(1, length + 1))


def balanced_return(window):
    return sum(sign(c) for c in window) == 1 and sum(
        j * sign(c) for j, c in enumerate(window, 1)
    ) == 0


def first_returns(word):
    ans = {}
    p = len(word)
    for u, c in enumerate(word):
        if c != "A":
            continue
        for d in range(1, p * (p + 1) + 1):
            w = history(word, u, d)
            if balanced_return(w):
                ans[u] = (d, w)
                break
    return ans


def covered(word, supply, members):
    p = len(word)
    return frozenset(
        (u - j) % p
        for u in members
        for j in range(1, supply[u][0] + 1)
        if word[(u - j) % p] == "S"
    )


def hall(word, supply, universe):
    failures = []
    rows = []
    for x in choices(universe):
        nx = covered(word, supply, x)
        row = (x, tuple(sorted(nx)))
        rows.append(row)
        if len(x) > len(nx):
            failures.append(row)
    return not failures, rows, failures


def verify(obj):
    w = obj["witness"] if "witness" in obj else obj
    p = w["period"]
    word = w["word"]
    U = tuple(w["U"])
    B = tuple(w["B"])
    t = w["t"]
    supply = first_returns(word)
    hall_u, hall_rows, hall_bad = hall(word, supply, U)
    hall_full, full_rows, full_bad = hall(word, supply, tuple(supply))
    checks = {
        "period_length": p == len(word) and p > 0,
        "alphabet": set(word) <= {"A", "S"},
        "positive_mass": sum(sign(c) for c in word) > 0,
        "U_nodup_sorted": len(U) == len(set(U)) and U == tuple(sorted(U)),
        "U_in_supply": set(U) <= set(supply),
        "U_proper": set(U) < set(supply),
        "hall_U": hall_u,
        "B_nonempty": bool(B),
        "B_sub_U": set(B) <= set(U) and len(B) == len(set(B)),
        "B_short": all(supply[b][0] in (3, 7) for b in B),
        "B_tight": len(covered(word, supply, B)) == len(B),
        "phase_member": t % p in B,
        "lag7": supply[t % p][0] == 7,
        "w1": "".join(history(word, t, 7)) == "SAAAASS",
        "next_S": word[(t + 1) % p] == "S",
        "full_Hall_false": not hall_full,
    }
    for shift in (-3 * p, -p, 0, p, 4 * p):
        checks[f"periodic_t_{shift:+d}"] = (
            history(word, t + shift, 7) == history(word, t, 7)
            and word[(t + shift + 1) % p] == word[(t + 1) % p]
            and (t + shift) % p == t % p
        )
    return {
        "checks": checks,
        "all_required": all(checks.values()),
        "supply": {str(u): {"lag": d, "window": "".join(win),
                              "cover": sorted(covered(word, supply, (u,)))}
                   for u, (d, win) in supply.items()},
        "hall_U": [{"subset": list(x), "N": list(nx)} for x, nx in hall_rows],
        "hall_U_failures": [{"subset": list(x), "N": list(nx)} for x, nx in hall_bad],
        "full_hall": hall_full,
        "full_hall_failures": [{"subset": list(x), "N": list(nx)} for x, nx in full_bad],
        "N_B": sorted(covered(word, supply, B)),
    }


def search(limit=11):
    # Independent ordering: A precedes S, then U before B.
    for p in range(1, limit + 1):
        for letters in product("AS", repeat=p):
            word = "".join(letters)
            if sum(sign(c) for c in word) <= 0:
                continue
            supply = first_returns(word)
            full = tuple(supply)
            for U in choices(full):
                if not U or len(U) == len(full):
                    continue
                hu, _, _ = hall(word, supply, U)
                if not hu:
                    continue
                for B in choices(U):
                    if not B or any(supply[b][0] not in (3, 7) for b in B):
                        continue
                    if len(covered(word, supply, B)) != len(B):
                        continue
                    for t in range(p):
                        if (t in B and supply[t][0] == 7
                                and "".join(history(word, t, 7)) == "SAAAASS"
                                and word[(t + 1) % p] == "S"):
                            return {"period": p, "word": word, "U": list(U),
                                    "B": list(B), "t": t}
    return None


def census(limit=11):
    stats = {
        "positive_words": 0,
        "proper_U": 0,
        "proper_U_hall": 0,
        "partial_tight_B": 0,
        "partial_w1_antecedents": 0,
        "partial_w1_violations": 0,
        "full_hall_words": 0,
        "full_tight_B": 0,
        "full_w1_antecedents": 0,
        "full_w1_violations": 0,
        "full_w1_B_equals_full_U": 0,
    }
    for p in range(1, limit + 1):
        for letters in product("AS", repeat=p):
            word = "".join(letters)
            if sum(sign(c) for c in word) <= 0:
                continue
            stats["positive_words"] += 1
            supply = first_returns(word)
            full = tuple(supply)
            full_ok, _, _ = hall(word, supply, full)
            if full_ok:
                stats["full_hall_words"] += 1
                for B in choices(full):
                    if not B or any(supply[b][0] not in (3, 7) for b in B):
                        continue
                    if len(covered(word, supply, B)) != len(B):
                        continue
                    stats["full_tight_B"] += 1
                    for t in B:
                        if supply[t][0] == 7 and "".join(history(word, t, 7)) == "SAAAASS":
                            stats["full_w1_antecedents"] += 1
                            stats["full_w1_violations"] += word[(t + 1) % p] == "S"
                            stats["full_w1_B_equals_full_U"] += set(B) == set(full)
            for U in choices(full):
                if len(U) == len(full):
                    continue
                stats["proper_U"] += 1
                hu, _, _ = hall(word, supply, U)
                if not hu:
                    continue
                stats["proper_U_hall"] += 1
                for B in choices(U):
                    if not B or any(supply[b][0] not in (3, 7) for b in B):
                        continue
                    if len(covered(word, supply, B)) != len(B):
                        continue
                    stats["partial_tight_B"] += 1
                    for t in B:
                        if supply[t][0] == 7 and "".join(history(word, t, 7)) == "SAAAASS":
                            stats["partial_w1_antecedents"] += 1
                            stats["partial_w1_violations"] += word[(t + 1) % p] == "S"
    return stats


def controls():
    rows = {}
    for label, word, U, B, t in (
        ("full_positive", "SSAAAASAAA", (4, 7, 9), (4, 7, 9), 7),
        ("drop_tightness", "SSAAAASA", (4, 7), (7,), 7),
    ):
        supply = first_returns(word)
        hall_ok, _, hall_bad = hall(word, supply, U)
        rows[label] = {
            "word": word,
            "supply": {str(u): supply[u][0] for u in supply},
            "U": list(U),
            "B": list(B),
            "hall_U": hall_ok,
            "hall_failures": [[list(x), list(nx)] for x, nx in hall_bad],
            "N_B": sorted(covered(word, supply, B)),
            "tight_B": len(covered(word, supply, B)) == len(B),
            "past7": "".join(history(word, t, 7)),
            "next": word[(t + 1) % len(word)],
            "negative_clock_same": (
                history(word, t - 3 * len(word), 7) == history(word, t, 7)
                and word[(t - 3 * len(word) + 1) % len(word)] == word[(t + 1) % len(word)]
                and (t - 3 * len(word)) % len(word) == t % len(word)
            ),
        }
    return rows


if __name__ == "__main__":
    if len(sys.argv) == 2:
        with open(sys.argv[1], encoding="utf-8") as handle:
            witness = next(json.loads(line) for line in handle if '"kind":"witness"' in line)
        print(json.dumps(verify(witness), sort_keys=True, indent=2))
    else:
        candidate = search()
        print(json.dumps({"independent_candidate": candidate}, sort_keys=True))
        if candidate is not None:
            print(json.dumps(verify(candidate), sort_keys=True, indent=2))
        print(json.dumps({"independent_census": census()}, sort_keys=True))
        print(json.dumps({"controls": controls()}, sort_keys=True))
