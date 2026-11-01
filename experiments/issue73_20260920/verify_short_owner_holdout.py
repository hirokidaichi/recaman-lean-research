#!/usr/bin/env python3
"""Same-session verification with independent supply and Hall algorithms.

No imports from research probes. Supply uses a closed formula for repeating
periods; Hall uses every subset, not a matching algorithm. This is independent
implementation, not a separate-agent audit.
"""
import hashlib
import json
import random
import time


def supply_by_period_formula(bits, p):
    rows = []
    for u in range(p):
        if not (bits >> u & 1):
            continue
        signs = [1 if bits >> ((u - k) % p) & 1 else -1 for k in range(1, p + 1)]
        masses = [0]
        moments = [0]
        for k, sign in enumerate(signs, 1):
            masses.append(masses[-1] + sign)
            moments.append(moments[-1] + k * sign)
        for d in range(1, p * (p + 1) + 1):
            q, r = divmod(d, p)
            mass = q * masses[p] + masses[r]
            moment = (q * moments[p] + p * masses[p] * q * (q - 1) // 2
                      + moments[r] + q * p * masses[r])
            if mass == 1 and moment == 0:
                w = [signs[(k - 1) % p] for k in range(1, d + 1)]
                offsets = [k for k, sign in enumerate(w, 1) if sign == -1]
                mask = 0
                for k in offsets:
                    mask |= 1 << ((u - k) % p)
                ss = sum(w[i] == w[i + 1] == -1 for i in range(d - 1))
                rows.append(dict(u=u, d=d, word=w, mask=mask, ss=ss,
                                 oldest=(u - max(offsets)) % p))
                break
    return rows


def check_formula():
    comparisons = 0
    for p in range(1, 7):
        for bits in range(1 << p):
            for u in range(p):
                signs = [1 if bits >> ((u - k) % p) & 1 else -1 for k in range(1, p + 1)]
                S = sum(signs)
                T = sum(k * sign for k, sign in enumerate(signs, 1))
                for d in range(0, p * (p + 1) + 1):
                    q, r = divmod(d, p)
                    sr = sum(signs[:r])
                    tr = sum(k * sign for k, sign in enumerate(signs[:r], 1))
                    direct = [signs[k % p] for k in range(d)]
                    assert q * S + sr == sum(direct)
                    assert (q * T + p * S * q * (q - 1) // 2 + tr + q * p * sr
                            == sum(k * sign for k, sign in enumerate(direct, 1)))
                    comparisons += 1
    return comparisons


def run():
    start = time.monotonic()
    print(json.dumps({"kind": "formula_check", "comparisons": check_formula()}), flush=True)
    rng = random.Random(2026091801)
    for p in (32, 33):
        distinct = set()
        digest = hashlib.sha256()
        count = dict(period=p, accepted=0, draws=0, hall_words=0, donor_words=0,
                     donors=0, tight_short_subsets=0, Q_cases=0, Q_nonempty=0,
                     W_cases=0, Q_violations=0, W_violations=0, max_full_U=0)
        while len(distinct) != 2000:
            bits = rng.getrandbits(p)
            count["draws"] += 1
            if bits.bit_count() * 2 <= p or bits in distinct:
                continue
            distinct.add(bits)
            cycle = "".join("A" if bits >> u & 1 else "S" for u in range(p))
            digest.update((cycle + "\n").encode())
            count["accepted"] += 1
            rows = supply_by_period_formula(bits, p)
            count["max_full_U"] = max(count["max_full_U"], len(rows))
            donors = [x for x in rows if x["d"] == 11 and x["ss"] == 2]
            count["donor_words"] += bool(donors)
            count["donors"] += len(donors)
            # Explicitly reconstruct every subset from its bits: no dynamic union table.
            for mask in range(1 << len(rows)):
                B = [row for j, row in enumerate(rows) if mask >> j & 1]
                N = 0
                for row in B:
                    N |= row["mask"]
                assert len(B) <= N.bit_count(), ("Hall", cycle, B)
                if len(B) != N.bit_count() or any(x["d"] not in (3, 7, 11) for x in B):
                    continue
                count["tight_short_subsets"] += 1
                members = {x["u"] for x in B}
                for donor in donors:
                    if donor["u"] in members:
                        continue
                    count["Q_cases"] += 1
                    count["Q_nonempty"] += bool(B)
                    assert not (N >> donor["oldest"] & 1), ("Q", cycle, B, donor)
                for row in B:
                    if row["word"] == [-1, 1, 1, 1, 1, -1, -1]:
                        count["W_cases"] += 1
                        assert bits >> ((row["u"] + 1) % p) & 1, ("W", cycle, B, row)
            count["hall_words"] += 1
        count["sample_sha256"] = digest.hexdigest()
        assert count["accepted"] == 2000 and count["donor_words"] >= 20
        assert count["W_cases"] and count["Q_nonempty"]
        print(json.dumps({"kind": "period_complete", **count}), flush=True)
    print(json.dumps({"status": "PASS", "elapsed_seconds": time.monotonic() - start}), flush=True)


if __name__ == "__main__":
    run()
