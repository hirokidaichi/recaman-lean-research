#!/usr/bin/env python3
import itertools
import json


def stats(bits):
    xs = [1 if b else -1 for b in bits]
    mass = sum(xs)
    moment = sum((i + 1) * x for i, x in enumerate(xs))
    ss = sum(not bits[i] and not bits[i + 1] for i in range(len(bits) - 1))
    prefix = any((not bits[k - 1]) and sum(xs[:k]) == 1 and
                 sum((i + 1) * x for i, x in enumerate(xs[:k])) == 0
                 for k in range(1, len(bits)))
    return mass, moment, ss, prefix


q_count = aa_count = eq = strict = 0
controls = {x: None for x in ("ending_A", "mass_zero", "moment_bound", "ss_bound")}
for n in range(1, 19):
    for bits in itertools.product((False, True), repeat=n):
        mass, moment, ss, prefix = stats(bits)
        ending = bits[-1]
        if ending:
            for q in range(ss, 5):
                assert q + 1 <= moment + q * n
                q_count += 1
        if n >= 2 and bits[-2:] == (True, True) and ss <= 2:
            assert 5 <= moment + n
            aa_count += 1
        ps = dict(ending_A=ending, mass_zero=mass == 0,
                  moment_bound=moment + n <= 0, ss_bound=ss <= 2)
        if all(ps.values()):
            assert prefix
            if moment + n == 0: eq += 1
            else:
                assert moment + n < 0
                strict += 1
        for dropped in controls:
            if controls[dropped] is None and (not ps[dropped]) and all(v for k, v in ps.items() if k != dropped) and not prefix:
                controls[dropped] = dict(word="".join("A" if b else "S" for b in bits), mass=mass,
                                         moment_plus_length=moment+n, ss=ss, conclusion=prefix)

print(json.dumps(dict(all_binary_max_length=18, q_values="actual_ss..4",
                      q_budget_count=q_count, aa_count=aa_count,
                      target_equality=eq, target_strict=strict,
                      controls=controls, seed=None), sort_keys=True, indent=2))
