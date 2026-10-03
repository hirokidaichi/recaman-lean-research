#!/usr/bin/env python3
import itertools
import json


def vals(bits):
    signs = [1 if b else -1 for b in bits]
    mass = sum(signs)
    moment = sum((i + 1) * x for i, x in enumerate(signs))
    ss = sum((not bits[i]) and (not bits[i + 1]) for i in range(len(bits) - 1))
    return mass, moment, ss


budget_checked = budget_bad = aa_checked = aa_bad = 0
budget_equal = aa_equal = None
for n in range(1, 13):
    for prefix in itertools.product((False, True), repeat=n - 1):
        bits = prefix + (True,)
        mass, moment, ss = vals(bits)
        for q in range(5):
            if ss <= q:
                budget_checked += 1
                lhs, rhs = q + 1, moment + q * n
                budget_bad += lhs > rhs
                if lhs == rhs and budget_equal is None:
                    budget_equal = dict(word="".join("A" if b else "S" for b in bits), q=q, ss=ss, lhs=lhs, rhs=rhs)
        if n >= 2 and bits[-2:] == (True, True) and ss <= 2:
            aa_checked += 1
            lhs, rhs = 5, moment + n
            aa_bad += lhs > rhs
            if lhs == rhs and aa_equal is None:
                aa_equal = dict(word="".join("A" if b else "S" for b in bits), ss=ss, lhs=lhs, rhs=rhs)

print(json.dumps(dict(cutoff=12, q_values=list(range(5)),
  budget_checked=budget_checked, budget_failures=budget_bad, budget_equality_example=budget_equal,
  aa_checked=aa_checked, aa_failures=aa_bad, aa_equality_example=aa_equal), sort_keys=True, indent=2))
