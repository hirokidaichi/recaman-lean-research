#!/usr/bin/env python3
"""Exact regression of the discovered minimum-kappa selection counterexample.
This is a fixed algebraic counterexample check, not a holdout of P2 itself.
"""
from fractions import Fraction
import hashlib
from pathlib import Path
import subprocess

word = 'SSASAAA'
eps = [1 if e == 'A' else -1 for e in word]
p, s = len(eps), sum(eps)
a = Fraction(p * s, 2)
b = sum((r + 1) * e for r, e in enumerate(eps)) - a
c = 0
kappa = []
for r, e in enumerate(eps):
    kappa.append(c - b * b / (4 * a))
    b += p * e
    c += (r + 1) * e
assert kappa == [Fraction(k, 56) for k in (-441, -105, -217, -49, -273, 7, -49)]
minima = [r for r, k in enumerate(kappa) if k == min(kappa)]
assert minima == [0] and eps[0] == -1
print('protocol=independent periodic audit; fixed counterexample regression; no holdout claim')
print('source_base_revision=612fcfaf74bfb49f3ae05a268057c82f70dcca26')
print('current_revision=' + subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
print('source_sha256=' + hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
print('word=' + word + ' period=' + str(p) + ' sign_sum=' + str(s))
print('kappa=' + ','.join(str(k) for k in kappa))
print('minimum_indices=' + str(minima) + ' outgoing_signs=S')
print('PASS: minimum-kappa choice rule REFUTED; all-period P2 lemma not refuted')
