#!/usr/bin/env python3
"""Bounded semantic audit for the already-frozen H-05 word lemma ranges."""

import itertools
import json


def stats(word):
    mass = 0
    moment = 0
    prefixes = []
    for index, sign in enumerate(word, 1):
        value = 1 if sign == "A" else -1
        mass += value
        moment += index * value
        if index < len(word) and sign == "S" and mass == 1 and moment == 0:
            prefixes.append(index)
    ss = sum(left == right == "S" for left, right in zip(word, word[1:]))
    return mass, moment, ss, prefixes


def words(length):
    return map("".join, itertools.product("AS", repeat=length))


premise_examples = []
strict_count = 0
equality_count = 0
inequality_checks = {"ending_A_budget": 0, "ending_AA_ss2": 0}
controls = {}

for length in range(1, 19):
    for word in words(length):
        mass, moment, ss, prefixes = stats(word)
        if word.endswith("A"):
            for budget in range(ss, 5):
                inequality_checks["ending_A_budget"] += 1
                assert budget + 1 <= moment + budget * length, (word, budget)
        if word.endswith("AA") and ss <= 2:
            inequality_checks["ending_AA_ss2"] += 1
            assert 5 <= moment + length, word

        conclusion = bool(prefixes)
        target = word.endswith("A") and mass == 0 and moment + length <= 0 and ss <= 2
        if target:
            assert conclusion, word
            (strict_count if moment + length < 0 else equality_count)
            if moment + length < 0:
                strict_count += 1
            else:
                equality_count += 1
            if len(premise_examples) < 8:
                premise_examples.append(
                    dict(word=word, length=length, mass=mass, moment=moment,
                         moment_plus_length=moment + length, ss=ss, prefixes=prefixes)
                )

        candidates = {
            "drop_ending_A": mass == 0 and moment + length <= 0 and ss <= 2,
            "drop_mass_zero": word.endswith("A") and moment + length <= 0 and ss <= 2,
            "drop_moment_bound": word.endswith("A") and mass == 0 and ss <= 2,
            "drop_ss_bound": word.endswith("A") and mass == 0 and moment + length <= 0,
        }
        for name, premise in candidates.items():
            if name not in controls and premise and not conclusion:
                if name == "drop_ending_A" and word.endswith("A"):
                    continue
                if name == "drop_mass_zero" and mass == 0:
                    continue
                if name == "drop_moment_bound" and moment + length <= 0:
                    continue
                if name == "drop_ss_bound" and ss <= 2:
                    continue
                controls[name] = dict(
                    word=word, length=length, mass=mass, moment=moment,
                    moment_plus_length=moment + length, ss=ss, prefixes=prefixes)

print(json.dumps(dict(
    status="PASS",
    range="all binary words of lengths 1..18",
    target_count=strict_count + equality_count,
    strict_inequality_count=strict_count,
    equality_count=equality_count,
    examples=premise_examples,
    inequality_checks=inequality_checks,
    negative_controls=controls,
), sort_keys=True))
