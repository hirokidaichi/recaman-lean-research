#!/usr/bin/env python3
"""Independent exhaustive check for the original H-03 finite protocol."""
import argparse
import hashlib
import itertools
import json


def p2(bits):
    values = tuple(1 if x else -1 for x in bits)
    return sum(values) == 1 and sum((i + 1) * v for i, v in enumerate(values)) == 0


def window(cycle, phase, length):
    size = len(cycle)
    return tuple(cycle[(phase - i) % size] for i in range(1, length + 1))


def neighborhood(cycle, assigned):
    size = len(cycle)
    return frozenset((b - i) % size for b, length in assigned
                     for i in range(1, length + 1) if not cycle[(b - i) % size])


def run_period(size):
    counts = dict(cycles=0, assignments=0, nonminimal=0, tight=0,
                  tight_nonminimal=0, strict_nonminimal=0,
                  tight_strict_nonminimal=0, changed_nontight=0,
                  donor_checks=0, deletion_checks=0)
    examples = {}
    digest = hashlib.sha256()
    for mask in range(1 << size):
        cycle = tuple(bool(mask & (1 << i)) for i in range(size))
        digest.update(("".join("A" if bit else "S" for bit in cycle) + "\n").encode())
        counts["cycles"] += 1
        choices = []
        for phase in range(size):
            if not cycle[phase]:
                continue
            valid = tuple(length for length in (3, 7, 11)
                          if p2(window(cycle, phase, length)))
            if valid:
                choices.append((None,) + tuple((phase, length, valid[0]) for length in valid))
        donors = []
        for phase in range(size):
            w = window(cycle, phase, 11)
            if p2(w) and sum(not w[i] and not w[i + 1] for i in range(10)) == 2:
                oldest = max(i for i, bit in enumerate(w, 1) if not bit)
                donors.append((phase, (phase - oldest) % size))
        for combination in itertools.product(*choices):
            records = tuple(x for x in combination if x is not None)
            if not records:
                continue
            assert len({b for b, _, _ in records}) == len(records)
            assert all(cycle[b] and p2(window(cycle, b, d)) and m <= d <= 11
                       for b, d, m in records)
            assert all(p2(window(cycle, b, m)) and
                       all(not p2(window(cycle, b, k)) for k in range(1, m))
                       for b, _, m in records)
            counts["assignments"] += 1
            original = neighborhood(cycle, ((b, d) for b, d, _ in records))
            minimal = neighborhood(cycle, ((b, m) for b, _, m in records))
            nonminimal = any(m < d for _, d, m in records)
            strict = nonminimal and minimal != original
            tight = len(original) == len(records)
            assert minimal <= original
            assert len(minimal) >= len(records), (size, mask, records, minimal)
            counts["nonminimal"] += nonminimal
            counts["strict_nonminimal"] += strict
            counts["tight"] += tight
            counts["tight_nonminimal"] += tight and nonminimal
            counts["tight_strict_nonminimal"] += tight and strict
            counts["changed_nontight"] += not tight and minimal != original
            if tight:
                assert minimal == original, (size, mask, records, minimal, original)
            if strict and "strict_nonminimal" not in examples:
                examples["strict_nonminimal"] = dict(cycle="".join("A" if x else "S" for x in cycle),
                    assigned=records, N=sorted(original), M=sorted(minimal))
            if tight and nonminimal and "tight_nonminimal" not in examples:
                examples["tight_nonminimal"] = dict(cycle="".join("A" if x else "S" for x in cycle),
                    assigned=records, N=sorted(original), M=sorted(minimal))
            for donor, oldest in donors:
                counts["deletion_checks"] += 1
                assert len(original - {oldest}) >= len(records), (size, mask, records, donor, oldest)
                if tight:
                    counts["donor_checks"] += 1
                    assert oldest not in original, (size, mask, records, donor, oldest)
    return dict(period=size, counts=counts, examples=examples, cycle_sha256=digest.hexdigest())


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--periods", type=int, nargs="+", required=True)
    args = parser.parse_args()
    print(json.dumps(dict(kind="parameters", periods=args.periods, seed=None), sort_keys=True), flush=True)
    for period in args.periods:
        print(json.dumps(run_period(period), sort_keys=True), flush=True)
