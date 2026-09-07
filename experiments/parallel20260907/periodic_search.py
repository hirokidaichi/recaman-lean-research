#!/usr/bin/env python3
"""Frozen second-pass falsifier; exact closed-form periodic lag signatures."""
import hashlib
import json
from pathlib import Path
import random
import subprocess


def suppliers(word):
    p, s = len(word), sum(word)
    result = {}
    for t, step in enumerate(word):
        if step < 0:
            continue
        back = [word[(t-i) % p] for i in range(1, p+1)]
        weight = sum(i*e for i, e in enumerate(back, 1))
        prefix = moment = 0
        hits = []
        for r in range(p):
            quotient, rem = divmod(1-prefix, s)
            d = quotient*p+r
            if rem == 0 and quotient >= 0 and d > 0:
                value = (quotient*weight + p*s*quotient*(quotient-1)//2
                         + quotient*p*prefix + moment)
                if value == 0:
                    hits.append(d)
            prefix += back[r]
            moment += (r+1)*back[r]
        result[t] = sorted(hits)
    return result


def naive(word):
    result = {}
    for t, step in enumerate(word):
        if step < 0:
            continue
        total = moment = 0
        hits = []
        for d in range(1, len(word)*(len(word)+1)+1):
            e = word[(t-d) % len(word)]
            total += e
            moment += d*e
            if total == 1 and moment == 0:
                hits.append(d)
        result[t] = hits
    return result


def main():
    rng = random.Random(20260907)
    print('protocol=periodic_search_protocol.md seed=20260907', flush=True)
    print('source_revision='+subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
    print('script_sha256='+hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    trials = 0
    def sample(p):
        word = [-1]*((p-1)//2)+[1]*(p-(p-1)//2)
        rng.shuffle(word)
        return word
    for p in range(1,13):
        for _ in range(10):
            word = sample(p)
            assert suppliers(word) == naive(word)
    print('closed_formula_vs_direct=120_words_PASS', flush=True)

    def score(word):
        nonlocal trials
        sig = suppliers(word)
        trials += 1
        missing = sum(not hits for hits in sig.values())
        if missing == 0:
            assert sig == naive(word)
            print('COUNTEREXAMPLE='+json.dumps({'word':word,'suppliers':sig,'trials':trials}), flush=True)
            raise SystemExit(0)
        return missing

    for p in range(19,65):
        best = p
        for _ in range(1000):
            best = min(best,score(sample(p)))
        for _ in range(100):
            word = [rng.choice([-1,1]) for _ in range(p)]
            while sum(word) <= 0:
                word = [rng.choice([-1,1]) for _ in range(p)]
            best = min(best,score(word))
        print(f'shuffled period={p} trials=1100 min_unsupported={best}', flush=True)
    for p in [24,32,48,64]:
        best = p
        for i in range(10000):
            if i % 1000 == 0:
                word = sample(p)
                current = score(word)
            plus = rng.choice([j for j,e in enumerate(word) if e > 0])
            minus = rng.choice([j for j,e in enumerate(word) if e < 0])
            trial = word.copy()
            trial[plus],trial[minus] = trial[minus],trial[plus]
            value = score(trial)
            if value <= current:
                word,current = trial,value
            best = min(best,value)
        print(f'swap period={p} proposals=10000 min_unsupported={best}', flush=True)
    print(f'COMPLETE tested_words_with_repetitions={trials} all_additions_supplied=0', flush=True)


if __name__ == '__main__':
    main()
