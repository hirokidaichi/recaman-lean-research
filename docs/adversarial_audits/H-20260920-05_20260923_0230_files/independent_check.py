#!/usr/bin/env python3
import hashlib
import itertools
import json


def stats(bits):
    signs = [1 if b else -1 for b in bits]
    mass = sum(signs)
    moment = sum((i + 1) * x for i, x in enumerate(signs))
    ss = sum((not bits[i]) and (not bits[i + 1]) for i in range(len(bits) - 1))
    witnesses = []
    for k in range(1, len(bits)):
        pre = bits[:k]
        ps = [1 if b else -1 for b in pre]
        if (not pre[-1]) and sum(ps) == 1 and sum((i + 1) * x for i, x in enumerate(ps)) == 0:
            witnesses.append(k)
    return mass, moment, ss, witnesses


def word(bits):
    return "".join("A" if b else "S" for b in bits)


def compositions(total, parts, positive):
    for cuts in itertools.combinations(range(total + parts - 1), parts - 1):
        bars = (-1,) + cuts + (total + parts - 1,)
        vals = tuple(bars[i + 1] - bars[i] - 1 for i in range(parts))
        if all((v > 0 if positive[i] else v >= 0) for i, v in enumerate(vals)):
            yield vals


def exact_ss2_ending_a(n):
    s = n // 2
    runs = s - 2
    for sruns in compositions(s, runs, (True,) * runs):
        if sum(v - 1 for v in sruns) != 2:
            continue
        for agaps in compositions(s, runs + 1, (False,) + (True,) * runs):
            bits = [True] * agaps[0]
            for i, r in enumerate(sruns):
                bits.extend([False] * r)
                bits.extend([True] * agaps[i + 1])
            yield tuple(bits)


def main():
    discovery = []
    all_valid = []
    missing_assumption = {k: None for k in ("ending_A", "mass_zero", "moment_bound", "ss_bound")}
    for n in range(1, 19):
        checked = failures = 0
        for bits in itertools.product((False, True), repeat=n):
            mass, moment, ss, ws = stats(bits)
            premises = {
                "ending_A": bits[-1],
                "mass_zero": mass == 0,
                "moment_bound": moment + n <= 0,
                "ss_bound": ss <= 2,
            }
            if all(premises.values()):
                checked += 1
                if not ws:
                    failures += 1
                else:
                    all_valid.append((bits, mass, moment, ss, ws))
            for dropped in missing_assumption:
                if missing_assumption[dropped] is None and all(v for k, v in premises.items() if k != dropped) and not premises[dropped] and not ws:
                    missing_assumption[dropped] = dict(word=word(bits), mass=mass, moment=moment, moment_plus_len=moment+n, ss=ss, witnesses=ws)
        discovery.append(dict(length=n, checked=checked, failures=failures))

    holdout = []
    for n in (20, 24):
        generated = list(exact_ss2_ending_a(n))
        assert len(generated) == len(set(generated))
        checked = failures = 0
        for bits in generated:
            mass, moment, ss, ws = stats(bits)
            assert bits[-1] and mass == 0 and ss == 2
            if moment + n <= 0:
                checked += 1
                failures += not bool(ws)
        holdout.append(dict(length=n, generated=len(generated), checked=checked, failures=failures))

    eq = [x for x in all_valid if x[2] + len(x[0]) == 0]
    strict = [x for x in all_valid if x[2] + len(x[0]) < 0]
    examples = {}
    for name, seq in (("equality", eq), ("strict_negative", strict)):
        if seq:
            bits, mass, moment, ss, ws = seq[0]
            examples[name] = dict(word=word(bits), mass=mass, moment=moment,
                                  moment_plus_len=moment+len(bits), ss=ss,
                                  witness_prefix_lengths=ws,
                                  suffix_nonempty_lengths=[len(bits)-k for k in ws])

    e130 = tuple(c == "A" for c in "AAASSSASASA")
    mass, moment, ss, ws = stats(e130)
    result = dict(
        statement="ending A AND mass=0 AND moment+length<=0 AND ss<=2 implies strict S-ended P2 prefix",
        discovery=discovery,
        discovery_total=sum(x["checked"] for x in discovery),
        discovery_failures=sum(x["failures"] for x in discovery),
        holdout=holdout,
        holdout_total=sum(x["checked"] for x in holdout),
        holdout_failures=sum(x["failures"] for x in holdout),
        nonvacuous_examples=examples,
        negative_controls=missing_assumption,
        e130_canonical_step115=dict(word=word(e130), mass=mass, moment=moment,
                                    moment_plus_len=moment+len(e130), ss=ss,
                                    strict_p2_prefix_lengths=ws),
        seed=None,
        cutoff={"all_binary_max_length":18, "exact_ss2_lengths":[20,24]},
    )
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
