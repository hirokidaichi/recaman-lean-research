"""Fresh disjoint lengths, independent reverse-sign supplier test."""
import json
import random
import time

lengths = (23, 27, 31, 35)
roots = ("", "A", "AA", "SAAA")
seed = 2026111101
rng = random.Random(seed)
start = time.process_time()
samples = 0
maxima = {}
counterexamples = {}


def win(prefix):
    mass = area = 0
    for distance, symbol in enumerate(prefix[::-1], 1):
        sign = 1 if symbol == "A" else -1
        mass += sign
        area += distance * sign
        if mass == 1 and area == 0:
            return True
    return False


for root in roots:
    for depth in range(5):
        for length in lengths:
            for _ in range(100):
                height = depth
                symbols = []
                for _ in range(length):
                    step = rng.choice((1, -1)) if 0 < height < 4 else (1 if height == 0 else -1)
                    symbols.append("A" if step == 1 else "S")
                    height += step
                word = root + "".join(symbols)
                A = supplied = S = 0
                positive = True
                for i, symbol in enumerate(symbols):
                    if symbol == "A":
                        A += 1
                        supplied += win(word[:len(root) + i])
                    else:
                        S += 1
                    positive &= S > supplied
                F = A - supplied
                E = A - 2 * F
                data = dict(root=root, depth=depth, tail="".join(symbols), excess=E,
                            A=A, supplied=supplied, free=F)
                for kind in (("all", "positive") if positive else ("all",)):
                    if kind not in maxima or E > maxima[kind]["excess"]:
                        maxima[kind] = data
                    if E > 0 and kind not in counterexamples:
                        counterexamples[kind] = data
                if positive and "positive_gap" not in counterexamples:
                    for gap in range(F, A // 2):
                        if win(word + "S" * gap):
                            counterexamples["positive_gap"] = dict(data, j=gap)
                            break
                samples += 1
                if (samples & 127) == 0 and time.process_time() - start > 3.3:
                    raise TimeoutError("cooperative 3.3 CPU second stop")
print(json.dumps(dict(method="independent reverse-sign literal holdout", seed=seed, lengths=lengths,
                      samples=samples, maxima=maxima, counterexamples=counterexamples,
                      process_algorithm_cpu=time.process_time() - start), sort_keys=True))
