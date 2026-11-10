"""All bounded-strip prefixes up to 18. Supplier test uses prior affine area keys."""
from collections import Counter
import json
import time

ROOTS = ("", "A", "AA", "SAAA")
LIMIT = 18
start = time.process_time()
rows = Counter()
best = {}
shortest = {}


def endable_literal(word):
    mass = area = 0
    for length, sign in enumerate(reversed(word), 1):
        step = 1 if sign == "A" else -1
        mass += step
        area += length * step
        if mass == 1 and area == 0:
            return True
    return False


def search(root, depth):
    height = total = 0
    origins = Counter()
    for t, sign in enumerate(root):
        origins[(height, total - t * height)] += 1
        height += 1 if sign == "A" else -1
        total += height
    low, high = height - depth, height - depth + 4
    word = []

    def visit(h, area, adds, ends, subs, positive):
        length = len(word)
        rows[length] += 1
        if (rows.total() & 16383) == 0 and time.process_time() - start > 3.3:
            raise TimeoutError("cooperative 3.3 CPU second stop")
        free = adds - ends
        excess = adds - 2 * free
        labels = ("all", "positive") if positive else ("all",)
        for label in labels:
            if label not in best or excess > best[label]["excess"]:
                best[label] = dict(excess=excess, root=root, depth=depth, tail="".join(word),
                                   A=adds, supplied=ends, free=free)
            if excess > 0 and (label not in shortest or length < len(shortest[label]["tail"])):
                shortest[label] = dict(best[label]) if best[label]["tail"] == "".join(word) else dict(
                    excess=excess, root=root, depth=depth, tail="".join(word),
                    A=adds, supplied=ends, free=free)
        if positive and adds >= 2 * (free + 1):
            for gap in range(free, adds // 2):
                if endable_literal(root + "".join(word) + "S" * gap):
                    key = "positive_gap"
                    if key not in shortest or length < len(shortest[key]["tail"]):
                        shortest[key] = dict(root=root, depth=depth, tail="".join(word),
                                             j=gap, A=adds, supplied=ends, free=free)
        if length == LIMIT:
            return
        clock = len(root) + length
        supplied = origins[(h - 1, area - clock * (h - 1))] > 0
        origin = (h, area - clock * h)
        origins[origin] += 1
        if h < high:
            word.append("A")
            visit(h + 1, area + h + 1, adds + 1, ends + supplied, subs,
                  positive and subs >= ends + supplied + 1)
            word.pop()
        if h > low:
            word.append("S")
            visit(h - 1, area + h - 1, adds, ends, subs + 1,
                  positive and subs + 1 >= ends + 1)
            word.pop()
        origins[origin] -= 1

    visit(height, total, 0, 0, 0, True)


for old in ROOTS:
    for d in range(5):
        search(old, d)

print(json.dumps(dict(method="complete finite discovery with affine keys", length_max=LIMIT,
                      roots=ROOTS, depths=list(range(5)), visits=rows.total(), by_length=dict(rows),
                      strongest=best, shortest=shortest, process_algorithm_cpu=time.process_time() - start),
                 sort_keys=True))
