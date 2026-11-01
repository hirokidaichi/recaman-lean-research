"""Boundary/rounding audit of the recorded all-mass paper argument; not its proof."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).parent
table = json.loads((root / 'spectrum-relax.spectrum.json').read_text())
for row in table:
    m = row['mass']
    expected = {0} if m == 0 else {1} if m == 1 else set(range(m*(m+1)//2-1, (5*m*m-11*m+16)//4+1))
    assert set(map(int, row['area_witnesses'])) == expected, m
    for value, word in row['area_witnesses'].items():
        height = area = 0
        for c in word:
            height += 1 if c == 'A' else -1
            area += height
        assert height == m and area == int(value), (m, word)

# Coefficients are in ascending order. These exact expansions do not sample m.
def add(a, b):
    return tuple(x+y for x, y in zip(a, b))

def scale(a, n):
    return tuple(n*x for x in a)

P = (16, -11, 5)
Pprev = (32, -21, 5)
Ptwo = (58, -31, 5)
Pfour = (140, -51, 5)
assert add(Pfour, (-124, 40, 0)) == P
four_LB = (-24, 10, 2)
four_LC = (-104, 26, 2)
four_UA_lower = add(Pprev, (-3, 4, 0))
four_UB_lower = add(Ptwo, (-27, 16, 0))
gap_A = add(add(four_UA_lower, (4, 0, 0)), scale(four_LB, -1))
gap_B = add(add(four_UB_lower, (4, 0, 0)), scale(four_LC, -1))
assert gap_A == (57, -27, 3)
assert gap_B == (139, -41, 3)
assert sum(v*8**i for i, v in enumerate(gap_A)) == 33
assert sum(v*8**i for i, v in enumerate(gap_B)) == 3
# q(m+1)-q(m) for coefficients (a,b,c) is (b+c)+2c*m.
assert (gap_A[1]+gap_A[2], 2*gap_A[2]) == (-24, 6)
assert (gap_B[1]+gap_B[2], 2*gap_B[2]) == (-38, 6)

out = dict(status='passed', finite_table_masses=[0, 17], all_area_sets_and_witnesses=True,
           gap_polynomial_coefficients=[gap_A, gap_B], gap_values_at_eight=[33, 3],
           gap_forward_differences=[[-24, 6], [-38, 6]],
           universal_argument='recorded paper induction; this finite audit is not its replacement',
           source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           table_sha256=hashlib.sha256((root / 'spectrum-relax.spectrum.json').read_bytes()).hexdigest())
(root / 'spectrum-formula-audit.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out))
