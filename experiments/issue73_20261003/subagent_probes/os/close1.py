"""Single owned window, state (G,Psi) at a clock (before reading); the rest of the walk is a good-block macro walk
(free A / AAS block / w1-triple block). Which (G,Psi) can close? (lag-uniform: boundary G>=4 => never)."""
from macro import run
for G in range(-5, 4):
    ps = []
    for Psi in range(-60, 61):
        res = []
        run(G, Psi, [], res)
        if res: ps.append(Psi)
    print('G=%2d closable Psi:' % G, ps)
