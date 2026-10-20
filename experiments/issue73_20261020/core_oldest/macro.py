"""Lag-uniform macro search (see report). State (G,Psi) at clock c BEFORE reading sigma(c),
G = F(c)-h_b0, Psi = sum_{tau in (x,c]} G(tau).  b0 may close at c iff G==1, Psi==0, sigma(c)=A, c not a member.
After b0's owned S, the walk is a sequence of: free A clocks, AAS blocks (S A A + member A),
w1-triple blocks (S S A A A A S A A + member A; internal members at offsets 4, 7).
G at macro boundaries strictly increases (+1, +2, +4); inside a block G >= start-2.
So once boundary G >= 4, G >= 2 forever and b0 can never close: the search is finite and lag-uniform."""
import sys
BLOCKS = {'AAS': ('SAA', set()), 'TRI': ('SSAAAASAA', {4, 7})}
def run(G, Psi, hist, res):
    if G >= 4:
        return
    if G == 1 and Psi == 0:
        res.append(hist + ['close@freeA'])
    run(G + 1, Psi + G + 1, hist + ['A'], res)
    for name, (letters, mem) in BLOCKS.items():
        g, p = G, Psi
        for i, ch in enumerate(letters):
            if ch == 'A' and i not in mem and g == 1 and p == 0:
                res.append(hist + [f'close@{name}[{i}]'])
            g += 1 if ch == 'A' else -1
            p += g
        g += 1; p += g   # trailing member clock (A), b0 cannot close there
        run(g, p, hist + [name], res)
def prefix_state(word):
    G = Psi = 0
    for ch in word:
        G += 1 if ch == 'A' else -1
        Psi += G
    return G, Psi
if __name__ == '__main__':
    for k in range(0, 12):
        res = []
        G, Psi = prefix_state('A' * k + 'S')
        run(G, Psi, ['A^%d S' % k], res)
        print('k =', k, 'closures:', res)
