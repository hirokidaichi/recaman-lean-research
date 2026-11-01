"""Independent NFA language coverage and direct-sum audit of representatives."""
import argparse
import json
from pathlib import Path

from semantic_cases import walk


def expected_contexts():
    # Boundary state 0 is shared. All other states are interior positions of
    # exactly one atom. Every state is reachable from 0.
    outgoing = {0: []}
    next_state = 1
    for atom in ['A', 'SAAA', 'SSAAAASAAA']:
        state = 0
        for i, c in enumerate(atom):
            target = 0 if i == len(atom)-1 else next_state
            if target:
                outgoing[target] = []
                next_state += 1
            outgoing[state].append((c, target))
            state = target
    suffixes = set()
    for start in outgoing:
        layer = {(start, '')}
        for _ in range(11):
            layer = {(target, word+c) for state, word in layer
                     for c, target in outgoing[state]}
        suffixes.update(word for state, word in layer if state == 0)
    short = {''}
    layer = {(0, '')}
    for _ in range(10):
        layer = {(target, word+c) for state, word in layer
                 for c, target in outgoing[state]}
        short.update(word for state, word in layer if state == 0)
    return suffixes, short, len(outgoing)


def audit(path):
    rows = json.loads(path.read_text())
    suffixes, short, nfa_states = expected_contexts()
    actual_suffixes = {r['key'][7:] for r in rows if r['key'].startswith('suffix:')}
    actual_short = {r['key'][6:] for r in rows if r['key'].startswith('short:')}
    assert suffixes == actual_suffixes, (suffixes-actual_suffixes, actual_suffixes-suffixes)
    assert short == actual_short
    assert len(rows) == len(suffixes)+len(short)
    for r in rows:
        w = r['prefix']
        f, starts, _ = walk(w)
        d = [0]
        for i, c in enumerate(w):
            d.append(d[-1]+(c == 'S')-(c == 'A' and bool(starts[i])))
        assert d[-1] == 0 and min(d) >= 0, (w, d)
        if r['key'].startswith('suffix:'):
            assert w == r['key'][7:] and len(w) == 11
        else:
            assert w == r['key'][6:] and len(w) < 11
    return dict(status='passed', nfa_states=nfa_states, suffix_contexts=len(suffixes),
                short_contexts=len(short), total_representatives=len(rows),
                independent_P2_start_scan=True, full_prefix_d0_and_nonnegative=True,
                coverage_argument='NFA all reachable states to boundary for length 11; shorter boundary-to-boundary words')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('representatives', type=Path)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    result = audit(args.representatives)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))
