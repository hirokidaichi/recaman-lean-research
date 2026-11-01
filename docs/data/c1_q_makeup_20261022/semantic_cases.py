"""Direct finite audits of the hypotheses used in the fresh-low-visit proof."""
import json
from pathlib import Path


def walk(word):
    f = [0]
    for c in word:
        f.append(f[-1] + (1 if c == 'A' else -1))
    starts = []
    a = [0]
    for b, c in enumerate(word):
        ts = [t for t in range(b) if f[b] == f[t]+1
              and sum((b-i)*(1 if word[i] == 'A' else -1)
                      for i in range(t, b)) == 0]
        starts.append(ts)
        a.append(a[-1] + (c == 'A' and not ts))
    return f, starts, a


def case(word, n, q0, r, b):
    f, starts, a = walk(word)
    m = f[r]
    return dict(word=word, n=n, q0=q0, r=r, b=b, m=m, F_b=f[b],
                global_tail_min=min(f[n:b+1]), attained_lower_bound=min(f[n:b+1]) == m,
                new_visit_after_q0=q0 <= r,
                ay_before_b=a[b]-a[q0],
                area=sum(f[u]-f[b]+1 for u in range(n+1, b+1)),
                endable_b=word[b] == 'A' and bool(starts[b]), starts_b=starts[b])


if __name__ == '__main__':
    out = {
        'fresh_min_nontrivial': case('SAAASSSSAAAASAAA'+'S'*7+'A'+'S', 4, 16, 23, 24),
        'ay_two_counterexample': case('SSSAAAS', 0, 1, 3, 6),
        'old_min_excluded': case('SAAASSSSAAAASAAA'+'S'*3, 4, 16, 8, 18),
        'N_threshold_two_counterexample': case('SAAA', 0, 0, 1, 3),
        'N_without_prefix_counterexample': case('SAAA', 3, 3, 3, 3),
        'N_without_tail_lower_bound': case('SAAASSSSAAAA', 4, 4, 5, 11),
    }
    assert out['fresh_min_nontrivial']['attained_lower_bound']
    assert out['fresh_min_nontrivial']['ay_before_b'] == 1
    assert out['fresh_min_nontrivial']['F_b'] == out['fresh_min_nontrivial']['m']+1
    assert out['fresh_min_nontrivial']['area'] >= 0
    assert out['ay_two_counterexample']['ay_before_b'] == 2
    assert out['ay_two_counterexample']['area'] == -3
    assert not out['old_min_excluded']['new_visit_after_q0']
    assert out['N_threshold_two_counterexample']['endable_b']
    assert out['N_without_prefix_counterexample']['endable_b']
    assert out['N_without_tail_lower_bound']['endable_b']
    p = Path(__file__).parent/'semantic-cases.json'
    p.write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))
