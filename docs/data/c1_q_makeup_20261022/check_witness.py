"""Independent direct-sum witness audit (no mod-4 start pruning)."""
import argparse
import json


def audit(word, q0, b=None):
    signs = [1 if c == 'A' else -1 for c in word]
    assert set(word) <= {'A', 'S'}
    f = [0]
    for v in signs:
        f.append(f[-1] + v)
    starts, ends, d, a = [], [], [0], [0]
    for j, v in enumerate(signs):
        ts = [t for t in range(j)
              if sum(signs[t:j]) == 1
              and sum(signs[i] * (j-i) for i in range(t, j)) == 0]
        starts.append(ts)
        e = v == 1 and bool(ts)
        ends.append(e)
        d.append(d[-1] + (v == -1) - e)
        a.append(a[-1] + (v == 1 and not e))
    assert 0 < q0 <= len(word) and d[q0] == 1
    assert min(d[:q0+1]) >= 0
    k1 = max(u for u in range(q0) if d[u] == 0)
    g = f[k1]
    az = sum(f[u]-g+1 for u in range(k1+1, q0+1))
    out = dict(word=word, q0=q0, k1=k1, g=g, F=f, d=d, a=a,
               starts=starts, endable=ends, Az=az, a_z=a[q0]-a[k1])
    if b is not None:
        assert q0 <= b < len(word)
        y = sum(f[u]-f[b]+1 for u in range(q0+1, b+1))
        z = sum(f[u]-f[b]+1 for u in range(k1+1, b+1))
        cross = (q0-k1)*(g-f[b])
        assert z == az+cross+y
        out.update(b=b, F_b=f[b], guard=f[b] <= g, Y=y, Z=z,
                   correction=cross, ay_through_b=a[b+1]-a[q0],
                   strict=min(d[q0:b+2]) >= 1,
                   full_completion_checked=False)
    return out


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('word')
    p.add_argument('q0', type=int)
    p.add_argument('--b', type=int)
    args = p.parse_args()
    print(json.dumps(audit(args.word, args.q0, args.b), indent=2))
