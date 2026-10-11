#!/usr/bin/env python3
"""Read-only independent fixed-model audit. No new model or census range."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path('/Users/hirokidaichi/.codex/worktrees/p2-terminal-tail-bound/recaman-lean-research')
OUT = Path('/tmp/ss2-pair-next-audit-20261006')
DATA = ROOT / 'docs/data/ss2_internal_sss_20261006'
logs = []
hashes = {}
for line in (DATA / 'source-frozen.sha256').read_text().splitlines():
    expected, name = line.split()
    actual = hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
    assert actual == expected, name
    hashes[name] = actual

results = []
for split in ['discovery', 'holdout']:
    command = [sys.executable, 'experiments/ss2_internal_sss_controls.py', split]
    replay = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, check=True)
    logs.append({'command': command, 'exit_code': replay.returncode, 'stderr': replay.stderr})
    (OUT / ('internal_sss_replay_' + split + '.json')).write_text(replay.stdout)
    observed = json.loads(replay.stdout)
    frozen = json.loads((DATA / (split + '.json')).read_text())
    assert observed == frozen
    for model in frozen['models']:
        P = model['period']
        p = len(P)
        value = lambda t: 1 if P[t % p] == 'A' else -1
        assert p == model['p'] and sum(value(t) for t in range(p)) == model['mass'] > 0
        assert all(''.join(P[(t+j) % p] for j in range(4)) != 'SAAS' for t in range(p)) == model['NoSAAS']
        endpoints = []
        for t in range(p):
            if value(t) != 1:
                continue
            m = Q = edges = 0
            prev = 1
            for lag in range(1, p * (p + 1) + 1):
                v = value(t - lag)
                m += v
                Q += lag * v
                edges += prev == v == -1
                prev = v
                if m == 1 and Q == 0 and edges <= 1 and v == -1:
                    endpoints.append((t, lag, (t-lag) % p))
        expected = sorted((row['phase'], row['lag'], (row['phase'] - row['lag']) % p)
                          for row in model['all_lowSS_Sended_witnesses'])
        assert sorted(endpoints) == expected
        E = {z[2] for z in endpoints}
        assert sorted(E) == model['lowSS_endpoint_phases']
        N = set()
        for donor in model['donors']:
            t, d = donor['phase'], donor['lag']
            assert value(t) == 1
            word = ''.join(P[(t-i) % p] for i in range(1,d+1))
            assert word == donor['word']
            m = Q = 0
            hits = []
            for i, letter in enumerate(word,1):
                v = 1 if letter == 'A' else -1
                m += v
                Q += i*v
                if m == 1 and Q == 0:
                    hits.append(i)
            assert hits == [d]
            assert sum(word[i:i+2] == 'SS' for i in range(d-1)) == 2
            N |= {(t-i) % p for i,x in enumerate(word,1) if x == 'S'}
        assert sorted(N-E) == model['uncovered_phases']
        s,q = model['s'],model['q']
        assert all(value(q+i) == -1 for i in range(3))
        assert value(s) == -1 and s % p not in E and q % p not in E
        if q > s:
            assert s % p != q % p and len(N-E) >= 2
        name = model['name']
        residual = name.startswith('remaining_family_r')
        if residual:
            r = int(name.removeprefix('remaining_family_r'))
            b,a,j = 3*r+1,9*r+5,8*r+6
            C = 'AS'*a + 'AAA' + 'SA'*b + 'SSS'
            X = 'SA'*j + 'A'
            assert a == 3*b+2 and 3*j+1 == 8*b+11
            assert C == model['C'] and X == model['X']
            assert p == 40*r+32
            assert sorted(z['lag'] for z in model['donors']) == [24*r+19,40*r+31]
            assert s == q == 0 and 1 not in E
            tA,tS = len(C),len(C)+len(X)
            assert ''.join(P[t % p] for t in range(1,tA)) == 'SS'+'AS'*b+'AAA'+'SA'*a
            assert ''.join(P[t % p] for t in range(tA,tS)) == 'A'+'AS'*j
            # Every current-A mass-one candidate up to tS; inspect exact moment.
            m = 0
            candidates = []
            for t in range(2,tS+1):
                m += value(t-1)
                if m == 1 and value(t) == 1:
                    Q = sum((t-i)*value(i) for i in range(1,t))
                    candidates.append((t,Q))
                if t > tA:
                    assert m in (2,3)
            assert candidates == [(tA,-1)]
        results.append({'split':split,'name':name,'p':p,'mass':model['mass'],
                        'NoSAAS':model['NoSAAS'],'s':s,'q':q,
                        'all_endpoint_witnesses':len(endpoints),'endpoint_phases':sorted(E),
                        'uncovered_count':len(N-E),'residual_phase_one_excluded':residual})

report = {'status':'PASS','models':len(results),'frozen_source_hashes':hashes,
          'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'commands':logs,'results':results,
          'scope':'Fixed six models only; independent direct mass/moment and all-lag positive-mass bound; no new holdout for phase-one conjecture.'}
(OUT / 'internal_sss_verification.json').write_text(json.dumps(report,indent=2)+'\n')
(OUT / 'internal_sss_commands.log').write_text('\n'.join(' '.join(log['command'])+' => exit 0; exact frozen JSON match' for log in logs)+'\nindependent scanner => six models PASS\n')
print(json.dumps(report,indent=2))
