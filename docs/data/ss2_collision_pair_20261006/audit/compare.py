#!/usr/bin/env python3
# Usage: python3 compare.py REPOSITORY_ROOT INDEPENDENT_OUTPUT
import json, sys
from pathlib import Path
root=Path(sys.argv[1]); result=Path(sys.argv[2])
base=root/'docs/data/ss2_collision_pair_20261006'
rows=[json.loads(x) for f in ['discovery.jsonl','holdout.jsonl'] for x in (base/f).read_text().splitlines()]
rows={r['p']:r for r in rows if r['kind']=='summary'}
keys=['p','positive_mass_necklaces','positive_mass_words','lowSS_phases','minimal_SS2_phases','SS2_lag_ge_period','max_oldest_group','collision_pairs','all_low_subsets','min_slack']
audit=[dict(zip(keys,map(int,line.split()))) for line in result.read_text().splitlines()]
assert [r['p'] for r in audit]==list(range(1,23))
assert set(rows)==set(range(1,23))
for r in audit:
 for k in keys: assert r[k]==rows[r['p']][k],(r['p'],k,r[k],rows[r['p']][k])
print(json.dumps({'status':'PASS','periods':22,'fields_per_period':10,'pairs':sum(r['collision_pairs'] for r in audit),'subsets':sum(r['all_low_subsets'] for r in audit),'min_slack':min(r['min_slack'] for r in audit if r['collision_pairs'])},sort_keys=True))
