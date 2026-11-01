import json,collections
from pathlib import Path
p=Path(__file__).parent
rows=sum([json.loads((p/(x+'-model.json')).read_text())['all_rows'] for x in ['discovery','holdout']],[])
stats={'max_local3':max(len(x['third']) for x in rows),'max_local2':max(len(x['second']) for x in rows),'T_lt_j':sum(x['T']<x['j'] for x in rows),'max_band_count':max(sum(i+x['j']>=x['T'] for i,_ in x['third']) for x in rows)}
for key,pred in [('three_local',lambda x:len(x['third'])==3),('lowT_small_total_free',lambda x:x['T']<x['j'] and x['free_lower']<=x['j']+1),('closest',lambda x:x['free_lower']==x['j']+1)]:
 xs=[x for x in rows if pred(x)]
 print(key,len(xs),json.dumps(xs[:12]))
print('STATS',json.dumps(stats))
