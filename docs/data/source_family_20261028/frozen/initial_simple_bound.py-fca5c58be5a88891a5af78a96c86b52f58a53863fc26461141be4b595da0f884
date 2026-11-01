from pathlib import Path
import json,time
start=time.process_time();base=Path(__file__).parent
out=[];bad=[];allcount=0
for name in ['initial-S-local-discovery.json','initial-S-local-holdout.json']:
 d=json.loads((base/name).read_text())
 for r in d['all_rows']:
  if r['h']!=39:continue
  M,L,T,R=[r[x] for x in ['M','L','T','R']]
  lo=M-min(2,max(0,M-2))+max(0,L-1-len(r['local_clocks'][1]))+max(0,T-1-len(r['local_clocks'][2]))
  rr=dict(r,simple_lower=lo,critical=(R,M+L+T) in [(5,12),(5,14),(6,14),(7,16)])
  allcount+=1
  if rr['critical']:out.append(rr)
  if lo<R:bad.append(rr)
res={'label':'OBSERVED','reason':'posthoc simple-bound diagnostic on frozen prior outputs, not fresh holdout','skeletons':allcount,'critical_count':len(out),'violations':len(bad),'bad':bad,'critical_rows':out,'cpu_seconds':time.process_time()-start}
(base/'initial-simple-bound.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items() if k not in ['critical_rows','bad']}));print('bad samples',json.dumps(bad[:4]))
