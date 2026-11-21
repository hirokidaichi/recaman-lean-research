"""Bounded read-only hosted CI observation AFTER the verified research push."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,subprocess,signal,os
P=Path(__file__).resolve().parent;R=P/'publication_snapshot'
r=json.loads((R/'PUBLICATION_RECEIPT.json').read_text());sha=r['research_snapshot_sha']
clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
observations=[]
for kind,path in [('workflow_runs',f'repos/hirokidaichi/recaman-lean-research/actions/runs?head_sha={sha}&per_page=10'),('check_runs',f'repos/hirokidaichi/recaman-lean-research/commits/{sha}/check-runs')]:
 left=(clock().replace(hour=8,minute=0,second=0,microsecond=0)-clock()).total_seconds()
 if clock().hour!=7 or left<20:observations.append({'kind':kind,'state':'unconfirmed, deadline margin'});continue
 proc=subprocess.Popen(['gh','api',path],stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True,start_new_session=True)
 try:out,err=proc.communicate(timeout=min(8,left-12))
 except subprocess.TimeoutExpired:
  os.killpg(proc.pid,signal.SIGKILL);out,err=proc.communicate();observations.append({'kind':kind,'state':'unconfirmed, read timeout'});continue
 if proc.returncode:observations.append({'kind':kind,'state':'unconfirmed, API read failed','error':err[-600:]});continue
 d=json.loads(out);items=d.get('workflow_runs',d.get('check_runs',[]))
 observations.append({'kind':kind,'state':'observed','runs':[{k:x.get(k)for k in ['id','name','status','conclusion','html_url','head_sha']}for x in items]})
meta={'sha':sha,'at':clock().isoformat(),'observations':observations,'scope':'Read-only current observation, not a claim that CI completed or the final receipt commit was checked'}
(R/'CI_SNAPSHOT.json').write_text(json.dumps(meta,indent=2)+'\n')
r['hosted_ci']=observations;r['hosted_ci_checked_at']=meta['at']
(R/'PUBLICATION_RECEIPT.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(meta,indent=2))
