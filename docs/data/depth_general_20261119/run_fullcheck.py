from pathlib import Path
import os,sys,time,json,resource,subprocess,signal,datetime,hashlib
from zoneinfo import ZoneInfo
p=Path(__file__).resolve().parent;clock=lambda:datetime.datetime.now(ZoneInfo('Asia/Tokyo'));t=time.monotonic()
def cap():resource.setrlimit(resource.RLIMIT_CPU,(10,10))
meta={'argv':['./scripts/check.sh'],'started_jst':clock().isoformat(),'wall_cap_seconds':90,'cpu_cap_seconds_per_process':10,'scope':'full validation, not cumulative tree cap; no failed Lean bytes under Recaman','head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'registry_sha256':hashlib.sha256(Path('docs/EVIDENCE_REGISTRY.tsv').read_bytes()).hexdigest()}
manifest={str(f):hashlib.sha256(f.read_bytes()).hexdigest()for f in sorted(Path('Recaman').glob('*.lean'))};manifest['Recaman.lean']=hashlib.sha256(Path('Recaman.lean').read_bytes()).hexdigest();(p/'FULLCHECK-source-tree.json').write_text(json.dumps(manifest,indent=2)+'\n');meta['source_tree_sha256']=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
(p/'FULLCHECK-start.json').write_text(json.dumps(meta,indent=2)+'\n')
with (p/'FULLCHECK.log').open('w')as log:
 c=subprocess.Popen(meta['argv'],stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=cap);reason='completed'
 while True:
  pid,status,u=os.wait4(c.pid,os.WNOHANG)
  if pid:break
  if time.monotonic()-t>90 or clock().hour>=8:
   reason='wall/deadline';os.killpg(c.pid,9);_,status,u=os.wait4(c.pid,0);break
  time.sleep(.1)
 c.returncode=os.waitstatus_to_exitcode(status)
out=dict(meta,finished_jst=clock().isoformat(),reason=reason,exit_code=c.returncode,wall_seconds=time.monotonic()-t,wait4_cpu_seconds=u.ru_utime+u.ru_stime,complete_tree_measurement=reason=='completed')
(p/'FULLCHECK-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));print((p/'FULLCHECK.log').read_text()[-2500:]);raise SystemExit(0 if c.returncode==0 else 1)
