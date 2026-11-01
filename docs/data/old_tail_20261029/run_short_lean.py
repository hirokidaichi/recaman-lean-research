"""Validation only: per-process CPU cap, group wall/deadline, exact completed wait4 CPU."""
import subprocess,resource,os,time,json,sys,datetime,hashlib
from pathlib import Path
from zoneinfo import ZoneInfo
p=Path(__file__).parent;tag=sys.argv[1];cmd=sys.argv[2:];t=time.monotonic()
meta={'tag':tag,'argv':cmd,'started_jst':datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'wall_cap_seconds':20,'cpu_limit_per_process_seconds':10,'source_sha256':{x:hashlib.sha256(Path(x).read_bytes()).hexdigest() for x in cmd if Path(x).is_file()},'scope':'Lean validation only; per-process CPU cap is not a cumulative process-tree cap; final wait4 includes reaped descendants'}
(p/(tag+'-start.json')).write_text(json.dumps(meta,indent=2)+'\n')
frozen=p/'frozen';frozen.mkdir(exist_ok=True)
for x in cmd:
 if Path(x).is_file():
  data=Path(x).read_bytes();(frozen/(hashlib.sha256(data).hexdigest()+'-'+Path(x).name)).write_bytes(data)
meta['revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
meta['dirty_source_hash']=hashlib.sha256(subprocess.check_output(['git','diff','--binary'])).hexdigest()
def cap():resource.setrlimit(resource.RLIMIT_CPU,(10,10))
with (p/(tag+'.log')).open('w') as log:
 c=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=cap)
 reason='completed'
 while True:
  pid,status,u=os.wait4(c.pid,os.WNOHANG)
  if pid:break
  if time.monotonic()-t>20 or datetime.datetime.now(ZoneInfo('Asia/Tokyo')).hour>=8:
   reason='wall/deadline cap';os.killpg(c.pid,9);_,status,u=os.wait4(c.pid,0);break
  time.sleep(.05)
 c.returncode=os.waitstatus_to_exitcode(status)
out=dict(meta,exit_code=c.returncode,reason=reason,wall_seconds=time.monotonic()-t,cpu_seconds=u.ru_utime+u.ru_stime,finished_jst=datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat())
(p/(tag+'-result.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out));print((p/(tag+'.log')).read_text())
raise SystemExit(0 if c.returncode==0 else 1)
