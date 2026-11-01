"""Read-only profiling of existing validation stages; no theorem or gate edits."""
import json,os,resource,signal,subprocess,time,datetime,hashlib
from pathlib import Path
p=Path(__file__).parent
steps=[('architecture',['bash','scripts/check_module_architecture.sh'],{0}),('registry',['bash','scripts/check_research_registry.sh'],{0}),('lake_build_cached',['lake','build'],{0}),('axiom_audit',['lake','env','lean','Recaman/Audit.lean'],{0}),('forbidden_scan',['rg','-n','--glob','*.lean',r'\b(sorry|admit|native_decide|axiom)\b','.'],{1})]
rows=[]
def cap():resource.setrlimit(resource.RLIMIT_CPU,(20,20))
for name,argv,ok in steps:
 t=time.monotonic()
 with (p/(name+'.log')).open('w') as out:
  c=subprocess.Popen(argv,stdout=out,stderr=subprocess.STDOUT,start_new_session=True,preexec_fn=cap)
  reason='completed'
  while True:
   pid,status,u=os.wait4(c.pid,os.WNOHANG)
   if pid:break
   if time.monotonic()-t>25:
    os.killpg(c.pid,signal.SIGKILL);_,status,u=os.wait4(c.pid,0);reason='wall_timeout';break
   time.sleep(.01)
  c.returncode=os.waitstatus_to_exitcode(status)
 row={'name':name,'argv':argv,'wall_seconds':time.monotonic()-t,'cpu_seconds':u.ru_utime+u.ru_stime,'maxrss_native':u.ru_maxrss,'exit_code':c.returncode,'expected_exit':sorted(ok),'reason':reason};rows.append(row)
 print(json.dumps(row),flush=True)
 if c.returncode not in ok:break
obj={'date':'2026-10-28','kind':'validation performance audit, separate from closed daily research journal','revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'dirty_tracked_hash':hashlib.sha256(subprocess.check_output(['git','diff','--binary'])).hexdigest(),'source_sha256':{f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in ['scripts/check.sh','scripts/check_module_architecture.sh','scripts/check_research_registry.sh','scripts/harness_gate.py','Recaman/Audit.lean']},'resource_scope':'per-process20CPU/group25wall; not generic tree cumulative cap','stages':rows,'stage_wall_sum':sum(x['wall_seconds'] for x in rows)}
(p/'stages.json').write_text(json.dumps(obj,indent=2)+'\n')
