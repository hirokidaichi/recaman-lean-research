"""Strictly one cooperative Python worker; exact wait4 usage, not a generic tree monitor."""
from pathlib import Path
import argparse, datetime, hashlib, json, math, os, resource, runpy, signal, subprocess, sys, time
from zoneinfo import ZoneInfo

def worker(argv):
    cpu, script, *script_args = argv
    cap=int(cpu)
    resource.setrlimit(resource.RLIMIT_CPU,(cap,cap))
    def audit(event,args):
        if event in {'os.fork','os.forkpty','os.posix_spawn','os.exec','os.system','subprocess.Popen','ctypes.dlopen'}:
            raise PermissionError('single-worker contract rejects '+event)
    sys.addaudithook(audit)
    sys.argv=[script]+script_args
    runpy.run_path(script,run_name='__main__')

if len(sys.argv)>1 and sys.argv[1]=='--worker':
    worker(sys.argv[2:]);raise SystemExit(0)

ap=argparse.ArgumentParser()
ap.add_argument('--tag',required=True);ap.add_argument('--cpu',type=int,required=True)
ap.add_argument('--wall',type=float,required=True);ap.add_argument('script');ap.add_argument('args',nargs=argparse.REMAINDER)
a=ap.parse_args();assert a.cpu>0 and a.wall>0
base=Path(__file__).resolve().parent
clock=lambda:datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat()
script=Path(a.script).resolve();start=time.monotonic();self0=resource.getrusage(resource.RUSAGE_SELF);children0=resource.getrusage(resource.RUSAGE_CHILDREN)
meta={'started_jst':clock(),'tag':a.tag,'argv':[sys.executable,str(Path(__file__).resolve()),'--worker',str(a.cpu),str(script)]+a.args,'worker_cpu_cap_seconds':a.cpu,'wall_cap_seconds':a.wall,'contract':'one cooperative Python process, no descendants, all threads share CPU cap; not a security sandbox','worker_source_sha256':hashlib.sha256(script.read_bytes()).hexdigest(),'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(base/(a.tag+'-start.json')).write_text(json.dumps(meta,indent=2)+'\n')
reason='completed';usage=None;status=None
with (base/(a.tag+'.log')).open('w') as log:
    child=subprocess.Popen(meta['argv'],stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    meta['pid']=child.pid;meta['process_group']=child.pid
    (base/(a.tag+'-start.json')).write_text(json.dumps(meta,indent=2)+'\n')
    while True:
        pid,status,usage=os.wait4(child.pid,os.WNOHANG)
        if pid:break
        now=datetime.datetime.now(ZoneInfo('Asia/Tokyo'))
        if time.monotonic()-start>a.wall or now.hour>=8:
            reason='wall/deadline cap'
            os.killpg(child.pid,signal.SIGKILL)
            _,status,usage=os.wait4(child.pid,0);break
        time.sleep(.025)
    child.returncode=os.waitstatus_to_exitcode(status)
if child.returncode<0 and reason=='completed':reason='signal '+str(-child.returncode)+' (see CPU cap and output)'
self1=resource.getrusage(resource.RUSAGE_SELF);children1=resource.getrusage(resource.RUSAGE_CHILDREN)
out=dict(meta,finished_jst=clock(),exit_code=child.returncode,reason=reason,wall_seconds=time.monotonic()-start,
         worker_user_seconds=usage.ru_utime,worker_sys_seconds=usage.ru_stime,worker_cpu_seconds=usage.ru_utime+usage.ru_stime,
         worker_maxrss_native=usage.ru_maxrss,controller_cpu_seconds=self1.ru_utime+self1.ru_stime-self0.ru_utime-self0.ru_stime,
         descendants_allowed=False,cpu_measurement_complete_for_supported_contract=True)
(base/(a.tag+'-result.json')).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
raise SystemExit(0 if child.returncode==0 else 1)
