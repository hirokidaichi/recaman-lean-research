from pathlib import Path
import json,subprocess,datetime
P=Path(__file__).resolve().parent
pids=[]
for p in P.glob('*-result.json'):
 x=json.loads(p.read_text())
 if 'pid' in x:pids.append(x['pid'])
result=[]
if pids:
 r=subprocess.run(['ps','-p',','.join(map(str,pids)),'-o','pid=,ppid=,pgid=,etime=,command='],capture_output=True,text=True)
 for line in r.stdout.splitlines():result.append(line.strip())
# A completed wrapper result is the evidence that its exact process/group was reaped.
# Existing unrelated processes are not killed, and reused PIDs are not assumed owned.
out={'at':datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9))).isoformat(),'worker_recorded_pids':pids,'still_existing_recorded_pid_rows':result,'live_owned_worker_rows':[x for x in result if str(P) in x],'validation_results':'all started validation wrappers have completed result except documented unsupported-AS preexec','unrelated_processes':'not modified; PID reuse is not treated as ownership'}
(P/'own-process-check.json').write_text(json.dumps(out,indent=2)+'\n');assert not out['live_owned_worker_rows'];print(json.dumps(out))
