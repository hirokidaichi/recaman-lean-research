"""Own-process-group validation watcher. Never touches unrelated sessions."""
import argparse,datetime,json,os,signal,subprocess,time
from pathlib import Path
from zoneinfo import ZoneInfo
ap=argparse.ArgumentParser();ap.add_argument('--tag',default='natblocks');args=ap.parse_args()
base=Path(__file__).parent
tag=args.tag
start=time.monotonic();peak=0;reason='completed'
log=(base/f'kernel-four-{tag}.log').open('w')
cmd=['/usr/bin/time','-lp','-o',str(base/f'kernel-four-{tag}.time'),'lake','build','Recaman.FourNonsuppliedData']
p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
meta=dict(started_jst=datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),pid=p.pid,argv=cmd,rss_cap_kib=4*1024*1024,deadline_jst='06:40:00')
(base/f'validation-{tag}-process.json').write_text(json.dumps(meta,indent=2)+'\n')
while p.poll() is None:
 time.sleep(1)
 records=[]
 for line in subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,comm='],text=True).splitlines():
  f=line.split(None,3)
  if len(f)==4:records.append((int(f[0]),int(f[1]),int(f[2]),f[3]))
 descendants={p.pid}
 for _ in range(5):
  descendants|={pid for pid,parent,rss,comm in records if parent in descendants}
 rss=max([rss for pid,parent,rss,comm in records if pid in descendants]+[0]);peak=max(peak,rss)
 now=datetime.datetime.now(ZoneInfo('Asia/Tokyo'))
 if rss>meta['rss_cap_kib'] or (now.hour,now.minute)>=(6,40):
  reason='RSS cap' if rss>meta['rss_cap_kib'] else 'deadline'
  os.killpg(p.pid,signal.SIGTERM);break
try:p.wait(timeout=5)
except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
log.close()
result=dict(**meta,finished_jst=datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),exit_code=p.returncode,reason=reason,peak_sampled_rss_kib=peak,wall_seconds=time.monotonic()-start)
(base/f'validation-{tag}-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
raise SystemExit(0 if p.returncode==0 else 1)
