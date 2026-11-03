"""Publish this owned validated snapshot; closed journal and unchanged baseline required."""
from pathlib import Path
import subprocess,json,os,datetime,signal,time
from zoneinfo import ZoneInfo
p=Path(__file__).parent
owned=json.loads((p/'OWNED_PATHS.json').read_text());journal=json.loads(Path('docs/data/daily_research/2026-11-04.json').read_text())
assert journal.get('cursor') is None, 'journal must be closed before final publication'
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='main'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==owned['baseline']
assert subprocess.check_output(['git','rev-list','--left-right','--count','HEAD...origin/main'],text=True).strip()=='0\t0'
deadline=datetime.datetime(2026,11,4,7,59,35,tzinfo=ZoneInfo('Asia/Tokyo'))
def run(argv,cap,env=None):
 remaining=(deadline-datetime.datetime.now(ZoneInfo('Asia/Tokyo'))).total_seconds()
 if remaining<=5:raise RuntimeError('publication deadline margin exhausted')
 c=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True,env=env)
 try:out,_=c.communicate(timeout=min(cap,remaining-3))
 except subprocess.TimeoutExpired:
  os.killpg(c.pid,signal.SIGKILL);out,_=c.communicate();Path('/private/tmp/recaman-20261104-publication-timeout.log').write_text(out);raise
 if c.returncode:
  print(out);raise subprocess.CalledProcessError(c.returncode,argv)
 return out
paths=owned['paths'];assert all(Path(x).is_file() for x in paths)
for k in range(0,len(paths),100):run(['git','add','--',*paths[k:k+100]],10)
run(['git','diff','--cached','--check'],10)
staged=set(run(['git','diff','--cached','--name-only'],10).splitlines());assert staged<=set(paths)
env=dict(os.environ);env['RECAMAN_ALLOW_BURST']='1'
out=run(['git','commit','-m','research: advance low-mass target source budgets (2026-11-04)','--',*paths],55,env)
Path('/private/tmp/recaman-20261104-commit.log').write_text(out)
sha=run(['git','rev-parse','HEAD'],5).strip();print('COMMIT',sha,flush=True)
print(run(['git','push','origin',sha+':refs/heads/main'],30),flush=True)
remote=run(['git','ls-remote','--heads','origin','refs/heads/main'],15).strip();match=remote.split()[0]==sha
result={'sha':sha,'branch':'main','remote':'origin/main','ls_remote':remote,'remote_matches':match,'status_porcelain':run(['git','status','--porcelain'],5),'commit_output_log':'/private/tmp/recaman-20261104-commit.log'}
Path('/private/tmp/recaman-20261104-publication.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True);assert match
