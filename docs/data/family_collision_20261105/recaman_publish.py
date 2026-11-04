from pathlib import Path
import os,subprocess,json,datetime,signal,time
from zoneinfo import ZoneInfo
P=Path('docs/data/family_collision_20261105');J=Path('docs/data/daily_research/2026-11-05.json');Z=ZoneInfo('Asia/Tokyo')
def now():return datetime.datetime.now(Z)
def run(argv,cap=20,env=None):
 remaining=(now().replace(hour=7,minute=59,second=39,microsecond=0)-now()).total_seconds()
 if remaining<2:raise RuntimeError('publication deadline reached; preserve uncommitted paths')
 p=subprocess.Popen(argv,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True,env=env)
 try:out,_=p.communicate(timeout=min(cap,remaining))
 except subprocess.TimeoutExpired:
  os.killpg(p.pid,signal.SIGTERM)
  try:out,_=p.communicate(timeout=1)
  except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);out,_=p.communicate()
  raise RuntimeError('publication command timed out: '+repr(argv)+'\n'+out[-2000:])
 if p.returncode:raise RuntimeError(repr(argv)+'\n'+out[-5000:])
 return out
j=json.loads(J.read_text());assert j['cursor'] is None,'journal must be stopped before publication'
assert j['events'][-1]['action']=='stop'
assert now().date().isoformat()=='2026-11-05' and now().hour==7 and now().minute>=45
assert run(['git','branch','--show-current']).strip()=='main'
assert run(['git','rev-parse','HEAD']).strip()=='f06d97ea35ffa528a383f1edd37ecd27f2d6bf35'
run(['python3','/private/tmp/recaman_finish_docs.py'])
run(['python3','/private/tmp/recaman_daily_report.py'])
run(['python3','viewer/gen_manifest.py'])
paths=json.loads((P/'PUBLICATION_PATHS.json').read_text())['owned_paths']
changed=set(run(['git','ls-files','-m','-o','--exclude-standard']).splitlines())
assert changed.issubset(set(paths)),sorted(changed-set(paths))
run(['git','add','--',*paths])
run(['git','diff','--check','--cached'])
env=os.environ.copy();env['RECAMAN_ALLOW_BURST']='1'
log=run(['git','commit','-m','research: preserve November 5 source coupling and counter bounds','--',*paths],cap=25,env=env)
sha=run(['git','rev-parse','HEAD']).strip()
print('SNAPSHOT '+sha,flush=True)
push=run(['git','push','origin',sha+':refs/heads/main'],cap=20)
remote=run(['git','ls-remote','origin','refs/heads/main'],cap=10).split()[0]
assert remote==sha
try:
 runs=json.loads(run(['gh','run','list','--repo','hirokidaichi/recaman-lean-research','--commit',sha,'--limit','3','--json','databaseId,status,conclusion,url,headSha'],cap=5))
 ci='; '.join(str(r.get('status'))+'/'+str(r.get('conclusion')) for r in runs) or 'not yet visible; unconfirmed'
except Exception as e:runs=[];ci='unconfirmed: '+str(e)[:200]
receipt={'snapshot_sha':sha,'target':'origin/main','push_ok':True,'remote_matches':True,'remote_sha_at_snapshot_readback':remote,'snapshot_readback_at':now().isoformat(),'hosted_ci':ci,'hosted_runs':runs,'publication_hook_git_cpu':'unmeasured, not0','source_validation':'H42 PASS; all55 current-byte -M512 receipts; tool suite PASS','journal_stopped_before_commit':True,'receipt_commit':'this receipt is persisted in the following doc-only commit; its own SHA is reported in chat and git history'}
(P/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
(P/'SNAPSHOT_COMMIT.log').write_text(log+'\n'+push)
run(['python3','/private/tmp/recaman_daily_report.py'])
run(['python3','viewer/gen_manifest.py'])
finalpaths=['docs/RESEARCH_HANDOFF_2026-11-05_DAILY.md',str(P/'PUBLICATION_RECEIPT.json'),str(P/'SNAPSHOT_COMMIT.log'),str(P/'JOURNAL_STATUS.json'),'viewer/manifest.json']
d=json.loads((P/'PUBLICATION_PATHS.json').read_text());d['publication_receipt_paths']=finalpaths;(P/'PUBLICATION_PATHS.json').write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n');finalpaths.append(str(P/'PUBLICATION_PATHS.json'))
run(['git','status','-s'])
run(['git','add','--',*finalpaths])
run(['git','commit','-m','docs: record verified daily research publication','--',*finalpaths],cap=25)
last=run(['git','rev-parse','HEAD']).strip();run(['git','push','origin',last+':refs/heads/main'],cap=20)
remote2=run(['git','ls-remote','origin','refs/heads/main'],cap=10).split()[0];assert remote2==last
clean=run(['git','status','--porcelain'])
try:latest=json.loads(run(['gh','run','list','--repo','hirokidaichi/recaman-lean-research','--commit',last,'--limit','3','--json','databaseId,status,conclusion,url,headSha'],cap=5))
except Exception:latest=[]
result={'snapshot_sha':sha,'final_sha':last,'target':'origin/main','remote_matches':remote2==last,'clean_worktree':not clean.strip(),'remaining_changes':clean,'latest_hosted_runs':latest,'completed_jst':now().isoformat()}
Path('/private/tmp/recaman_publication_final.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(result,ensure_ascii=False),flush=True)
