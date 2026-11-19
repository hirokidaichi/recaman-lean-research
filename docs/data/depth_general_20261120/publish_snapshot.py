"""Authorized daily snapshot. Exact owned paths, enabled hooks, normal main push."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,os,subprocess,signal,time,hashlib,tempfile
P=Path(__file__).resolve().parent
clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
assert clock().hour==7 and clock().minute>=45
journal=json.loads(Path('docs/data/daily_research/2026-11-20.json').read_text())
assert journal['cursor'] is None
assert (P/'FINAL_WORK_SUMMARY.json').exists()
def run(argv,env=None,timeout=30):
 remaining=(clock().replace(hour=8,minute=0,second=0,microsecond=0)-clock()).total_seconds()
 assert remaining>12,'Publication deadline margin exhausted'
 proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True,env=env)
 try:out,_=proc.communicate(timeout=min(timeout,remaining-10))
 except subprocess.TimeoutExpired:
  os.killpg(proc.pid,signal.SIGKILL);out,_=proc.communicate();raise RuntimeError('Timed out own process '+argv[0]+'\n'+out)
 if proc.returncode:raise RuntimeError('Command failed '+repr(argv)+'\n'+out)
 return out
base=json.loads((P/'BASELINE.json').read_text());ownership=json.loads((P/'OWNED_PATHS.json').read_text())
assert run(['git','branch','--show-current']).strip()=='main'
assert run(['git','rev-parse','HEAD']).strip()==base['head']
assert run(['git','config','--get','core.hooksPath']).strip()=='.githooks'
for unowned in base['unowned']:
 assert hashlib.sha256(Path(unowned).read_bytes()).hexdigest()==base['unowned_sha256']
paths=sorted(set(ownership['paths']+ownership.get('explicit_anticipated_after_stop',[])))
assert all(Path(x).is_file()for x in paths)
assert not any('protected_pins/' in x or x.endswith('PROTECTED_CLAIMS.tsv')for x in paths)
changes=set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())
assert changes-set(paths)-set(base['unowned'])==set(),'Unexpected ownership change'
remote_before=run(['git','ls-remote','origin','refs/heads/main']).split()[0]
assert remote_before==base['origin_main'],'Remote advanced; do not overwrite'
run(['git','add','--',*paths])
run(['git','diff','--cached','--check'])
index=set(run(['git','diff','--cached','--name-only']).splitlines())
assert index==set(paths),'Unexpected preexisting index; preserve it'
env=dict(os.environ);env['RECAMAN_ALLOW_BURST']='1'
commitlog=run(['git','commit','-m','research: record activation cost counterfamilies and greedy candidate ranks (2026-11-20)','-m','PAPER proofs and finite controls only; no new Lean adoption. Preserve original-source, canonical and finite/infinite scope. Includes immutable owned Nov19 carryover and finalized Nov20 journal.','--',*paths],env=env)
sha=run(['git','rev-parse','HEAD']).strip()
pushlog=run(['git','push','origin',sha+':refs/heads/main'])
remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0];assert remote==sha
receipt={'research_snapshot_sha':sha,'destination':'origin/main','normal_push':'success','ls_remote_matches':True,'remote_sha':remote,'checked_at_jst':clock().isoformat(),'hosted_ci':'unconfirmed, to be read after push','journal_stop':journal['events'][-1]['at'],'validation_scope':json.loads((P/'ADOPTED_SOURCES.json').read_text()),'scope':'Validated research snapshot; subsequent exact docs-only receipt commit records this SHA, its own final SHA is reported in chat'}
r=P/'publication_snapshot';r.mkdir(exist_ok=True)
(r/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
(r/'COMMIT_AND_PUSH.log').write_text(commitlog+'\n'+pushlog)
print(json.dumps(receipt,indent=2))
