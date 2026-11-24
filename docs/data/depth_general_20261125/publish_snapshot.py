"""Authorized daily validated snapshot, exact paths, enabled hooks, normal origin/main push."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,os,subprocess,signal,hashlib
P=Path(__file__).resolve().parent;R=P/'publication_snapshot';clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
assert clock().hour==7 and clock().minute>=45
j=json.loads(Path('docs/data/daily_research/2026-11-25.json').read_text());assert j['cursor']is None
assert(P/'FINAL_WORK_SUMMARY.json').exists()and json.loads((P/'OWNED_CONTENT_AUDIT.json').read_text())['final_after_stop']
def run(argv,env=None,timeout=30):
    left=(clock().replace(hour=8,minute=0,second=0,microsecond=0)-clock()).total_seconds();assert left>15,'Deadline margin exhausted'
    proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True,env=env)
    try:out,_=proc.communicate(timeout=min(timeout,left-12))
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid,signal.SIGKILL);out,_=proc.communicate();raise RuntimeError('Own publication process timeout '+repr(argv)+'\n'+out)
    if proc.returncode:raise RuntimeError('Command failed '+repr(argv)+'\n'+out)
    return out
base=json.loads((P/'BASELINE.json').read_text());owned=json.loads((P/'OWNED_PATHS.json').read_text());audit=json.loads((P/'OWNED_CONTENT_AUDIT.json').read_text())
assert run(['git','branch','--show-current']).strip()=='main'and run(['git','rev-parse','HEAD']).strip()==base['head']
assert run(['git','config','--get','core.hooksPath']).strip()=='.githooks'
for s in base['unowned']:assert hashlib.sha256(Path(s).read_bytes()).hexdigest()==base['unowned_sha256'][s]
paths=sorted(set(owned['paths']+owned['explicit_anticipated_after_stop']));assert all(Path(s).is_file()for s in paths)
assert not any(s.startswith('Recaman')or'protected_pins/'in s or s.endswith('PROTECTED_CLAIMS.tsv')for s in paths)
changes=set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())
assert changes-set(paths)-set(base['unowned'])==set(),'Unexpected ownership change'
assert not run(['git','diff','--cached','--name-only']),'Foreign index must be preserved'
remote_before=run(['git','ls-remote','origin','refs/heads/main']).split()[0]
assert remote_before==base['origin_main'],'Remote advanced; preserve it and integrate only after separate safe review, never force'
for s,sha in audit['hashes'].items():assert hashlib.sha256(Path(s).read_bytes()).hexdigest()==sha,('Post-audit bytes changed',s)
run(['git','add','--',*paths]);run(['git','diff','--cached','--check'])
assert set(run(['git','diff','--cached','--name-only']).splitlines())==set(paths)
index_rows=run(['git','ls-files','--stage','-z','--',*paths]).split('\0')
index_verified=0
for line in index_rows:
    if not line:continue
    head,path=line.split('\t',1);mode,oid,stage=head.split();assert stage=='0'
    raw=Path(path).read_bytes();expected=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    assert oid==expected,('Index content differs from reviewed bytes',path);index_verified+=1
assert index_verified==len(paths)
env=dict(os.environ);env['RECAMAN_ALLOW_BURST']='1'
log=run(['git','commit','-m','research: pay height, source and executed-past boundaries (2026-11-25)',
         '-m','PAPER/unreviewed E775-E780 and exact controls; no Lean adoption, original source/free and canonical scopes retained. Include hash-verified unpublished Nov23 research/Nov24 administrative records and finalized Nov25 journal; foreign Nov07 journal excluded. Daily snapshot exception only, all hooks/protected claims enabled.','--',*paths],env=env)
sha=run(['git','rev-parse','HEAD']).strip();R.mkdir(exist_ok=True)
receipt={'research_snapshot_sha':sha,'destination':'origin/main','normal_push':'pending','ls_remote_matches':False,
         'base_remote':remote_before,'journal_stop':j['events'][-1]['at'],'owned_path_count':len(paths),
         'precommit_index_blob_audit':'all '+str(index_verified)+' stage0 objects equal the audited working bytes',
         'validation_scope':json.loads((P/'PAPER_ADOPTION_INDEX.json').read_text()),'hosted_ci':'unconfirmed until explicit read',
         'scope':'Validated docs/evidence snapshot with finalized journal; no new Lean/full build. Final docs-only receipt commit self-SHA is reported in chat.'}
(R/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
try:
    push=run(['git','push','origin',sha+':refs/heads/main'],timeout=25)
    remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0];assert remote==sha
except Exception as exc:
    receipt.update({'normal_push':'failed or unconfirmed','error':str(exc),'checked_at_jst':clock().isoformat()})
    (R/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');(R/'COMMIT_AND_PUSH.log').write_text(log+'\n'+str(exc)+'\n');raise
receipt.update({'normal_push':'success','ls_remote_matches':True,'remote_sha':remote,'checked_at_jst':clock().isoformat()})
(R/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n');(R/'COMMIT_AND_PUSH.log').write_text(log+'\n'+push)
print(json.dumps(receipt,indent=2))
