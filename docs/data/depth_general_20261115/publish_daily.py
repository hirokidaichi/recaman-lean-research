"""Authorized daily snapshot only. Exact files, normal SHA push, hooks intact.

Run only after journal stop. C1 stores finalized research; C2 stores C1's
publication receipt. C2's own final remote/CI observation is returned to chat
and /tmp, avoiding a self-referential commit SHA inside that commit.
"""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib, json, os, signal, subprocess, sys, tempfile, time

ROOT=Path(__file__).resolve().parents[3]
PACKET=ROOT/'docs/data/depth_general_20261115'
DAILY=ROOT/'docs/RESEARCH_HANDOFF_2026-11-15_DAILY.md'
JOURNAL=ROOT/'docs/data/daily_research/2026-11-15.json'
DEST='refs/heads/main'
BASE='3780dbe7c49f03f245f21f487ea262a122ca6cb1'
clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
deadline=datetime.fromisoformat('2026-11-15T07:59:40+09:00')
logs=Path(tempfile.mkdtemp(prefix='recaman-20261115-publication-'))

def run(tag,argv,timeout=8,burst=False,required=True):
    now=clock()
    if now.date()!=deadline.date() or now>=deadline:
        raise RuntimeError('publication deadline reached')
    timeout=min(timeout,max(.1,(deadline-now).total_seconds()))
    meta={'tag':tag,'argv':argv,'started_jst':now.isoformat(),'wall_cap_seconds':timeout,
          'scope':'publication; CPU not measured or counted as research after journal stop','snapshot_burst_exception_on_this_command_only':burst}
    (logs/(tag+'-start.json')).write_text(json.dumps(meta,indent=2)+'\n')
    env=os.environ.copy();env.pop('RECAMAN_ALLOW_BURST',None)
    if burst:env['RECAMAN_ALLOW_BURST']='1'
    t=time.monotonic();reason='completed'
    with (logs/(tag+'.log')).open('w') as out:
        proc=subprocess.Popen(argv,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
        try:code=proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            reason='wall/deadline';os.killpg(proc.pid,signal.SIGKILL);code=proc.wait()
    meta.update(exit_code=code,reason=reason,finished_jst=clock().isoformat(),wall_seconds=time.monotonic()-t)
    (logs/(tag+'-result.json')).write_text(json.dumps(meta,indent=2)+'\n')
    output=(logs/(tag+'.log')).read_text()
    if required and code:raise RuntimeError(tag+' failed: '+output[-1200:])
    return code,output

def head(tag):return run(tag,['git','rev-parse','HEAD'])[1].strip()
def remote(tag,sha):
    text=run(tag,['git','ls-remote','origin',DEST],timeout=6)[1]
    actual=[r.split()[0] for r in text.splitlines() if r.split()[-1]==DEST]
    if actual!=[sha]:raise RuntimeError('remote exact SHA mismatch: '+text)
    return actual[0]
def ci(tag,sha):
    code,out=run(tag,['gh','run','list','--repo','hirokidaichi/recaman-lean-research','--branch','main',
        '--commit',sha,'--json','headSha,status,conclusion,url'],timeout=5,required=False)
    try:rows=json.loads(out) if code==0 else []
    except json.JSONDecodeError:rows=[]
    rows=[r for r in rows if r.get('headSha')==sha]
    return {'checked_at_jst':clock().isoformat(),'rows':rows,'status':'observed' if rows else 'unconfirmed'}

def main():
    if sys.argv[1:]!=['--execute']:raise RuntimeError('use --execute only after finalized journal stop')
    if clock().hour!=7 or clock().minute<45:raise RuntimeError('outside publication phase')
    journal=json.loads(JOURNAL.read_text())
    if journal.get('cursor') is not None:raise RuntimeError('journal must be stopped first')
    if '@@FINAL_WORK@@' in DAILY.read_text():raise RuntimeError('final work values not saved')
    if run('BRANCH',['git','branch','--show-current'])[1].strip()!='main':raise RuntimeError('wrong branch')
    if head('HEAD-START')!=BASE:raise RuntimeError('HEAD changed; manual integration needed')
    run('FETCH-FINAL',['git','fetch','origin','main'])
    if run('REMOTE-BASE',['git','rev-parse','origin/main'])[1].strip()!=BASE:
        raise RuntimeError('remote advanced; preserve changes, do not force or publish unintegrated snapshot')
    if run('INDEX-START',['git','diff','--cached','--name-only'])[1].strip():
        raise RuntimeError('unexpected staged files')
    for row in json.loads((PACKET/'ADOPTED_SOURCES.json').read_text()):
        if hashlib.sha256((ROOT/row['file']).read_bytes()).hexdigest()!=row['sha256']:
            raise RuntimeError('adopted source changed since capped/full check')
    paths=json.loads((PACKET/'OWNED_PATHS.json').read_text())
    if 'docs/data/daily_research/2026-11-07.json' in paths:raise RuntimeError('unowned journal in paths')
    for p in paths:
        target=ROOT/p
        if not target.is_file() or not target.resolve().is_relative_to(ROOT):raise RuntimeError('invalid owned path '+p)
    run('C1-STAGE',['git','add','--']+paths)
    staged=set(run('C1-STAGED-PATHS',['git','diff','--cached','--name-only'])[1].splitlines())
    if not staged or not staged.issubset(set(paths)):raise RuntimeError('staged scope mismatch')
    run('C1-PRECOMMIT-STATUS',['git','status','--short'])
    run('C1-COMMIT',['git','commit','-m','research: record source preloading and cut accounts (2026-11-15)','--']+paths,
        timeout=20,burst=True)
    sha1=head('C1-SHA')
    run('C1-PUSH',['git','push','origin',sha1+':'+DEST])
    remote('C1-REMOTE',sha1);ci1=ci('C1-CI',sha1)
    receipt={'research_snapshot_sha':sha1,'destination':'origin/main','normal_push':'success',
        'remote_ref':DEST,'ls_remote_matches':True,'checked_at_jst':clock().isoformat(),'hosted_ci':ci1,
        'scope':'C1 finalized research snapshot; C2 docs-only receipt SHA/remote/CI returned in chat'}
    pub=PACKET/'publication_snapshot';pub.mkdir(exist_ok=False)
    # Copy only completed C1 evidence; C2 logs stay outside the committed tree.
    for f in sorted(logs.iterdir()):(pub/f.name).write_bytes(f.read_bytes())
    (pub/'PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+'\n')
    observed='; '.join(r['status']+'/'+r.get('conclusion','')+' '+r['url'] for r in ci1['rows']) or '未確認（該当SHAのrun未取得）'
    paragraph=('研究snapshot **'+sha1+'** を通常pushで **origin/main** へ保存し、`git ls-remote origin refs/heads/main`の完全一致を確認。'
        'hosted CIは'+observed+'。ローカル全体検証とremote到達を区別する。'
        '[公開receipt](data/depth_general_20261115/publication_snapshot/PUBLICATION_RECEIPT.json)を参照。'
        'この照合記録をdocs-onlyの最終commitへ保存し、そのSHA/remote/CIは自己参照を避け当日chatへ報告する。未保存の研究成果なし。')
    text=DAILY.read_text()
    if '@@PUBLICATION@@' not in text:raise RuntimeError('publication placeholder missing')
    DAILY.write_text(text.replace('@@PUBLICATION@@',paragraph))
    paths2=[str(DAILY.relative_to(ROOT))]+[str(f.relative_to(ROOT)) for f in sorted(pub.iterdir())]
    run('C2-STAGE',['git','add','--']+paths2)
    staged2=set(run('C2-STAGED-PATHS',['git','diff','--cached','--name-only'])[1].splitlines())
    if not staged2.issubset(set(paths2)):raise RuntimeError('receipt staged scope mismatch')
    run('C2-COMMIT',['git','commit','-m','docs: save verified daily publication receipt (2026-11-15)','--']+paths2,timeout=20)
    sha2=head('C2-SHA');run('C2-PUSH',['git','push','origin',sha2+':'+DEST])
    actual=remote('C2-REMOTE',sha2);ci2=ci('C2-CI',sha2)
    status=run('FINAL-STATUS',['git','status','--short'])[1]
    final={'research_snapshot_sha':sha1,'final_receipt_commit_sha':sha2,'destination':'origin/main',
        'remote_sha':actual,'remote_matches':actual==sha2,'hosted_ci':ci2,'final_status':status,
        'research_unsaved':[],'external_publication_logs':str(logs),'finished_jst':clock().isoformat()}
    (logs/'FINAL_PUBLICATION.json').write_text(json.dumps(final,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(final,ensure_ascii=False,indent=2),flush=True)

try:main()
except Exception as exc:
    (logs/'PUBLICATION_FAILURE.json').write_text(json.dumps({'error':str(exc),'at_jst':clock().isoformat()},ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'publication_error':str(exc),'evidence':str(logs)},ensure_ascii=False),flush=True)
    raise
