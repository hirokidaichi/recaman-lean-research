"""Final explicit docs-only publication receipt, with enabled hook and normal push."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,subprocess,signal,os
P=Path(__file__).resolve().parent;R=P/'publication_snapshot';clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
def run(argv,timeout=25):
    left=(clock().replace(hour=8,minute=0,second=0,microsecond=0)-clock()).total_seconds();assert clock().hour==7 and left>10
    proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
    try:out,_=proc.communicate(timeout=min(timeout,left-7))
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid,signal.SIGKILL);out,_=proc.communicate();raise RuntimeError('Own receipt process timeout\n'+out)
    if proc.returncode:raise RuntimeError('Command failed '+repr(argv)+'\n'+out)
    return out
r=json.loads((R/'PUBLICATION_RECEIPT.json').read_text());assert r['normal_push']=='success'and r['ls_remote_matches']
assert run(['git','rev-parse','HEAD']).strip()==r['research_snapshot_sha']and run(['git','branch','--show-current']).strip()=='main'
daily=Path('docs/RESEARCH_HANDOFF_2026-11-25_DAILY.md');txt=daily.read_text();a=txt.index('<!-- PUBLICATION_BEGIN -->');b=txt.index('<!-- PUBLICATION_END -->')
obs=r.get('hosted_ci','unconfirmed');ci=[]
if isinstance(obs,list):
    for z in obs:
        desc=', '.join(str(q.get('name'))+':'+str(q.get('status'))+'/'+str(q.get('conclusion'))for q in z.get('runs',[]))
        ci.append(z['kind']+': '+(desc or z.get('state','unconfirmed')))
else:ci=[str(obs)]
body=f'''研究snapshot **{r['research_snapshot_sha']}** を **origin/main** へ通常pushし、`git ls-remote origin refs/heads/main`との完全一致を確認（{r['checked_at_jst']}）。hosted CI観測 **{'; '.join(ci)}**。詳細は[receipt](data/depth_general_20261125/publication_snapshot/PUBLICATION_RECEIPT.json) / CI_SNAPSHOT.json。完了成功を推定しない。ローカル静的検証/remote到達/hosted CIを区別する。

Nov23未公開158paths・Nov24管理2pathsと当日の検証済み研究・確定journalを保存し、この研究snapshotの未保存対象なし。旧実績を当日へ加算せず、foreign Nov07 journalは保持・対象外。新Lean0/全PAPER human review pending。この照合はdocs-only最終commitへ保存し、その自己SHA/remote照合/最終CIは当日chatへ報告する。'''
daily.write_text(txt[:a]+'<!-- PUBLICATION_BEGIN -->\n'+body+'\n'+txt[b:])
paths=[str(daily),str(R/'PUBLICATION_RECEIPT.json'),str(R/'COMMIT_AND_PUSH.log')]
if(R/'CI_SNAPSHOT.json').exists():paths.append(str(R/'CI_SNAPSHOT.json'))
paths=[str(Path(s).relative_to(Path.cwd()))if Path(s).is_absolute()else s for s in paths]
base=json.loads((P/'BASELINE.json').read_text())
changes=set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())
assert changes-set(paths)-set(base['unowned'])==set(),'Preserve unexpected changes; do not claim a fully saved snapshot'
run(['git','add','--',*paths]);run(['git','diff','--cached','--check'])
assert set(run(['git','diff','--cached','--name-only']).splitlines())==set(paths)
log=run(['git','commit','-m','docs: record verified daily research publication (2026-11-25)','--',*paths])
sha=run(['git','rev-parse','HEAD']).strip();push=run(['git','push','origin',sha+':refs/heads/main'])
remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0];assert remote==sha
leftover=set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())-set(base['unowned'])
assert not leftover,('Owned publication records remain unsaved',leftover)
out={'final_receipt_sha':sha,'research_snapshot_sha':r['research_snapshot_sha'],'branch':'main','destination':'origin/main','normal_push':True,'remote_match':True,'checked_jst':clock().isoformat(),'hosted_ci':'research SHA observed in committed receipt; final receipt commit separately unconfirmed','remaining_status':run(['git','status','--short']).splitlines()}
Path('/tmp/recaman-20261125-final-publication.json').write_text(json.dumps(out,indent=2)+'\n');Path('/tmp/recaman-20261125-final-publication.log').write_text(log+'\n'+push)
print(json.dumps(out,indent=2))
