"""Exact docs-only receipt commit; final self-SHA is reported in chat."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,os,subprocess,signal
P=Path(__file__).resolve().parent
R=P/'publication_snapshot'
clock=lambda:datetime.now(ZoneInfo('Asia/Tokyo'))
def run(argv,timeout=25):
 left=(clock().replace(hour=8,minute=0,second=0,microsecond=0)-clock()).total_seconds()
 assert clock().hour==7 and left>8
 proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
 try:out,_=proc.communicate(timeout=min(timeout,left-5))
 except subprocess.TimeoutExpired:
  os.killpg(proc.pid,signal.SIGKILL);out,_=proc.communicate();raise RuntimeError('Own publication process timeout\n'+out)
 if proc.returncode:raise RuntimeError('Command failed '+repr(argv)+'\n'+out)
 return out
r=json.loads((R/'PUBLICATION_RECEIPT.json').read_text())
assert run(['git','rev-parse','HEAD']).strip()==r['research_snapshot_sha']
assert run(['git','branch','--show-current']).strip()=='main'
p=Path('docs/RESEARCH_HANDOFF_2026-11-22_DAILY.md');s=p.read_text();a=s.index('<!-- PUBLICATION_BEGIN -->');b=s.index('<!-- PUBLICATION_END -->')
ci=r.get('hosted_ci','unconfirmed')
if isinstance(ci,list):
 parts=[]
 for obs in ci:
  runs=obs.get('runs',[])
  detail=', '.join(str(x.get('name'))+':'+str(x.get('status'))+'/'+str(x.get('conclusion'))for x in runs)
  parts.append(obs['kind']+': '+(detail or ('observed; no runs returned yet' if obs.get('state')=='observed' else obs.get('state','unconfirmed'))))
 ci='; '.join(parts)
body=f'''研究snapshot **{r['research_snapshot_sha']}** を **origin/main** へ通常pushし、`git ls-remote origin refs/heads/main`との完全一致を確認（{r['checked_at_jst']}）。hosted CI観測 **{ci}**。詳細は[receipt](data/depth_general_20261122/publication_snapshot/PUBLICATION_RECEIPT.json)とCI_SNAPSHOT.json参照、完了成功とは推定しない。ローカル静的検証（新Lean全体buildなし）/remote到達/hosted CIを分ける。\n\nこの照合記録はdocs-onlyの最終commitへ保存し、その自己SHA/remote照合/CIは当日chatへ報告する。未保存の研究成果なし。他sessionの11/07 journalは変更せず対象外。'''
p.write_text(s[:a]+'<!-- PUBLICATION_BEGIN -->\n'+body+'\n'+s[b:])
paths=[str(p),str(R/'PUBLICATION_RECEIPT.json'),str(R/'COMMIT_AND_PUSH.log')]
if (R/'CI_SNAPSHOT.json').exists():paths.append(str(R/'CI_SNAPSHOT.json'))
paths=[str(Path(x).relative_to(Path.cwd())) if Path(x).is_absolute() else x for x in paths]
run(['git','add','--',*paths]);run(['git','diff','--cached','--check'])
assert set(run(['git','diff','--cached','--name-only']).splitlines())==set(paths)
log=run(['git','commit','-m','docs: record confirmed daily research publication (2026-11-22)','--',*paths])
sha=run(['git','rev-parse','HEAD']).strip();push=run(['git','push','origin',sha+':refs/heads/main'])
remote=run(['git','ls-remote','origin','refs/heads/main']).split()[0];assert sha==remote
out={'final_receipt_sha':sha,'research_snapshot_sha':r['research_snapshot_sha'],'branch':'main','target':'origin/main','normal_push':True,'remote_match':True,'observed_jst':clock().isoformat(),'hosted_ci':'research-snapshot observation in committed receipt; final-receipt commit not confirmed','status':run(['git','status','--short']).splitlines()}
Path('/tmp/recaman-20261122-final-publication.json').write_text(json.dumps(out,indent=2)+'\n')
Path('/tmp/recaman-20261122-final-publication.log').write_text(log+'\n'+push)
print(json.dumps(out,indent=2))
