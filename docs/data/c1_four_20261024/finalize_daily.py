"""Publish only closed-journal actuals; never credit an open interval or previous day."""
from collections import defaultdict
from datetime import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess

base=Path(__file__).resolve().parent
root=base.parents[2]
journal=root/'docs/data/daily_research/2026-10-24.json'
daily=root/'docs/RESEARCH_HANDOFF_2026-10-24_DAILY.md'
log=json.loads(journal.read_text())
assert log['cursor'] is None, 'stop the genuine journal before finalizing'
assert log['events'][-1]['action']=='stop'
assert {e['session'] for e in log['events']}=={'785c43d7-babb-4467-9063-967a228328b7'}
status=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status','--date','2026-10-24'],cwd=root,text=True))
assert status['open_interval_unconfirmed_seconds']==0 and status['overtime_work_seconds']==0
stats=defaultdict(float); units={}; card_seconds=defaultdict(float)
work={'setup','research','audit','handoff'};first=None
for seg in log['segments']:
    if seg['phase'] not in work:continue
    if first is None:first=seg['start']
    sec=(datetime.fromisoformat(seg['end'])-datetime.fromisoformat(seg['start'])).total_seconds()
    group=seg['phase']
    if group=='research':
        group='exploitation' if seg['unit'].startswith(('H-20261024-01/','H-20261024-02/','H-20261024-04/','H-20261024-09/','H-20261024-13/')) else 'exploration'
        m=re.match(r'H-20261024-\d{2}',seg['unit'])
        if m:card_seconds[m[0]]+=sec
    stats[group]+=sec
    u=units.setdefault(seg['unit'],dict(start=seg['start'],end=seg['end'],seconds=0.0,phase=seg['phase']))
    u['end']=seg['end'];u['seconds']+=sec
end=log['events'][-1]['at']
window=datetime.fromisoformat(first).replace(hour=6,minute=0,second=0,microsecond=0)
startup=(datetime.fromisoformat(first)-window).total_seconds()
ending=(window.replace(hour=8)-datetime.fromisoformat(end)).total_seconds()
assert abs(startup+ending-status['shortfall_seconds'])<.002, 'unexpected unaccounted in-window interruption'
assert abs(sum(stats.values())-status['confirmed_work_seconds'])<.002
confirmed=status['confirmed_work_seconds'];mins,secs=divmod(confirmed,60)
rows=['| 区分 | 当初予定（分） | closed journal実績（秒） |','| --- | ---: | ---: |']
for k,n,p in [('setup','開始確認',10),('exploitation','C1活用 H01/H04/H09/H13',60),('exploration','局所探索 H03/H05〜H08/H10〜H12',30),('audit','別pass監査',10),('handoff','引き継ぎ',10)]:rows.append(f'| {n} | {p} | {stats[k]:.3f} |')
timeline=['| 実unit | JST開始〜終了 | 確認済み秒 |','| --- | --- | ---: |']
for n,u in units.items():timeline.append(f"| {n} | {u['start'][11:19]}〜{u['end'][11:19]} | {u['seconds']:.3f} |")
text='\n'.join([
 f'- 実作業開始 `{first}`、実終了 `{end}`。journal待機開始は05:59:05.837049。',
 f'- **confirmed_work_seconds={confirmed:.3f}（{int(mins)}分{secs:.3f}秒）**。120分への不足 **{status["shortfall_seconds"]:.3f}秒**。',
 f'- 開始側の未計上{startup:.3f}秒を遡及加算しない。待機等除外 `{json.dumps(status["excluded_non_work_seconds"],ensure_ascii=False)}`、gap {status["unconfirmed_gap_seconds"]:.3f}秒、open0、時間外0。',
 f'- 待機68.233秒のうち約54.163秒は6時前。窓内の開始不足{startup:.3f}秒と終了側余裕{ending:.3f}秒が今回の不足を構成し、待機全体を重ねて加算しない。',
 '- 前日以前の朝18分51秒・追加98分13秒・2026-10-23実績を本日へ加えていない。',
 '- journalは担当が確認した研究・資料読取・監視・検証・記録区間で、純思考時間やCPU時間の測定ではない。CPUは別計上。',
 '',*rows,'',*timeline,'',
 '- 親cycle R-20261024-01に全てを包含。子card時間とsetup/audit/handoffを重ねて加算しない。',
 '- [最終status](data/c1_four_20261024/final-journal-status.json)、[集計JSON](data/c1_four_20261024/final-allocation.json)、[packet manifest](data/c1_four_20261024/final-packet-manifest.json)。',
 '- stop後の集計・manifest書込はjournalへ遡及加算していない。'])
old=daily.read_text();new,count=re.subn(r'(?s)(<!-- FINAL_METRICS_START -->).*?(<!-- FINAL_METRICS_END -->)',lambda m:m[1]+'\n'+text+'\n'+m[2],old);assert count==1
daily.write_text(new)
for p in sorted((root/'docs').glob('HYPOTHESIS_CARD_2026-10-24_*.md')):
    s=p.read_text();m=re.search(r'H-20261024-\d{2}',s);assert m,p
    ctext=f'このカードに属するresearch区間は **{card_seconds[m[0]]:.3f}秒**。共通setup/監査/handoffは親cycleでのみ計上。\nclosed journal: `docs/data/daily_research/2026-10-24.json`、親全体confirmed_work_seconds={confirmed:.3f}。\n'
    marker='<!-- DAILY_CARD_ACTUAL_START -->'
    if marker in s:s=re.sub(r'(?s)<!-- DAILY_CARD_ACTUAL_START -->.*?<!-- DAILY_CARD_ACTUAL_END -->',marker+'\n'+ctext+'<!-- DAILY_CARD_ACTUAL_END -->',s)
    else:s+='\n## 最終実績（closed journal）\n\n'+marker+'\n'+ctext+'<!-- DAILY_CARD_ACTUAL_END -->\n'
    p.write_text(s)
schedule=root/'docs/DAILY_RESEARCH_SCHEDULE.md';s=schedule.read_text()
if '## 2026-10-24の確定実績' not in s:
    s+=f'\n## 2026-10-24の確定実績\n\n{first[11:19]}〜{end[11:19]} JST、confirmed_work_seconds={confirmed:.3f}（{int(mins)}分{secs:.3f}秒）。\n待機68.233秒は除外、不足{status["shortfall_seconds"]:.3f}秒。前日実績/予定/CPUの加算なし。\n[DAILY](RESEARCH_HANDOFF_2026-10-24_DAILY.md)、[journal](data/daily_research/2026-10-24.json)。\n'
    schedule.write_text(s)
(base/'final-journal-status.json').write_text(json.dumps(status,ensure_ascii=False,indent=2)+'\n')
(base/'final-allocation.json').write_text(json.dumps(dict(start=first,end=end,phase_seconds=stats,unit_intervals=units,card_research_seconds=card_seconds,startup_uncredited_seconds=startup,ending_uncredited_seconds=ending,confirmed_work_seconds=confirmed,shortfall_seconds=status['shortfall_seconds']),ensure_ascii=False,indent=2)+'\n')
sanity_path=base/'final-handoff-sanity.json'
sanity=json.loads(sanity_path.read_text())
sanity.update(actuals_pending_genuine_stop=False,genuine_stop_seen=True,confirmed_work_seconds=confirmed,shortfall_seconds=status['shortfall_seconds'])
sanity_path.write_text(json.dumps(sanity,ensure_ascii=False,indent=2)+'\n')
manifest=base/'final-packet-manifest.json';files=[]
for p in sorted(base.rglob('*')):
    if not p.is_file() or p==manifest or '__pycache__' in p.parts:continue
    d=p.read_bytes();files.append(dict(path=str(p.relative_to(root)),bytes=len(d),sha256=hashlib.sha256(d).hexdigest()))
external_paths=[journal,daily,schedule,root/'docs/CURRENT_FRONTIER.md',root/'docs/GLOSSARY.md',root/'docs/PROOF_MAP.md',root/'docs/RESEARCH_PORTFOLIO.md',root/'docs/HYPOTHESIS_CARD_2026-10-21_C1_AREA.md',root/'docs/EVIDENCE_REGISTRY.tsv',root/'docs/DAILY_RESEARCH_AUTOMATION_PROMPT.md',root/'docs/RESEARCH_NOTE_2026-10-24_C1_INPUTS.md',root/'docs/HYPOTHESIS_CARD_2026-10-25_JOINT_OLD_SUPPLY.md']
external_paths+=list((root/'docs').glob('HYPOTHESIS_CARD_2026-10-24_*.md'))
external_paths+=list((root/'docs/statement_audits').glob('E-39*.md'))
external=[]
for p in sorted(set(external_paths)):
    d=p.read_bytes();external.append(dict(path=str(p.relative_to(root)),bytes=len(d),sha256=hashlib.sha256(d).hexdigest()))
manifest.write_text(json.dumps(dict(frozen_at=datetime.now().astimezone().isoformat(),scope='final closed journal, handoff/cards and evidence packet; excludes manifest itself and pycache',packet_files=files,external_files=external),ensure_ascii=False,indent=2)+'\n')
print(json.dumps(dict(confirmed_work_seconds=confirmed,shortfall_seconds=status['shortfall_seconds'],ended_jst=end,packet_files=len(files)),ensure_ascii=False))
