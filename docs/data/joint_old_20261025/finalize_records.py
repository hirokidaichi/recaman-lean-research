"""Render only a closed, genuine journal. Never supplies/changes timestamps."""
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import json, subprocess

packet=Path(__file__).parent
root=packet.parents[2]
journal=root/'docs/data/daily_research/2026-10-25.json'
j=json.loads(journal.read_text())
assert j['cursor'] is None, 'stop the actual active session before final accounting'
s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status','--date','2026-10-25'],text=True,cwd=root))
phase=defaultdict(float);unit=defaultdict(float)
for r in j['segments']:
    seconds=(datetime.fromisoformat(r['end'])-datetime.fromisoformat(r['start'])).total_seconds()
    phase[r['phase']]+=seconds
    unit[r['unit']]+=seconds
work=sum(phase.get(k,0) for k in ('setup','research','audit','handoff'))
assert abs(work-s['confirmed_work_seconds'])<.005,(work,s)
first=j['events'][0]['at'];last=j['events'][-1]['at']
assert j['events'][-1]['action']=='stop'
def fmt(sec):
    whole=round(sec,3)
    return f'{int(whole//60)}分{whole%60:06.3f}秒'
def clock(t): return datetime.fromisoformat(t).strftime('%H:%M:%S.%f')
summary={'date':'2026-10-25','session':j['events'][0]['session'],'start':first,'end':last,
         'confirmed_work_seconds':s['confirmed_work_seconds'],'shortfall_seconds':s['shortfall_seconds'],
         'phase_seconds':dict(phase),'unit_seconds':dict(unit),'excluded_non_work_seconds':s['excluded_non_work_seconds'],
         'unconfirmed_gap_seconds':s['unconfirmed_gap_seconds'],'overtime_work_seconds':s['overtime_work_seconds'],
         'cpu_complete':False,'source':'closed journal, no backfill; work is confirmed wall intervals, not pure CPU or pure thinking'}
(packet/'final-time-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
text=f'''実開始 {clock(first)}、実終了 {clock(last)} JST。`confirmed_work_seconds={s['confirmed_work_seconds']}`、**{fmt(work)}**。
120分に対する不足 **{fmt(s['shortfall_seconds'])}**。起動遅れ・枠内の終了余白を遡及補填しない。
待機/blocked除外 {s['excluded_non_work_seconds']}、未確認gap {s['unconfirmed_gap_seconds']}秒、枠外作業 {s['overtime_work_seconds']}秒。
終了cursorはnull、open区間の先取りなし。journalは確認済み作業区間で純CPU/純思考の計測ではない。

| Phase | 予定 | 確認済み実績 |
| --- | --- | --- |
| setup | 10分 | {fmt(phase.get('setup',0))} |
| research（活用+探索） | 60+30分 | {fmt(phase.get('research',0))} |
| audit | 10分 | {fmt(phase.get('audit',0))} |
| handoff | 10分 | {fmt(phase.get('handoff',0))} |

実unitごとの区間（上表の内訳で追加加算しない）:

| Unit | 実績 |
| --- | --- |
'''
for name,seconds in unit.items():text+=f'| {name} | {fmt(seconds)} |\n'
text+='\n[確定時間のJSON](data/joint_old_20261025/final-time-summary.json)。並行CPUを足さず、前日/別sessionの時間を含めない。\n'
p=root/'docs/RESEARCH_HANDOFF_2026-10-25_DAILY.md';doc=p.read_text();a=doc.index('<!-- FINAL_TIME_START -->');b=doc.index('<!-- FINAL_TIME_END -->',a)
doc=doc[:a]+'<!-- FINAL_TIME_START -->\n'+text+doc[b:];p.write_text(doc)
for p in sorted((root/'docs').glob('HYPOTHESIS_CARD_2026-10-25_*.md')):
    t=p.read_text();marker='\n## 当日journal確定実績\n'
    if marker in t:t=t.split(marker)[0]
    p.write_text(t+marker+f'親cycle R-20261025-01: {clock(first)}〜{clock(last)}、確認済み{fmt(work)}、不足{fmt(s["shortfall_seconds"])}。\nこのcardを別cycleとして加算せず、実unit/phaseの内訳は[当日DAILY](RESEARCH_HANDOFF_2026-10-25_DAILY.md)と[journal](data/daily_research/2026-10-25.json)を参照。待機・未確認・CPU・前日分の加算なし。\n')
p=root/'docs/DAILY_RESEARCH_SCHEDULE.md';t=p.read_text();marker='\n10/25のjournal確定値:'
if marker in t:t=t.split(marker)[0]
p.write_text(t+marker+f' {clock(first)}〜{clock(last)}、{fmt(work)}、不足{fmt(s["shortfall_seconds"])}。正本は当日DAILY/journal。\n')
cpath=packet/'final-consistency.json'
c=json.loads(cpath.read_text());c['journal']='stopped; cursor null';c['confirmed_work_seconds']=s['confirmed_work_seconds'];cpath.write_text(json.dumps(c,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False,indent=2))
