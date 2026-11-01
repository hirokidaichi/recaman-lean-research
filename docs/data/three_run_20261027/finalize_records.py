"""Render only the actual stopped journal, never create or change timestamps."""
from pathlib import Path
from datetime import datetime
from collections import defaultdict
import json,subprocess,re
P=Path(__file__).resolve().parent;root=P.parents[2];day='2026-10-27'
j=json.loads((root/f'docs/data/daily_research/{day}.json').read_text())
assert j['date']==day and j['cursor'] is None,'stop the real active session first'
assert j['events'][-1]['action']=='stop'
s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status','--date',day],text=True,cwd=root))
ph=defaultdict(float);un=defaultdict(float);md=defaultdict(float)
for x in j['segments']:
 lo=datetime.fromisoformat(day+'T06:00:00+09:00');hi=datetime.fromisoformat(day+'T08:00:00+09:00')
 seconds=max(0,(min(datetime.fromisoformat(x['end']),hi)-max(datetime.fromisoformat(x['start']),lo)).total_seconds());ph[x['phase']]+=seconds;un[x['unit']]+=seconds
 if x['phase']=='research':md['exploit' if '/exploit/' in x['unit'] else 'explore' if '/explore/' in x['unit'] else 'unclassified']+=seconds
work=sum(ph[k] for k in ['setup','research','audit','handoff']);assert abs(work-s['confirmed_work_seconds'])<.005
first=j['events'][0]['at'];last=j['events'][-1]['at']
# Keep actual stop time; the journal clips work at08:00 and records overtime separately.
def fmt(v):return f'{int(v//60)}分{v%60:06.3f}秒'
def clk(t):return datetime.fromisoformat(t).strftime('%H:%M:%S.%f')
out={'date':day,'session':j['events'][0]['session'],'start':first,'end':last,'confirmed_work_seconds':s['confirmed_work_seconds'],'shortfall_seconds':s['shortfall_seconds'],'phase_seconds':dict(ph),'research_mode_seconds':dict(md),'unit_seconds':dict(un),'excluded_non_work_seconds':s['excluded_non_work_seconds'],'unconfirmed_gap_seconds':s['unconfirmed_gap_seconds'],'overtime_work_seconds':s['overtime_work_seconds'],'source':'actual closed confirmed journal; no backfill; not pure CPU/thought','cpu_measurement_complete_for_entire_session':False,'chat_delivery':'report draft is not proof of delivery; actual final message required'}
(P/'final-time-summary.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
t=f'''実開始 **{clk(first)}**、実終了 **{clk(last)} JST**。`confirmed_work_seconds={s['confirmed_work_seconds']}`、**{fmt(work)}**。
120分に対する不足 **{fmt(s['shortfall_seconds'])}**。起動遅れ/終了保存余白を遡及補填しない。
待機/blocked除外 `{s['excluded_non_work_seconds']}`、未確認gap {s['unconfirmed_gap_seconds']}秒、枠外作業 {s['overtime_work_seconds']}秒（confirmedへ加算しない）。終了stopが08:00を4.412秒超過し、確定値転記のclip不整合も8時後に修正した。stop noteの『期限前』は意図であり、実時計が正本。
終了cursor null、open区間や予定の先取りなし。journalは担当が確認した作業区間で純CPU/純思考時間ではない。

| Phase | 予定 | 確認済み実績 |
| --- | --- | --- |
| setup | 10分 | {fmt(ph['setup'])} |
| research（活用+探索） | 60+30分 | {fmt(ph['research'])} |
| audit | 10分 | {fmt(ph['audit'])} |
| handoff | 10分 | {fmt(ph['handoff'])} |

research内の明示modeは活用{fmt(md['exploit'])}/探索{fmt(md['explore'])}/未分類{fmt(md['unclassified'])}。
modeとaudit/handoffを二重加算せず、semantic audit混在区間も推定分割しない。監査超過は研究の実残枠へ反映した。

| Unit（同じ親cycleの内訳） | 実績 |
| --- | --- |
'''
for name,v in un.items():t+=f'| {name} | {fmt(v)} |\n'
t+='\n[確定時間JSON](data/three_run_20261027/final-time-summary.json)。CPU/過去日を追加加算しない。\n'
p=root/f'docs/RESEARCH_HANDOFF_{day}_DAILY.md';txt=p.read_text();a=txt.index('<!-- FINAL_TIME_START -->');b=txt.index('<!-- FINAL_TIME_END -->',a);p.write_text(txt[:a]+'<!-- FINAL_TIME_START -->\n'+t+txt[b:])
for p in sorted((root/'docs').glob('HYPOTHESIS_CARD_2026-10-27_*.md')):
 txt=p.read_text();key=re.search(r'- ID: (H-\d+-\d+)',txt).group(1);own={k:v for k,v in un.items() if k.startswith(key+'/')}
 mark='\n## 当日journal確定実績\n'
 if mark in txt:txt=txt.split(mark)[0]
 msg=f'親cycle R-20261027-01: {clk(first)}〜{clk(last)}、確認済み{fmt(work)}、不足{fmt(s["shortfall_seconds"])}。\nこのcardの明示unit実績は'+('、'.join(k+': '+fmt(v) for k,v in own.items()) if own else 'journalの実unit名を正本とする（推定割当なし）')+'。\n同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。\n'
 p.write_text(txt+mark+msg)
p=root/'docs/DAILY_RESEARCH_SCHEDULE.md';txt=p.read_text();mark='\n10/27のjournal確定値:'
if mark in txt:txt=txt.split(mark)[0]
p.write_text(txt+mark+f' {clk(first)}〜{clk(last)}、{fmt(work)}、不足{fmt(s["shortfall_seconds"])}。待機/未確認/CPU/旧日加算なし。正本は当日DAILY/journal。\n')
p=P/'final-consistency.json';c=json.loads(p.read_text());c.update(journal='stopped; cursor null',confirmed_work_seconds=s['confirmed_work_seconds'],shortfall_seconds=s['shortfall_seconds'],actual_end=last);p.write_text(json.dumps(c,ensure_ascii=False,indent=2)+'\n')
(P/'ACTIVE_RUN.md').write_text('# Closed research session 2026-10-27\n\nActual journal stop '+last+'; confirmed '+fmt(s['confirmed_work_seconds'])+', shortfall '+fmt(s['shortfall_seconds'])+'. Cursor null; no second run.\n\nE416/E423/E429/E431 PROVED-LEAN, E432 PROVED-PAPER not Lean/human reviewed. See docs/RESEARCH_HANDOFF_2026-10-27_DAILY.md and docs/RESEARCH_NOTE_2026-10-27_C1_SOURCE_FAMILY.md. Next H-20261028-01, third local ray classification first15min. Preserve r4/R19/AS failures and no same-job resource extension.\n\nReport draft is not proof of delivery; use actual final message in thread history for same-day deduplication. Future120min is never marked complete by scheduling.\n')
print(json.dumps(out,ensure_ascii=False,indent=2))
