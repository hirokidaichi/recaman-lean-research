"""Transfer a stopped journal's confirmed totals to today's handoff only."""
import collections,datetime,json
from pathlib import Path
base=Path(__file__).resolve().parent
root=base.parents[2]
journal=root/'docs/data/daily_research/2026-10-29.json'
j=json.loads(journal.read_text());stop=json.loads((base/'STOP_RESULT.json').read_text())
if j['cursor'] is not None or stop.get('cursor') is not None:raise SystemExit('journal still active; no final credit')
if stop.get('date')!='2026-10-29':raise SystemExit('unexpected date')
phase=collections.defaultdict(float);mode=collections.defaultdict(float)
for x in j['segments']:
 sec=(datetime.datetime.fromisoformat(x['end'])-datetime.datetime.fromisoformat(x['start'])).total_seconds();phase[x['phase']]+=sec
 if x['phase']=='research':
  tail=x['unit'].split('/')[-1]
  local=tail.startswith(('H08','H09','H10','H17','H21'))
  mode['local_exploration' if local else 'exploitation']+=sec
confirmed=sum(phase[k] for k in ['setup','research','audit','handoff'])
assert abs(confirmed-stop['confirmed_work_seconds'])<0.002
start=j['segments'][0]['start'];end=j['segments'][-1]['end']
fmt=lambda sec:f'{int(sec//60)}分{sec%60:06.3f}秒'
short=max(0,7200-confirmed)
summary={'date':j['date'],'actual_start':start,'actual_end':end,'confirmed_work_seconds':stop['confirmed_work_seconds'],'shortfall_seconds':stop['shortfall_seconds'],'phase_seconds':dict(phase),'research_mode_seconds':dict(mode),'waiting_or_blocked_excluded_seconds':{k:v for k,v in phase.items() if k in ['waiting','blocked']},'unconfirmed_gaps':j['unconfirmed_gaps'],'journal':'docs/data/daily_research/2026-10-29.json','journal_is_not_pure_cpu_or_thinking_time':True}
(base/'FINAL_TIME_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
text=f'''- 日付: 2026-10-29 JST、実開始 **{start[11:26]}**、実終了 **{end[11:26]}**。
- `confirmed_work_seconds={stop['confirmed_work_seconds']}` = **{fmt(confirmed)}**。120分に対する不足 **{fmt(short)}**。開始遅延を遡及補填せず、終了余裕も実績へ足していない。
- 待機/blockedの研究計上なし。未確認gapは{len(j['unconfirmed_gaps'])}件。予定/open区間は実績にせず、cursorはnull。journalは確認した作業区間であり純CPU/純思考時間ではない。

| 配分 | 当初予定 | journal確定実績 |
|---|---:|---:|
| setup |10分|{fmt(phase['setup'])}|
| C1活用 |60分|{fmt(mode['exploitation'])}|
| 局所探索 |30分|{fmt(mode['local_exploration'])}|
| 別pass監査/検証 |10分|{fmt(phase['audit'])}|
| 引き継ぎ |10分|{fmt(phase['handoff'])}|

actual配分は予定と別記した。数学unitの完了後、監査/再現失敗の記録・source復元検証へ移し、監査超過{fmt(max(0,phase['audit']-600))}を研究枠から支払った。setup縮小と実開始遅れも含むため、当初の100分研究監査枠を独立の追加時間として二重計上しない。CPU別計上はCPU_ACCOUNTINGを参照。全体連続無変化0、旧r4枝STOPPED2回は保持。

07:45以降に新数学探索なし。自分の検証/計算は全て終了済み、journal stopを確認。stop後の確定値転記と終了通知はjournal時間へ追加していない。次回はH-20261030-01の未実行unitからであり、今日の完了unitを反復しない。
'''
p=root/'docs/RESEARCH_HANDOFF_2026-10-29_DAILY.md';s=p.read_text();marker='## 確定実績\n';assert marker in s;s=s[:s.index(marker)+len(marker)]+'\n'+text;p.write_text(s)
p=root/'docs/DAILY_RESEARCH_SCHEDULE.md';s=p.read_text();marker='\n## 2026-10-29 実績と引き継ぎ\n';assert marker not in s
s+=marker+f'''\n当日journalの実開始{start[11:19]}〜実終了{end[11:19]}、confirmed {fmt(confirmed)}、不足{fmt(short)}。待機/未確認gapを研究時間へ加えていない。詳細な予定/実績・CPU/失敗は[10/29 DAILY](RESEARCH_HANDOFF_2026-10-29_DAILY.md)と[journal](data/daily_research/2026-10-29.json)。E451三run全長free-gapがPROVED-LEAN、四runE456は供給19/数値残余のみ。一般Q/C1は未解決。次は[H-20261030-01](HYPOTHESIS_CARD_2026-10-30_FOUR_RUN_OLD_TARGET.md)。\n''';p.write_text(s)
for name in ['HYPOTHESIS_CARD_2026-10-29_OLD_TARGET_TAIL.md','HYPOTHESIS_CARD_2026-10-29_INITIAL_S_OLD_PAIR.md','HYPOTHESIS_CARD_2026-10-29_INITIAL_S_TWO_SHAPES.md','HYPOTHESIS_CARD_2026-10-29_LOCAL_SOURCE_PREFIX.md','HYPOTHESIS_CARD_2026-10-29_RUN_COUNT_BUDGET.md']:
 p=root/'docs'/name
 with p.open('a') as f:f.write(f'\n## 当日実績への参照\n\n親R-20261029-01のjournal確定実績は{fmt(confirmed)}（不足{fmt(short)}）。このカードへ親の全時間を追加計上しない。unit別時刻/予定と実績/CPUは[当日DAILY](RESEARCH_HANDOFF_2026-10-29_DAILY.md)と[journal](data/daily_research/2026-10-29.json)を正本とする。\n')
print(json.dumps(summary,indent=2))
