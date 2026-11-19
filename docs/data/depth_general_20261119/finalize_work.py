"""Post-stop bookkeeping only. Reads confirmed journal, never creates time."""
from pathlib import Path
from datetime import datetime
import json,subprocess
P=Path(__file__).resolve().parent
J=Path('docs/data/daily_research/2026-11-19.json')
d=json.loads(J.read_text())
s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
assert d['cursor'] is None, 'journal must be stopped before final totals'
assert s['open_interval_unconfirmed_seconds']==0
session='3e3b2bfb-dcb1-4749-be0d-bdbc3bc6070f'
starts=[e['at']for e in d['events']if e['action']=='start' and e['session']==session]
stops=[e['at']for e in d['events']if e['action']=='stop' and e['session']==session]
assert len(starts)==len(stops)==1
phase={};groups={}
for seg in d['segments']:
 assert seg['session']==session
 begin=datetime.fromisoformat(seg['start']); end=datetime.fromisoformat(seg['end']); cutoff=begin.replace(hour=8,minute=0,second=0,microsecond=0)
 sec=max(0,(min(end,cutoff)-max(begin,begin.replace(hour=6,minute=0,second=0,microsecond=0))).total_seconds())
 phase[seg['phase']]=phase.get(seg['phase'],0)+sec
 group=('local_research' if (seg['unit'].startswith(('H-20261119-03','H-20261119-04','H-20261119-07')) or 'finite-seeded-replay-formalizer' in seg['unit']) else 'general_research')if seg['phase']=='research' else seg['phase']
 groups[group]=groups.get(group,0)+sec
assert abs(sum(phase.values())-s['confirmed_work_seconds'])<.0011
out={'journal':str(J),'parent':'R-20261119-01','session':session,'actual_start':starts[0],'actual_stop':stops[0],**{k:s[k] for k in ['confirmed_work_seconds','shortfall_seconds','excluded_non_work_seconds','unconfirmed_gap_seconds','overtime_work_seconds','open_interval_unconfirmed_seconds']},'phase_seconds':phase,'allocation_seconds':groups,'distinct_mechanism_seconds':json.loads((P/'DISTINCT_MECHANISM.json').read_text())['confirmed_seconds'],'scope':'confirmed journal intervals, not pure CPU/thinking. Publication after stop is excluded. No prior-day work added.'}
(P/'FINAL_WORK_SUMMARY.json').write_text(json.dumps(out,indent=2)+'\n')
def fmt(sec):
 return f'{int(sec//60)}分{sec%60:06.3f}秒'
work=f'''実開始 **{starts[0]}**、実終了 **{stops[0]}**。confirmed_work_seconds **{s['confirmed_work_seconds']:.3f}** = **{fmt(s['confirmed_work_seconds'])}**、120分に対する不足 **{fmt(s['shortfall_seconds'])}**。待機/中断gapなし、open区間0。journal stopは期限を超過し、08:00以降 **{s['overtime_work_seconds']:.3f}秒** はconfirmed実績から除外。開始遅れを補填しない。保存準備とstopが期限に収まらず、commit/pushは未実行。\n\n確定配分: {', '.join(k+' '+fmt(v)for k,v in groups.items())}。別機構{fmt(out['distinct_mechanism_seconds'])}はgeneral内に含み、追加加算しない。正本[確定実績](data/depth_general_20261119/FINAL_WORK_SUMMARY.json)と[journal](data/daily_research/2026-11-19.json)。'''
p=Path('docs/RESEARCH_HANDOFF_2026-11-19_DAILY.md');t=p.read_text();a=t.index('<!-- FINAL_WORK_BEGIN -->');b=t.index('<!-- FINAL_WORK_END -->')
t=t[:a]+'<!-- FINAL_WORK_BEGIN -->\n'+work+'\n'+t[b:];p.write_text(t)
for card in sorted(Path('docs').glob('HYPOTHESIS_CARD_2026-11-19_*.md')):
 card.write_text(card.read_text()+f'\n## Confirmed parent journal\n\nParent R-20261119-01 stopped {stops[0]}, confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}sec. This is the single parent total, NOT additional time for this card. Waiting/gap0; overtime {s["overtime_work_seconds"]:.3f}sec excluded from confirmed time. Final phase allocations, CPU separation, evidence and next question are in [11/19 DAILY](RESEARCH_HANDOFF_2026-11-19_DAILY.md) and data/depth_general_20261119/FINAL_WORK_SUMMARY.json.\n')
print(json.dumps(out,indent=2))

p=Path('docs/CURRENT_FRONTIER.md');p.write_text(p.read_text().replace('日次研究（進行中、実績はstop後確定）','日次研究（確定、実績はDAILY/journal参照）'))
p=Path('docs/RESEARCH_GENERALIZATION_TRACKER.md');p.write_text(p.read_text()+f'\n## 2026-11-19 final parent verdict\n\n| Parent | Local | Depth-general | Consecutive no general progress | Next |\n|---|---|---|---|---|\n| R-20261119-01 | E753/E757/source-height strict reduction PAPER; no new Lean adoption | E754/E756 original-rank head-depth reserve and E752/E755 global stock boundary PAPER | 0, based on new evidence not old controls/date/local success | 30/60/10; >=25min distinct mechanism |\n\nWhole-free potential does not pay LOW free; C1 remains unproved. Old E721 all-r family is supporting control, r7/13 were NOT fresh histories. Stop-state/resource/source-scope corrections remain in DAILY. Confirmed parent {out["confirmed_work_seconds"]:.3f}s; distinct {out["distinct_mechanism_seconds"]:.6f}s is contained in that total, not added. Next main is all-R low-free minimum/return, not R4-to-R5/M5-to-M6.\n')
