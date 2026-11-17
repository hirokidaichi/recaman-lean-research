"""Post-stop bookkeeping only. Reads confirmed journal, never creates time."""
from pathlib import Path
from datetime import datetime
import json,subprocess
P=Path(__file__).resolve().parent
J=Path('docs/data/daily_research/2026-11-18.json')
d=json.loads(J.read_text())
s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
assert d['cursor'] is None, 'journal must be stopped before final totals'
assert s['open_interval_unconfirmed_seconds']==0
session='6959042b-280b-4f0b-9c83-25040ec43614'
starts=[e['at']for e in d['events']if e['action']=='start' and e['session']==session]
stops=[e['at']for e in d['events']if e['action']=='stop' and e['session']==session]
assert len(starts)==len(stops)==1
phase={};groups={}
for seg in d['segments']:
 assert seg['session']==session
 sec=(datetime.fromisoformat(seg['end'])-datetime.fromisoformat(seg['start'])).total_seconds()
 phase[seg['phase']]=phase.get(seg['phase'],0)+sec
 group=('local_research' if seg['unit'].startswith('H-20261118-03') else 'general_research')if seg['phase']=='research' else seg['phase']
 groups[group]=groups.get(group,0)+sec
assert abs(sum(phase.values())-s['confirmed_work_seconds'])<.0011
out={'journal':str(J),'parent':'R-20261118-01','session':session,'actual_start':starts[0],'actual_stop':stops[0],**{k:s[k] for k in ['confirmed_work_seconds','shortfall_seconds','excluded_non_work_seconds','unconfirmed_gap_seconds','overtime_work_seconds','open_interval_unconfirmed_seconds']},'phase_seconds':phase,'allocation_seconds':groups,'distinct_mechanism_seconds':json.loads((P/'DISTINCT_MECHANISM.json').read_text())['conservative_seconds'],'scope':'confirmed journal intervals, not pure CPU/thinking. Publication after stop is excluded. No prior-day work added.'}
(P/'FINAL_WORK_SUMMARY.json').write_text(json.dumps(out,indent=2)+'\n')
def fmt(sec):
 return f'{int(sec//60)}分{sec%60:06.3f}秒'
work=f'''実開始 **{starts[0]}**、実終了 **{stops[0]}**。confirmed_work_seconds **{s['confirmed_work_seconds']:.3f}** = **{fmt(s['confirmed_work_seconds'])}**、120分に対する不足 **{fmt(s['shortfall_seconds'])}**。待機/中断gapなし、open区間0、overtime0。開始遅れとstop後の公開余白を補填せず、公開操作を研究実績へ戻さない。\n\n確定配分: {', '.join(k+' '+fmt(v)for k,v in groups.items())}。別機構{fmt(out['distinct_mechanism_seconds'])}はgeneral内に含み、追加加算しない。正本[確定実績](data/depth_general_20261118/FINAL_WORK_SUMMARY.json)と[journal](data/daily_research/2026-11-18.json)。'''
p=Path('docs/RESEARCH_HANDOFF_2026-11-18_DAILY.md');t=p.read_text();a=t.index('<!-- FINAL_WORK_BEGIN -->');b=t.index('<!-- FINAL_WORK_END -->')
t=t[:a]+'<!-- FINAL_WORK_BEGIN -->\n'+work+'\n'+t[b:];p.write_text(t)
for card in sorted(Path('docs').glob('HYPOTHESIS_CARD_2026-11-18_*.md')):
 card.write_text(card.read_text()+f'\n## Confirmed parent journal\n\nParent R-20261118-01 stopped {stops[0]}, confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}sec. This is the single parent total, NOT additional time for this card. Waiting/gap/overtime0. Final phase allocations, CPU separation, evidence and next question are in [11/18 DAILY](RESEARCH_HANDOFF_2026-11-18_DAILY.md) and data/depth_general_20261118/FINAL_WORK_SUMMARY.json.\n')
print(json.dumps(out,indent=2))
