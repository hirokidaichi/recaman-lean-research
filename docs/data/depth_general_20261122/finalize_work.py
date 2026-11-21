"""Finalize ONLY this real stopped journal. Post-stop publication is excluded."""
from pathlib import Path
from datetime import datetime
import json,subprocess
P=Path(__file__).resolve().parent
J=Path('docs/data/daily_research/2026-11-22.json')
session='45f3710c-fdb7-4f12-9cb5-4071951492ef'
d=json.loads(J.read_text())
s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
assert d['cursor'] is None and s['open_interval_unconfirmed_seconds']==0
assert not (P/'FINAL_WORK_SUMMARY.json').exists(),'Finalize once only'
starts=[e['at'] for e in d['events'] if e['action']=='start' and e['session']==session]
stops=[e['at'] for e in d['events'] if e['action']=='stop' and e['session']==session]
assert len(starts)==len(stops)==1 and datetime.fromisoformat(stops[0]).hour==7
groups={};late=[]
for seg in d['segments']:
 assert seg['session']==session
 begin,end=map(datetime.fromisoformat,(seg['start'],seg['end']));sec=(end-begin).total_seconds()
 key=seg['phase']
 if key=='research':
  key='local_research' if str(seg.get('unit','')).startswith(('H-20261122-04/','H-20261122-05/')) else 'general_research'
 groups[key]=groups.get(key,0)+sec
 if sec>300:late.append({'start':seg['start'],'end':seg['end'],'seconds':sec,'unit':seg.get('unit')})
assert abs(sum(groups.values())-s['confirmed_work_seconds'])<.0011
assert not s['excluded_non_work_seconds'] and s['unconfirmed_gap_seconds']==s['overtime_work_seconds']==0
out={'parent':'R-20261122-01','session':session,'journal':str(J),'actual_start':starts[0],'actual_stop':stops[0],
 'allocation_seconds':groups,'late_checkpoint_intervals':late,'local_progress':'yes E769 PAPER; adopted Lean0',
 'depth_general_progress':True,'general_stagnation_streak':0,'next_allocation':'30/60/10',
 'cpu_summary':json.loads((P/'CPU_SUMMARY.json').read_text()),'distinct_mechanism':json.loads((P/'DISTINCT_MECHANISM.json').read_text()),
 **{k:s[k] for k in ['confirmed_work_seconds','target_seconds','shortfall_seconds','excluded_non_work_seconds','unconfirmed_gap_seconds','overtime_work_seconds','open_interval_unconfirmed_seconds']},
 'scope':'Actual confirmed checked intervals, not pure thinking/CPU; no previous-day time or post-stop commit/push added. No backdated checkpoints.'}
(P/'FINAL_WORK_SUMMARY.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
fmt=lambda x:f'{int(x//60)}分{x%60:06.3f}秒'
body=f'''実開始 **{starts[0]}**、実終了 **{stops[0]}**。confirmed_work_seconds **{s['confirmed_work_seconds']:.3f}** = **{fmt(s['confirmed_work_seconds'])}**。120分への不足 **{fmt(s['shortfall_seconds'])}**。待機/中断gapなし、open区間0、超過0。開始遅れとstop後のcommit/pushを作業実績へ足さない。

確定配分: {', '.join(k+' '+fmt(v) for k,v in groups.items())}。別機構1513.545289秒はgeneral内で追加加算しない。[確定実績](data/depth_general_20261122/FINAL_WORK_SUMMARY.json) / [journal](data/daily_research/2026-11-22.json)。

5分目安を超えたcheckpoint区間は{len(late)}件、詳細はFINAL_WORK_SUMMARY参照。実作業継続を確認した区間であり、遡及checkpointや中断gapの作業復帰を作らない。journalは担当確認区間で、純CPU/純思考時間ではない。'''
p=Path('docs/RESEARCH_HANDOFF_2026-11-22_DAILY.md');t=p.read_text();a=t.index('<!-- FINAL_WORK_BEGIN -->');b=t.index('<!-- FINAL_WORK_END -->')
p.write_text(t[:a]+'<!-- FINAL_WORK_BEGIN -->\n'+body+'\n'+t[b:])
for p in sorted(Path('docs').glob('HYPOTHESIS_CARD_2026-11-22_*.md')):
 p.write_text(p.read_text()+f'\n## Confirmed shared parent journal\n\nR-20261122-01: {starts[0]} to {stops[0]}; confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}s, waiting/gap/overtime0. ONE shared parent total, not extra time per card. See DAILY/FINAL_WORK_SUMMARY for actual phase/CPU/publication.\n')
p=Path('docs/CURRENT_FRONTIER.md');p.write_text(p.read_text().replace('日次研究（実績はstop後DAILY/journalで確定）','日次研究（確定実績はDAILY/journal参照）',1).replace('確定実績/CPU/公開SHAはstop後DAILY/journal。','確定実績/CPU/公開SHAはDAILY/journal参照。',1))
p=Path('docs/RESEARCH_GENERALIZATION_TRACKER.md');p.write_text(p.read_text()+f'\nParent R-20261122-01 finalized: {starts[0]} to {stops[0]}, confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}s, waiting/gap/overtime0. Distinct1513.545289s is INSIDE the parent. Local E769 PAPER/adoptedLean0; general new evidence/streak0/next30-60-10. Post-stop publication excluded.\n')
brief=subprocess.run(['make','brief'],capture_output=True,text=True,timeout=8)
(P/'FINAL_BRIEF.log').write_text(brief.stdout+brief.stderr)
(P/'FINAL_BRIEF.json').write_text(json.dumps({'argv':['make','brief'],'exit_code':brief.returncode,'scope':'Brief refreshed after finalized journal/header wording; no Lean build or new research'},indent=2)+'\n')
assert brief.returncode==0 and '2026-11-22' in brief.stdout
print(json.dumps({k:out[k] for k in ['actual_start','actual_stop','confirmed_work_seconds','shortfall_seconds','allocation_seconds','late_checkpoint_intervals']},ensure_ascii=False,indent=2))
