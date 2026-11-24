"""Only after the actual journal stop; publication/after-stop admin is not credited."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json,subprocess
P=Path(__file__).resolve().parent;J=Path('docs/data/daily_research/2026-11-25.json')
session='b0dc7157-d226-442b-9e58-e4de75cf1b6a'
d=json.loads(J.read_text());s=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
assert d['cursor']is None and s['open_interval_unconfirmed_seconds']==0
assert not(P/'FINAL_WORK_SUMMARY.json').exists(),'Finalize once after REAL stop'
starts=[e['at']for e in d['events']if e['action']=='start'and e['session']==session]
stops=[e['at']for e in d['events']if e['action']=='stop'and e['session']==session]
assert len(starts)==len(stops)==1 and datetime.fromisoformat(stops[0]).hour==7
groups={};late=[];work_starts=[]
for seg in d['segments']:
    assert seg['session']==session
    begin,end=map(datetime.fromisoformat,(seg['start'],seg['end']));seconds=(end-begin).total_seconds();phase=seg['phase']
    if phase in ['waiting','blocked']:continue
    work_starts.append(seg['start']);key=phase
    if phase=='research':key='local_research'if str(seg.get('unit','')).startswith(('H-20261125-03/','H-20261125-07/'))else'general_research'
    groups[key]=groups.get(key,0)+seconds
    if seconds>300:late.append({'start':seg['start'],'end':seg['end'],'seconds':seconds,'unit':seg.get('unit')})
assert abs(sum(groups.values())-s['confirmed_work_seconds'])<.0011
assert s['unconfirmed_gap_seconds']==s['overtime_work_seconds']==0
assert abs(s['excluded_non_work_seconds'].get('waiting',0)-13.202)<.0011
out={'parent':'R-20261125-01','session':session,'journal':str(J),'actual_run_start':starts[0],'actual_work_start':min(work_starts),'actual_stop':stops[0],
     'allocation_seconds':groups,'late_checkpoint_intervals':late,'local_progress':'yes restricted E776 and paid-prefix E780; new Lean0',
     'depth_general_progress':True,'general_progress_evidence':['E775 all-profile barrier','E778 all-word complete-seed producer','E779 all-r executed-past no-go'],
     'general_stagnation_streak':0,'prior_completed_streak':0,'Nov24':'missing/unevaluated, not a completed parent','next_allocation':'30/60/10, distinct mechanism>=25min',
     'cpu_summary':json.loads((P/'CPU_SUMMARY.json').read_text()),'distinct_mechanism':json.loads((P/'H02_CONTINUATION_GATE.json').read_text()),
     **{k:s[k]for k in ['confirmed_work_seconds','target_seconds','shortfall_seconds','excluded_non_work_seconds','unconfirmed_gap_seconds','overtime_work_seconds','open_interval_unconfirmed_seconds']},
     'scope':'Checked actual intervals, not pure CPU/thinking. Waiting/old days/post-stop publication excluded; no backfill. One parent only.'}
fmt=lambda x:f'{int(x//60)}分{x%60:06.3f}秒'
body=f'''実run開始 **{starts[0]}**、実作業開始 **{out['actual_work_start']}**、実終了 **{stops[0]}**。confirmed_work_seconds **{s['confirmed_work_seconds']:.3f}** = **{fmt(s['confirmed_work_seconds'])}**。120分への不足 **{fmt(s['shortfall_seconds'])}**。waiting **13.202秒** 除外、gap/open/超過0。開始遅れとstop後の保存・commit/pushを実績へ足さない。

確定配分: {', '.join(k+' '+fmt(v)for k,v in groups.items())}。独立height機構1517.572752秒は親内（H03冒頭監査含む）で追加加算なし。nominal local30分に対する未使用分は新一般機構・必要監査へ移した。予定と実績を区別する。

5分目安を超えたcheckpoint区間{len(late)}件は確定summaryへ保存。実作業継続を確認した区間であり、遡及checkpointやgapの作業復帰を作らない。[確定実績](data/depth_general_20261125/FINAL_WORK_SUMMARY.json) / [journal](data/daily_research/2026-11-25.json)。'''
daily=Path('docs/RESEARCH_HANDOFF_2026-11-25_DAILY.md');text=daily.read_text();a=text.index('<!-- FINAL_WORK_BEGIN -->');b=text.index('<!-- FINAL_WORK_END -->')
daily.write_text(text[:a]+'<!-- FINAL_WORK_BEGIN -->\n'+body+'\n'+text[b:])
for q in Path('docs').glob('HYPOTHESIS_CARD_2026-11-25_*.md'):
    q.write_text(q.read_text()+f'\n## Confirmed shared parent journal\nR-20261125-01: actual work{out["actual_work_start"]} to{stops[0]}, confirmed{s["confirmed_work_seconds"]:.3f}s, shortfall{s["shortfall_seconds"]:.3f}s, waiting13.202s excluded, gap/overtime0. ONE shared parent total, not extra per card. See DAILY/FINAL_WORK_SUMMARY.\n')
front=Path('docs/CURRENT_FRONTIER.md');text=front.read_text().replace('日次研究・検証進行中（確定実績はstop後DAILY/journal）','日次研究（確定実績はDAILY/journal参照）',1)
text=text.replace('親R-20261125-01進行中、確定phase/CPU/不足/公開SHAはstop後DAILY。','親R-20261125-01確定、phase/CPU/不足/公開SHAはDAILY/journal参照。',1)
text=text.replace('今回general新証拠はE775/E778/E779、localと独立に最終判定する。','今回general新証拠E775/E778/E779により連続進展なし0、localとは独立に判定。',1);front.write_text(text)
tracker=Path('docs/RESEARCH_GENERALIZATION_TRACKER.md');tracker.write_text(tracker.read_text()+f'\nParent R-20261125-01 finalized: actual work{out["actual_work_start"]} to{stops[0]}, confirmed{s["confirmed_work_seconds"]:.3f}s/shortfall{s["shortfall_seconds"]:.3f}s, waiting13.202s excluded/gap0/overtime0. Local E776/E780 PAPER, newLean0; general E775/E778/E779 NEW evidence/streak0/next30-60-10. Nov24 unevaluated, no date reset. Distinct1517.572752s INSIDE parent, post-stop publication excluded.\n')
brief=subprocess.run(['make','brief'],capture_output=True,text=True,timeout=8)
(P/'FINAL_BRIEF.log').write_text(brief.stdout+brief.stderr);(P/'FINAL_BRIEF.json').write_text(json.dumps({'argv':['make','brief'],'exit_code':brief.returncode,'scope':'Refresh after REAL stop wording/journal, no math/Lean rerun'},indent=2)+'\n')
assert brief.returncode==0 and '2026-11-25'in brief.stdout
(P/'FINAL_WORK_SUMMARY.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:out[k]for k in ['actual_run_start','actual_work_start','actual_stop','confirmed_work_seconds','shortfall_seconds','allocation_seconds','late_checkpoint_intervals']},ensure_ascii=False,indent=2))
