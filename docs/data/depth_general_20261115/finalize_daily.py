"""Close the actual journal once, then save only its confirmed values."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib, json, subprocess, sys

ROOT=Path(__file__).resolve().parents[3]
PACKET=ROOT/'docs/data/depth_general_20261115'
JOURNAL=ROOT/'docs/data/daily_research/2026-11-15.json'
SESSION='b62344cd-d73e-435a-94aa-0274cd820461'
now=datetime.now(ZoneInfo('Asia/Tokyo'))
if sys.argv[1:]!=['--stop-and-save'] or now.date().isoformat()!='2026-11-15' or now.hour!=7 or now.minute<45:
    raise RuntimeError('explicit current-day final save in publication phase required')
before=json.loads(JOURNAL.read_text())
if not before.get('cursor') or before['cursor']['session']!=SESSION:
    raise RuntimeError('active owned journal required; never add a duplicate stop')
result=json.loads(subprocess.check_output([
    'python3','scripts/research_session.py','stop','--session',SESSION,'--note',
    'Research and independent audit complete; all mathematical workers stopped, adopted Lean/fullcheck passed. Close confirmed handoff before final snapshot publication; do not credit later save/push time.'
],cwd=ROOT,text=True))
assert result['status']=='stop' and result['cursor'] is None and result['open_interval_unconfirmed_seconds']==0
j=json.loads(JOURNAL.read_text())
phases={};local=0.;general=0.
for row in j['segments']:
    sec=(datetime.fromisoformat(row['end'])-datetime.fromisoformat(row['start'])).total_seconds()
    phases[row['phase']]=phases.get(row['phase'],0)+sec
    if row['phase']=='research':
        if row['unit'].startswith('H-20261115-06/'):local+=sec
        else:general+=sec
assert abs(sum(phases.values())-result['confirmed_work_seconds'])<.001
start=next(e['at'] for e in j['events'] if e['action']=='start' and e['session']==SESSION)
end=j['events'][-1]['at']
phase_data={'phase_seconds':{k:round(v,6) for k,v in phases.items()},
    'research_local_seconds':round(local,6),'research_general_seconds':round(general,6),
    'independent_adaptive_operation_seconds':1775.048789,
    'independent_operation_scope':'inside general research, not an additional time credit',
    'nominal_plan_minutes':{'setup':10,'local':30,'general':60,'audit':10,'handoff':10},
    'reallocation':'saved setup and early local completion paid general construction, required semantic audit and final handoff; no future/previous-day credit'}
(PACKET/'FINAL_PHASE_TOTALS.json').write_text(json.dumps(phase_data,ensure_ascii=False,indent=2)+'\n')
summary=dict(result,session=SESSION,parent_cycle='R-20261115-01',actual_start_jst=start,actual_end_jst=end,
    journal_sha256=hashlib.sha256(JOURNAL.read_bytes()).hexdigest(),phase_totals=phase_data,
    publication_after_stop_excluded=True,scope='confirmed journal intervals, not pure CPU/thought measurement')
(PACKET/'FINAL_WORK_SUMMARY.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
def duration(s):
    ms=round(s*1000);minutes,rest=divmod(ms,60000)
    return str(minutes)+'分'+format(rest/1000,'06.3f')+'秒'
text=('実setup開始 **'+start+'**、実終了 **'+end+'**。confirmed_work_seconds **'+str(result['confirmed_work_seconds'])+
    '** = **'+duration(result['confirmed_work_seconds'])+'**、120分に対する不足 **'+duration(result['shortfall_seconds'])+
    '**。待機/中断gapなし、open区間0、overtime0。journalは確認済み作業区間であり純CPU/純思考時間ではない。'
    '開始遅れとstop後の確定保存・公開余白は遡及補填せず、公開操作を研究実績へ戻さない。\n\n'
    '確定phase: setup '+duration(phases.get('setup',0))+'、local research '+duration(local)+
    '、general research '+duration(general)+'、audit '+duration(phases.get('audit',0))+'、handoff '+duration(phases.get('handoff',0))+
    '。別機構29分35.049秒はgeneral内に含み、親とunitを二重計上しない。')
daily=ROOT/'docs/RESEARCH_HANDOFF_2026-11-15_DAILY.md'
s=daily.read_text();assert s.count('@@FINAL_WORK@@')==1
s=s.replace('@@FINAL_WORK@@',text).replace('（最終保存前、journal未確定）','（journal stop後の確定記録）')
daily.write_text(s)
frontier=ROOT/'docs/CURRENT_FRONTIER.md';s=frontier.read_text().replace('最終更新: 2026-11-15（研究中）。','最終更新: 2026-11-15（研究・検証終了、journal確定）。');frontier.write_text(s)
tracker=ROOT/'docs/RESEARCH_GENERALIZATION_TRACKER.md'
s=tracker.read_text().replace('全研究作業は継続中のため、この数学的判定を120分完了や終了時刻の先取りにしない。',
    '最終workはstop後journal/11月15日DAILYの確定値を参照。120分完了へ切り上げず、不足を明記した。')
tracker.write_text(s)
with (PACKET/'brief-final.log').open('w') as log:
    subprocess.run(['make','brief'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,check=True)
print(json.dumps({'start':start,'end':end,'confirmed_work_seconds':result['confirmed_work_seconds'],
    'work':duration(result['confirmed_work_seconds']),'shortfall':duration(result['shortfall_seconds']),
    'phases':phase_data,'next_action':'publish exact finalized owned paths; no further journal start/stop'},ensure_ascii=False,indent=2))
