"""Bookkeeping only: read confirmed journal segments, never edit the journal or credit open time."""
from pathlib import Path
import collections,datetime,json,re,subprocess
p=Path(__file__).parent
status=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
j=json.loads(Path(status['journal']).read_text());phase=collections.defaultdict(float);units=collections.defaultdict(float)
for s in j['segments']:
 sec=(datetime.datetime.fromisoformat(s['end'])-datetime.datetime.fromisoformat(s['start'])).total_seconds()
 phase[s['phase']]+=sec;units[s['unit']]+=sec
exp=0.;expl=0.
for s in j['segments']:
 if s['phase']!='research':continue
 sec=(datetime.datetime.fromisoformat(s['end'])-datetime.datetime.fromisoformat(s['start'])).total_seconds()
 local=any(x in s['unit'] for x in ['/H02-','/H07-exploration','/H09-','/H10-','/H11-','/H12-'])
 if local:expl+=sec
 else:exp+=sec
start=next(e['at'] for e in j['events'] if e['action']=='start');stops=[e['at'] for e in j['events'] if e['action']=='stop'];end=stops[-1] if stops and status['cursor'] is None else None
out=dict(status,actual_start=start,actual_end=end,planned_minutes={'setup':10,'exploitation':60,'exploration':30,'audit':10,'handoff':10},phase_seconds=dict(phase),unit_seconds=dict(units),research_allocation_seconds={'exploitation':exp,'exploration':expl},accounting_scope='confirmed wall intervals; no double parent costs, no open/gap/CPU credit')
(p/'ACCOUNTING_FINAL.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
def fmt(x):
 m=int(x//60);s=x-60*m;return f'{m}分{s:.3f}秒'
lines=[f"実開始 {start}、実終了 {end or '未確定（session継続中）'}。confirmed_work_seconds={status['confirmed_work_seconds']:.3f}、確認済み作業 **{fmt(status['confirmed_work_seconds'])}**、120分に対する不足 **{fmt(status['shortfall_seconds'])}**。",f"待機/blocked除外={json.dumps(status['excluded_non_work_seconds'],ensure_ascii=False)}、未確認gap={status['unconfirmed_gap_seconds']}秒。open区間={status['open_interval_unconfirmed_seconds']}秒は加算しない。",'実績内訳（確認区間のみ）: '+', '.join(f'{k}={fmt(v)}' for k,v in phase.items())+'。',f"research内の配分: 活用{fmt(exp)} / 局所探索{fmt(expl)}。監査/記録超過は研究時間から差し引き、親と子unitは重ねて足さない。"]
f=Path('docs/RESEARCH_HANDOFF_2026-11-01_DAILY.md');s=f.read_text();s=re.sub(r'<!-- SESSION_METRICS_BEGIN -->.*?<!-- SESSION_METRICS_END -->','<!-- SESSION_METRICS_BEGIN -->\n'+'\n\n'.join(lines)+'\n<!-- SESSION_METRICS_END -->',s,flags=re.S);f.write_text(s)
print(json.dumps({k:out[k] for k in ['actual_start','actual_end','confirmed_work_seconds','shortfall_seconds','cursor']},ensure_ascii=False))
