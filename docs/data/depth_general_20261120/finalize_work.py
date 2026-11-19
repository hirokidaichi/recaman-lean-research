"""Finalize this session's stopped journal; never invent or backfill time."""
from pathlib import Path
from datetime import datetime
import json, subprocess

P = Path(__file__).resolve().parent
J = Path('docs/data/daily_research/2026-11-20.json')
session = '0abc5a83-4549-40cf-8910-3e0ca8d68bfc'
d = json.loads(J.read_text())
s = json.loads(subprocess.check_output(['python3', 'scripts/research_session.py', 'status'], text=True))
assert d['cursor'] is None and s['open_interval_unconfirmed_seconds'] == 0
assert not (P / 'FINAL_WORK_SUMMARY.json').exists(), 'Finalize once only'
starts = [e['at'] for e in d['events'] if e['action'] == 'start' and e['session'] == session]
stops = [e['at'] for e in d['events'] if e['action'] == 'stop' and e['session'] == session]
assert len(starts) == len(stops) == 1
assert datetime.fromisoformat(stops[0]).hour == 7, 'Do not publish overtime as confirmed work'
groups = {}
for seg in d['segments']:
    assert seg['session'] == session
    begin, end = map(datetime.fromisoformat, (seg['start'], seg['end']))
    sec = (end - begin).total_seconds()
    key = seg['phase']
    if key == 'research':
        key = 'local_research' if seg['unit'].startswith('H-20261120-03') else 'general_research'
    groups[key] = groups.get(key, 0) + sec
assert abs(sum(groups.values()) - s['confirmed_work_seconds']) < .0011
out = {'parent': 'R-20261120-01', 'session': session, 'journal': str(J),
       'actual_start': starts[0], 'actual_stop': stops[0], 'allocation_seconds': groups,
       **{k: s[k] for k in ['confirmed_work_seconds', 'shortfall_seconds', 'excluded_non_work_seconds',
                             'unconfirmed_gap_seconds', 'overtime_work_seconds', 'open_interval_unconfirmed_seconds']},
       'distinct_mechanism': json.loads((P / 'DISTINCT_MECHANISM.json').read_text()),
       'scope': 'Confirmed checked intervals, not pure thinking/CPU; post-stop publication excluded; no previous-day time added.'}
(P / 'FINAL_WORK_SUMMARY.json').write_text(json.dumps(out, indent=2) + '\n')
def fmt(sec):
    return f'{int(sec // 60)}分{sec % 60:06.3f}秒'
body = f'''実開始 **{starts[0]}**、実終了 **{stops[0]}**。confirmed_work_seconds **{s['confirmed_work_seconds']:.3f}** = **{fmt(s['confirmed_work_seconds'])}**。120分への不足 **{fmt(s['shortfall_seconds'])}**。待機/中断gapなし、open区間0、超過0。開始遅れとstop後のcommit/pushを作業実績へ足さない。

確定配分: {', '.join(k + ' ' + fmt(v) for k, v in groups.items())}。別機構の時間はgeneral内に含み追加加算しない。[確定実績](data/depth_general_20261120/FINAL_WORK_SUMMARY.json) / [journal](data/daily_research/2026-11-20.json)。'''
p = Path('docs/RESEARCH_HANDOFF_2026-11-20_DAILY.md')
t = p.read_text(); a = t.index('<!-- FINAL_WORK_BEGIN -->'); b = t.index('<!-- FINAL_WORK_END -->')
p.write_text(t[:a] + '<!-- FINAL_WORK_BEGIN -->\n' + body + '\n' + t[b:])
for p in sorted(Path('docs').glob('HYPOTHESIS_CARD_2026-11-20_*.md')):
    p.write_text(p.read_text() + f'\n## Confirmed parent journal\n\nR-20261120-01: {starts[0]} to {stops[0]}; confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}s, waiting/gap/overtime0. This is ONE shared parent total, not additional card time. See [DAILY](RESEARCH_HANDOFF_2026-11-20_DAILY.md) and packet FINAL_WORK_SUMMARY.json for allocation/CPU/evidence/next question.\n')
p = Path('docs/CURRENT_FRONTIER.md')
p.write_text(p.read_text().replace('日次研究（実績はstop後DAILY/journalで確定）', '日次研究（確定実績はDAILY/journal参照）'))
p = Path('docs/RESEARCH_GENERALIZATION_TRACKER.md')
p.write_text(p.read_text() + f'\nParent R-20261120-01 finalized: actual {starts[0]} to {stops[0]}, confirmed_work_seconds={s["confirmed_work_seconds"]:.3f}, shortfall={s["shortfall_seconds"]:.3f}s, waiting/gap/overtime0. Distinct1720.403768s is contained in the parent, not added. Local0/general new evidence/streak0/next30-60-10 unchanged. Publication after stop is excluded.\n')
print(json.dumps(out, indent=2))
