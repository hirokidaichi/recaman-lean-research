"""Save only closed-journal accounting, then hash the final evidence packet."""
from collections import defaultdict
from datetime import datetime, timedelta
import hashlib
import json
from pathlib import Path
import re
import subprocess

base = Path(__file__).resolve().parent
root = base.parents[2]
journal = root / 'docs/data/daily_research/2026-10-23.json'
daily = root / 'docs/RESEARCH_HANDOFF_2026-10-23_DAILY.md'
log = json.loads(journal.read_text())
assert log['cursor'] is None, 'stop the actual journal first; open time cannot be credited'
assert log['events'][-1]['action'] == 'stop'
status = json.loads(subprocess.check_output(
    ['python3', 'scripts/research_session.py', 'status', '--date', '2026-10-23'], cwd=root, text=True))
assert status['open_interval_unconfirmed_seconds'] == 0
assert status['overtime_work_seconds'] == 0
assert len({e['session'] for e in log['events']}) == 1
stats = defaultdict(float)
units = {}
for seg in log['segments']:
    seconds = (datetime.fromisoformat(seg['end']) - datetime.fromisoformat(seg['start'])).total_seconds()
    group = seg['phase']
    if group == 'research':
        group = 'exploitation' if seg['unit'].startswith(('H-20261023-01/', 'H-20261023-02/')) else 'exploration'
    stats[group] += seconds
    unit = units.setdefault(seg['unit'], dict(start=seg['start'], end=seg['end'], seconds=0.0))
    unit['end'] = seg['end']
    unit['seconds'] += seconds
start, end = log['events'][0]['at'], log['events'][-1]['at']
window_start = datetime.fromisoformat(start).replace(hour=6, minute=0, second=0, microsecond=0)
startup = (datetime.fromisoformat(start) - window_start).total_seconds()
confirmed = status['confirmed_work_seconds']
assert abs(sum(stats.values()) - confirmed) < .002
minutes, seconds = divmod(confirmed, 60)
rows = ['| 区分 | 予定（分） | journal実績（秒） |', '| --- | ---: | ---: |']
for key, name, planned in [('setup', '開始確認', 10), ('exploitation', 'C1活用 H01/H02', 60),
                           ('exploration', '局所探索 H03/H05（子H04/H06含む）', 30),
                           ('audit', '別pass監査', 10), ('handoff', '引き継ぎ', 10)]:
    rows.append(f'| {name} | {planned} | {stats[key]:.3f} |')
timeline = ['| 実unit | JST開始〜終了 | 秒 |', '| --- | --- | ---: |']
for name, value in units.items():
    timeline.append(f"| {name} | {value['start'][11:19]}〜{value['end'][11:19]} | {value['seconds']:.3f} |")
text = '\n'.join([
    f'- 実開始: `{start}`。実終了: `{end}`。',
    f'- **confirmed_work_seconds={confirmed:.3f}（{int(minutes)}分{seconds:.3f}秒）**。',
    f'- 120分への不足: **{status["shortfall_seconds"]:.3f}秒**。開始未記録{startup:.3f}秒を加算しない。',
    f'- 待機/blocked: {json.dumps(status["excluded_non_work_seconds"], ensure_ascii=False)}（いずれも0）。中断gap: {status["unconfirmed_gap_seconds"]:.3f}秒。open: 0。時間外: 0。',
    '- 前日の18分51秒・追加98分13秒を本日の実績へ加えていない。',
    '- journalは担当が確認した作業区間（資料読取・証明作成・計算監視・検証・記録を含む）。純思考時間やCPU時間の計測ではない。',
    '', *rows, '', *timeline, '',
    '- [最終status](data/c1_depth_20261023/final-journal-status.json)と[packet manifest](data/c1_depth_20261023/final-packet-manifest.json)を保存。',
    '- stop後のこの集計・manifest書込はjournalへ遡及加算していない。',
])
old = daily.read_text()
new, count = re.subn(r'(?s)(<!-- FINAL_METRICS_START -->).*?(<!-- FINAL_METRICS_END -->)',
                     lambda m: m[1] + '\n' + text + '\n' + m[2], old)
assert count == 1
(base / 'final-journal-status.json').write_text(json.dumps(status, ensure_ascii=False, indent=2) + '\n')
(base / 'final-allocation.json').write_text(json.dumps(dict(start=start, end=end, phase_seconds=stats, unit_intervals=units,
    startup_uncredited_seconds=startup, confirmed_work_seconds=confirmed,
    shortfall_seconds=status['shortfall_seconds']), ensure_ascii=False, indent=2) + '\n')
daily.write_text(new)
files = []
manifest_path = base / 'final-packet-manifest.json'
for p in sorted(base.rglob('*')):
    if not p.is_file() or p == manifest_path or '__pycache__' in p.parts:
        continue
    data = p.read_bytes()
    files.append(dict(path=str(p.relative_to(root)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
external = []
for p in [journal, daily]:
    data = p.read_bytes()
    external.append(dict(path=str(p.relative_to(root)), bytes=len(data), sha256=hashlib.sha256(data).hexdigest()))
manifest_path.write_text(json.dumps(dict(frozen_at=datetime.now().astimezone().isoformat(),
    scope='closed daily journal and final handoff plus evidence packet; manifest excludes itself and pycache',
    packet_files=files, external_files=external), ensure_ascii=False, indent=2) + '\n')
print(json.dumps(dict(confirmed_work_seconds=confirmed, shortfall_seconds=status['shortfall_seconds'],
                     packet_files=len(files), ended_jst=end), ensure_ascii=False))
