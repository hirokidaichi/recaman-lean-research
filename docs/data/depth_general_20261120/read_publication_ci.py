"""Read main-push Actions for the exact published snapshot; bounded read only."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import json, re, subprocess

P = Path(__file__).resolve().parent / 'publication_snapshot'
receipt = P / 'PUBLICATION_RECEIPT.json'
r = json.loads(receipt.read_text())
sha = r['research_snapshot_sha']
assert re.fullmatch('[0-9a-f]{40}', sha)
now = lambda: datetime.now(ZoneInfo('Asia/Tokyo'))
assert now().hour == 7 and now().minute >= 45
argv = ['gh', 'api', 'repos/hirokidaichi/recaman-lean-research/actions/runs?head_sha=' + sha + '&per_page=100',
        '--jq', '.workflow_runs | map({id,name,head_sha,status,conclusion,html_url,event})']
result = {'snapshot_sha': sha, 'observed_jst': now().isoformat(), 'scope': 'Exact main-push commit, first100 Actions, not PR-only connector results'}
try:
    proc = subprocess.run(argv, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=10)
    result['read_exit'] = proc.returncode
    if proc.returncode == 0:
        runs = json.loads(proc.stdout)
        assert all(x['head_sha'] == sha for x in runs)
        result['runs'] = runs
        state = ('not_observed_yet' if not runs else
                 'completed_success' if all(x['status'] == 'completed' and x['conclusion'] == 'success' for x in runs) else
                 'failed_or_cancelled' if any(x['status'] == 'completed' and x['conclusion'] not in ['success', 'skipped', 'neutral'] for x in runs) else
                 'pending_or_in_progress')
    else:
        result['error'] = proc.stderr[:1000]
        state = 'unconfirmed_read_failed'
except subprocess.TimeoutExpired:
    state = 'unconfirmed_read_timeout'
result['observed_state'] = state
r['hosted_ci'] = state + ' for research snapshot; final receipt commit CI separately unconfirmed'
(P / 'CI_SNAPSHOT.json').write_text(json.dumps(result, indent=2) + '\n')
receipt.write_text(json.dumps(r, indent=2) + '\n')
print(json.dumps(result, indent=2))
