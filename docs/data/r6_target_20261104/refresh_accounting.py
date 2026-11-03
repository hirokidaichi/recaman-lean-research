"""Snapshot closed journal intervals and completed validation receipts, never credit open time."""
from pathlib import Path
import json, subprocess, datetime
from zoneinfo import ZoneInfo
p=Path(__file__).parent
status=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
receipts=[]
for f in sorted(p.glob('*-result.json')):
    r=json.loads(f.read_text())
    if 'cpu_seconds' in r and 'exit_code' in r:
        receipts.append({'receipt':str(f),'cpu_seconds':r['cpu_seconds'],'exit_code':r['exit_code'],'reason':r.get('reason')})
cpu={'observed_jst':datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'mathematical_search_worker':'not started; budget 0','completed_validation_receipt_cpu_seconds':round(sum(r['cpu_seconds'] for r in receipts),6),'completed_validation_receipts':len(receipts),'receipts':receipts,'unmeasured':'ordinary tools/scripts outside these controllers; not assumed zero','contract':'per-process CPU caps; no generic process-tree cumulative cap or OS address-space cap claimed'}
(p/'CPU_ACCOUNTING.json').write_text(json.dumps(cpu,indent=2)+'\n')
(p/'WORK_ACCOUNTING_LATEST.json').write_text(json.dumps(status,indent=2)+'\n')
print(json.dumps({'confirmed_work_seconds':status['confirmed_work_seconds'],'open_unconfirmed':status['open_interval_unconfirmed_seconds'],'validation_cpu_seconds':cpu['completed_validation_receipt_cpu_seconds'],'receipts':len(receipts)}))
