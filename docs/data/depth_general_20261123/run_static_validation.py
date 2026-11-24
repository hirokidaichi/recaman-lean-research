"""Bounded static validation, separate from mathematical-worker/Lean evidence."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import sys,json,subprocess,signal
P=Path(__file__).resolve().parent
tags={'architecture':['bash','scripts/check_module_architecture.sh'],'registry':['bash','scripts/check_research_registry.sh'],'manifest':['python3','viewer/gen_manifest.py','--check'],'brief':['make','brief']}
tag=sys.argv[1];argv=tags[tag]
proc=subprocess.Popen(argv,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,start_new_session=True)
try:out,_=proc.communicate(timeout=30)
except subprocess.TimeoutExpired:
 signal.signal(signal.SIGTERM,signal.SIG_DFL);import os;os.killpg(proc.pid,signal.SIGKILL);out,_=proc.communicate();out+='\nOwn static validation timeout\n'
(P/f'validation-{tag}.log').write_text(out)
receipt={'at':datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'argv':argv,'exit_code':proc.returncode,'scope':'static/tool validation, no new Lean build or hosted CI; not mathematical CPU'}
(P/f'validation-{tag}.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));print(out[-1200:]);raise SystemExit(proc.returncode)
