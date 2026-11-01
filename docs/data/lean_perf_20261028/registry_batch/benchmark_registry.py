import json,subprocess,time,sys,hashlib
from pathlib import Path
p=Path(__file__).parent;label=sys.argv[1];rows=[]
inputs=['docs/EVIDENCE_REGISTRY.tsv','docs/CURRENT_FRONTIER.md','Recaman/Audit.lean','scripts/harness_gate.py']
for i in range(3):
 t=time.monotonic();r=subprocess.run(['bash','scripts/check_research_registry.sh'],capture_output=True,text=True,timeout=30);d=time.monotonic()-t
 rows.append({'run':i+1,'wall_seconds':d,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
 print(label,i+1,round(d,3),r.returncode,flush=True)
 if r.returncode:break
out={'label':label,'script_sha256':hashlib.sha256(Path('scripts/check_research_registry.sh').read_bytes()).hexdigest(),'input_sha256':{f:hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in inputs},'runs':rows}
(p/(label+'.json')).write_text(json.dumps(out,indent=2)+'\n')
