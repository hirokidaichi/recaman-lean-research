import subprocess,json,time
from pathlib import Path
xs=sorted(set(subprocess.check_output(['git','ls-files','--others','--exclude-standard','Recaman'],text=True).splitlines()+subprocess.check_output(['git','diff','--name-only','--diff-filter=A','f06d97ea35ffa528a383f1edd37ecd27f2d6bf35','--','Recaman'],text=True).splitlines()))
rows=[]
for x in xs:
 if x.endswith('.lean'):
  p=subprocess.run(['python3','scripts/harness_gate.py','--lint-module',x],text=True,capture_output=True)
  rows.append({'path':x,'exit_code':p.returncode,'output':p.stdout+p.stderr})
Path('docs/data/family_collision_20261105/NEW_MODULE_LINT.json').write_text(json.dumps(rows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'count':len(rows),'nonzero':[r for r in rows if r['exit_code']],'warnings':[r for r in rows if 'warn' in r['output'].lower()]},ensure_ascii=False))
raise SystemExit(any(r['exit_code'] for r in rows))
