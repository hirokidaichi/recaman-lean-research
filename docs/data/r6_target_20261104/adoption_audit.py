from pathlib import Path
import subprocess,json,hashlib
p=Path('docs/data/r6_target_20261104')
changed=subprocess.check_output(['git','ls-files','--others','--exclude-standard','Recaman'],text=True).splitlines()
changed+=subprocess.check_output(['git','diff','--name-only','--','Recaman'],text=True).splitlines()
mods=sorted(set(x for x in changed if x.endswith('.lean') and x!='Recaman/Audit.lean'))
receipts=[]
for f in p.glob('*-result.json'):
 d=json.loads(f.read_text())
 if d.get('exit_code')==0 and '-M512' in d.get('argv',[]):receipts.append((f.name,d))
rows=[];fail=[]
for f in mods:
 h=hashlib.sha256(Path(f).read_bytes()).hexdigest()
 r=[n for n,d in receipts if d.get('source_sha256',{}).get(f)==h]
 out=subprocess.run(['python3','scripts/harness_gate.py','--lint-module',f],text=True,capture_output=True)
 rows.append(dict(path=f,sha256=h,individual_M512_receipts=r,lint_exit=out.returncode,lint_stdout=out.stdout,lint_stderr=out.stderr))
 expected_support = f in ['Recaman/MassTwoSmallHeadKey.lean','Recaman/UnitTargetSmallHeadKey.lean'] and 'would fail G3 if registered alone' in out.stdout
 if expected_support: rows[-1]['lint_disposition']='pure arithmetic support only; not independently registered; no dummy wrapper or gate exemption'
 if not r or (out.returncode and not expected_support):fail.append(f)
(p/'ADOPTION_AUDIT.json').write_text(json.dumps({'modules':rows,'module_count':len(mods),'failures':fail,'scope':'current source bytes must match completed -M512 individual validation; all source tree hashes archived in receipts; pure arithmetic lint warnings are not standalone evidence'},indent=2)+'\n')
print(json.dumps({'module_count':len(mods),'failures':fail,'lint_warnings':[{ 'path':r['path'],'stdout':r['lint_stdout']} for r in rows if 'warning' in r['lint_stdout'].lower()]},ensure_ascii=False))
raise SystemExit(bool(fail))
