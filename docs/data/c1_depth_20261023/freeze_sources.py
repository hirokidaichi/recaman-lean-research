"""Freeze proof sources (including untracked modules) and verify regenerated data."""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

base=Path(__file__).resolve().parent.relative_to(Path.cwd().resolve())
dest=base/'source_snapshot'
files=[Path('Recaman.lean'),Path('Makefile'),Path('lakefile.toml'),Path('lean-toolchain')]
files+=list(Path('Recaman').glob('*.lean'))+list(Path('scripts').glob('*.py'))+list(Path('scripts').glob('*.sh'))
files+=[Path('docs')/n for n in ['EVIDENCE_REGISTRY.tsv','PROTECTED_CLAIMS.tsv','MODULE_IMPORT_CONTRACTS.tsv','CURRENT_FRONTIER.md']]
files+=list(Path('docs/statement_audits').glob('*.md'))
files+=[base/n for n in ['checker_prefix.txt','q_checker_prefix.txt','certificate.json','q-certificate.json','generate_lean_data.py','generate_q_lean.py']]
if Path('lake-manifest.json').exists():files.append(Path('lake-manifest.json'))
rows=[]
for f in sorted(set(files)):
    target=dest/f;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,target)
    raw=f.read_bytes();rows.append(dict(path=str(f),bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
source_hash=hashlib.sha256(''.join(x['path']+'\0'+x['sha256']+'\n' for x in rows).encode()).hexdigest()
regenerated={}
with tempfile.TemporaryDirectory(prefix='recaman-regenerate-') as td:
    temp=Path(td);(temp/'Recaman').mkdir()
    work=temp/base;work.mkdir(parents=True)
    for name in ['checker_prefix.txt','q_checker_prefix.txt','certificate.json','q-certificate.json','generate_lean_data.py','generate_q_lean.py']:
        shutil.copyfile(base/name,work/name)
    for script,module in [('generate_lean_data.py','ThreeNonsuppliedData.lean'),('generate_q_lean.py','ThreeNonsuppliedQData.lean')]:
        subprocess.run([sys.executable,str((work/script).resolve())],cwd=temp,check=True,capture_output=True,timeout=30)
        expected=Path('Recaman')/module
        assert (temp/expected).read_bytes()==expected.read_bytes(),module
        regenerated[module]=hashlib.sha256(expected.read_bytes()).hexdigest()
manifest=dict(frozen_jst=datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9))).isoformat(),
              head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
              dirty_source_sha256=source_hash,files=rows,regenerated_modules=regenerated,
              scope='proof source/G5/protected/brief snapshot; historical computation artifacts stay in the evidence packet')
(base/'source_snapshot_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(dict(files=len(rows),dirty_source_sha256=source_hash,regenerated_modules=regenerated)))
