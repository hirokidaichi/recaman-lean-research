"""Reproduce final small framework and explicit-root Q certificate; never run stopped r4 generators."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

base=Path(__file__).resolve().parent
root=base.parents[2]
p=argparse.ArgumentParser();p.add_argument('--write',action='store_true');args=p.parse_args()
with tempfile.TemporaryDirectory(prefix='recaman-final-sources-') as tmp:
    tmp=Path(tmp);(tmp/'Recaman').mkdir()
    (tmp/'Recaman/FourNonsuppliedData.lean').write_bytes((base/'FourNonsuppliedData.template.lean.txt').read_bytes())
    subprocess.run([sys.executable,str(base/'generate_q_lean.py')],cwd=tmp,check=True,capture_output=True,text=True)
    results=[]
    for name in ['FourNonsuppliedData.lean','SixteenRootAreaData.lean']:
        path=Path('Recaman')/name;data=(tmp/path).read_bytes()
        if args.write:(root/path).write_bytes(data)
        match=(root/path).read_bytes()==data
        results.append(dict(path=str(path),sha256=hashlib.sha256(data).hexdigest(),byte_identical=match))
    assert all(r['byte_identical'] for r in results),results
    print(json.dumps(dict(mode='write' if args.write else 'check-only',sources=results)))
