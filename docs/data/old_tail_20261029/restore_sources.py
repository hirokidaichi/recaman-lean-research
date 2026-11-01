"""Restore a frozen source packet to a new directory; does not run any build."""
import hashlib,json,sys
from pathlib import Path
if len(sys.argv)!=2:raise SystemExit('usage: restore_sources.py NEW_DIRECTORY')
base=Path(__file__).resolve().parent
target=Path(sys.argv[1]).expanduser().absolute()
if target.exists():raise SystemExit('destination already exists; refusing to overwrite')
manifest=json.loads((base/'REPRODUCTION_MANIFEST.json').read_text())
verified=[]
for relative,entry in manifest['files'].items():
 rel=Path(relative)
 if rel.is_absolute() or '..' in rel.parts:raise SystemExit('unsafe recorded path')
 blob=(base/entry['blob']).resolve()
 if not blob.is_relative_to(base):raise SystemExit('unsafe blob path')
 data=blob.read_bytes()
 if hashlib.sha256(data).hexdigest()!=entry['sha256']:raise SystemExit('blob hash mismatch: '+relative)
 verified.append((target/rel,data,entry['mode']))
target.mkdir(parents=True)
for path,data,mode in verified:
 path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data);path.chmod(mode)
print('Restored',len(verified),'verified files; no build executed')
