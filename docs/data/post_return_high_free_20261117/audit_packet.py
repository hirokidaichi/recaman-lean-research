"""Read-only provenance validation, with exact-byte archival of matching old inputs.

Late archives are labelled as such; they never imply an earlier file creation time.
No mathematical worker or stopped Lean certificate is executed.
"""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
from zoneinfo import ZoneInfo

P=Path(__file__).resolve().parent
ROOT=P.parents[2]
BASE='08fc48f20e395adc56a1ab2c8a3dac223560723d'
start=time.process_time();wanted={};tree_checks=[]
hex64=lambda x:isinstance(x,str) and re.fullmatch('[0-9a-f]{64}',x) is not None
sha=lambda b:hashlib.sha256(b).hexdigest()

def require(path,h,manifest):
 if not hex64(h):return
 wanted.setdefault((path,h),set()).add(manifest)

for f in sorted(P.glob('*.json')):
 d=json.loads(f.read_text())
 if not isinstance(d,dict):continue
 for key in ['hashes','source_sha256']:
  if isinstance(d.get(key),dict):
   for path,h in d[key].items():require(path,h,f.name)
 # Some frozen protocols/source-tree manifests are direct path/hash maps.
 for path,h in d.items():
  if '/' in path and hex64(h):require(path,h,f.name)
 if 'worker_source_sha256' in d:
  require(d['argv'][4],d['worker_source_sha256'],f.name)
  require(d['argv'][1],d['runner_sha256'],f.name)
 if 'source_tree_manifest' in d:
  mf=P/d['source_tree_manifest'];m=json.loads(mf.read_text())
  actual=sha(json.dumps(m,sort_keys=True,separators=(',',':')).encode())
  tree_checks.append(dict(receipt=f.name,manifest=mf.name,matched=actual==d['source_tree_sha256']))

archive={}
for folder in [P/'frozen',P/'stopped']:
 for f in folder.glob('*'):
  if f.is_file():archive.setdefault(sha(f.read_bytes()),str(f.relative_to(ROOT)))
current={};prefixes={}
for name in ['Recaman.lean','Recaman/Audit.lean']:
 f=ROOT/name;data=f.read_bytes();digest=hashlib.sha256();offset=0
 for line in data.splitlines(keepends=True):
  digest.update(line);offset+=len(line);h=digest.hexdigest()
  if (name,h) in wanted:prefixes[(name,h)]=data[:offset]

results=[];missing=[];late=[]
for (path,h),sources in sorted(wanted.items()):
 f=Path(path);f=f if f.is_absolute() else ROOT/f
 try:rel=str(f.relative_to(ROOT))
 except ValueError:rel=str(f)
 if f.is_file():
  if str(f) not in current:current[str(f)]=sha(f.read_bytes())
  if current[str(f)]==h:
   results.append(dict(input=rel,sha256=h,location=rel,kind='current exact bytes',manifests=sorted(sources)));continue
 if h in archive:
  results.append(dict(input=rel,sha256=h,location=archive[h],kind='archived exact bytes',manifests=sorted(sources)));continue
 data=prefixes.get((rel,h));kind='current append-only prefix matching pre-recorded hash'
 if data is None and not Path(rel).is_absolute():
  r=subprocess.run(['git','show',BASE+':'+rel],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
  if r.returncode==0 and sha(r.stdout)==h:data=r.stdout;kind='baseline Git blob matching pre-recorded hash'
 if data is not None and sha(data)==h:
  dest=P/'frozen'/(h+'-'+f.name+'.txt');dest.write_bytes(data);loc=str(dest.relative_to(ROOT));archive[h]=loc
  late.append(dict(input=rel,sha256=h,location=loc,source=kind))
  results.append(dict(input=rel,sha256=h,location=loc,kind=kind,manifests=sorted(sources)));continue
 missing.append(dict(input=rel,sha256=h,manifests=sorted(sources)))

out=dict(recorded_jst=datetime.datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),baseline=BASE,
 result='PASS' if not missing and all(x['matched'] for x in tree_checks) else 'FAIL',
 distinct_inputs=len(wanted),matched=len(results),missing=missing,source_tree_receipts=tree_checks,
 late_exact_byte_archives=late,inputs=results,cpu_seconds=time.process_time()-start,
 scope='provenance only; matching a pre-recorded hash proves byte identity, not earlier archive creation time')
(P/'FINAL_INPUT_HASH_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['result','distinct_inputs','matched','missing','cpu_seconds']}))
raise SystemExit(0 if out['result']=='PASS' else 1)
