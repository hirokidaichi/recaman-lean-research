"""Owned snapshot/content audit; never stage files or retry any Lean job."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import argparse,ast,base64,csv,hashlib,json,subprocess
ap=argparse.ArgumentParser();ap.add_argument('--final',action='store_true');a=ap.parse_args()
P=Path(__file__).resolve().parent;root=Path.cwd();prefix=str(P.relative_to(root))+'/'
base=json.loads((P/'BASELINE.json').read_text())
allowed={
 'docs/CURRENT_FRONTIER.md','docs/EVIDENCE_REGISTRY.tsv','docs/PROOF_MAP.md','docs/RESEARCH_PORTFOLIO.md','docs/RESEARCH_GENERALIZATION_TRACKER.md',
 'docs/HYPOTHESIS_CARD_2026-11-22_LOW_CANDIDATE_CLASS_DEPTH.md',
 'docs/HYPOTHESIS_CARD_2026-11-22_ADJACENT_CLASS_BIRTH.md','docs/HYPOTHESIS_CARD_2026-11-22_CLASS_CLOCK_CAPACITY.md',
 'docs/HYPOTHESIS_CARD_2026-11-22_LAST_FREE_CLASS_FLOOR.md','docs/HYPOTHESIS_CARD_2026-11-22_LOW_AGE_FINITE_CERTIFICATE.md',
 'docs/HYPOTHESIS_CARD_2026-11-22_LOW_NUMERIC_AGE_NO_GO.md','docs/HYPOTHESIS_CARD_2026-11-22_NUMERIC_BLOCKER_AGE.md','docs/HYPOTHESIS_CARD_2026-11-22_THREE_LOW_CLASSES.md',
 'docs/HYPOTHESIS_CARD_2026-11-23_SOURCE_KEY_BAND_COST.md','docs/RESEARCH_HANDOFF_2026-11-22_DAILY.md',
 'docs/RESEARCH_NOTE_2026-11-22_ADJACENT_CLASS_COUNTER.md','docs/RESEARCH_NOTE_2026-11-22_CLASS_CLOCK_CAPACITY.md',
 'docs/RESEARCH_NOTE_2026-11-22_LAST_FREE_CLASS_FLOOR.md','docs/RESEARCH_NOTE_2026-11-22_LOW_CLASS_FIRST_GATE.md',
 'docs/RESEARCH_NOTE_2026-11-22_LOW_NUMERIC_AGE.md','docs/RESEARCH_NOTE_2026-11-22_NUMERIC_BLOCKER_AGE.md','docs/RESEARCH_NOTE_2026-11-22_THREE_LOW_CLASSES.md',
 'docs/data/daily_research/2026-11-22.json'}
run=lambda args:subprocess.check_output(args,text=True).strip()
assert run(['git','branch','--show-current'])=='main'
assert run(['git','rev-parse','HEAD'])==base['head']
assert not run(['git','diff','--cached','--name-only']),'Preserve any foreign index'
for path in base['unowned']:
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==base['unowned_sha256'][path]
def changed():
 return set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())
def is_owned(s):return s in allowed or s.startswith(prefix)
paths=changed()-set(base['unowned'])
assert all(is_owned(s) for s in paths),sorted(s for s in paths if not is_owned(s))
assert not any(s.startswith('Recaman') or 'protected_pins/' in s or s.endswith('PROTECTED_CLAIMS.tsv') for s in paths)
assert not any(any(t in Path(s).parts for t in ['__pycache__','.git','.cache']) or s.endswith(('.lock','.pyc','.env')) for s in paths)
for q in sorted(P.glob('*.py')):ast.parse(q.read_text(),filename=str(q))
# Exact raw output is archived BEFORE any display whitespace normalization.
archives=[]
for s in sorted(paths):
 q=Path(s);raw=q.read_bytes();text=raw.decode('utf-8')
 bad=text.endswith('\n\n') or any(l.rstrip()!=l for l in text.splitlines())
 if bad and q.suffix=='.log':
  sha=hashlib.sha256(raw).hexdigest();archive=P/'raw_stdout'/f'{sha}.json';archive.parent.mkdir(exist_ok=True)
  archive.write_text(json.dumps({'path':s,'sha256':sha,'encoding':'base64','exact_original_bytes':base64.b64encode(raw).decode(),'reason':'Exact stdout preserved; human-readable log view normalized only for whitespace audit'},indent=2)+'\n')
  q.write_text('\n'.join(l.rstrip() for l in text.rstrip().splitlines())+'\n');archives.append({'view':s,'raw_archive':str(archive.relative_to(root)),'original_sha256':sha})
 elif bad:
  raise AssertionError('Owned non-log whitespace needs review: '+s)
if archives:
 old=json.loads((P/'RAW_STDOUT_ARCHIVES.json').read_text()) if (P/'RAW_STDOUT_ARCHIVES.json').exists() else []
 (P/'RAW_STDOUT_ARCHIVES.json').write_text(json.dumps(old+archives,indent=2)+'\n')
paths=changed()-set(base['unowned'])
audit_path=str((P/'OWNED_CONTENT_AUDIT.json').relative_to(root));manifest_path=str((P/'OWNED_PATHS.json').relative_to(root))
paths.update([audit_path,manifest_path])
future=[str((P/'FINAL_WORK_SUMMARY.json').relative_to(root))]
manifest={'paths':sorted(paths-set(future)),'explicit_anticipated_after_stop':future,
 'excluded_unowned':base['unowned'],'scope':'Explicit Nov22 docs/journal and owned reproducibility packet only. No Lean/root/Audit/gate/protected/previous-day changes. Publication receipts are a subsequent exact docs-only commit.'}
(P/'OWNED_PATHS.json').write_text(json.dumps(manifest,indent=2)+'\n')
present=sorted(s for s in paths|set(future) if Path(s).is_file() and s!=audit_path)
blob_hashes={hashlib.sha256(Path(s).read_bytes()).hexdigest():s for s in present}
for q in (P/'raw_stdout').glob('*.json') if (P/'raw_stdout').exists() else []:
 d=json.loads(q.read_text());raw=base64.b64decode(d['exact_original_bytes'])
 assert hashlib.sha256(raw).hexdigest()==d['sha256']
 blob_hashes[d['sha256']]=str(q)+' (decoded original bytes)'
hash_checks=[]
for q in sorted(P.glob('*-result.json')):
 d=json.loads(q.read_text())
 for key in ['worker_source_sha256','runner_sha256']:
  if key in d:assert d[key] in blob_hashes,(q,key,d[key])
 hash_checks.append(str(q.relative_to(root)))
protocol_hash_checks=[]
for q in sorted(P.glob('*PROTOCOL.json')):
 d=json.loads(q.read_text());values=[]
 for key,value in d.items():
  if 'hash' not in key.lower() and 'sha256' not in key.lower():continue
  values.extend(value.values() if isinstance(value,dict) else [value])
 for sha in values:
  assert isinstance(sha,str) and sha in blob_hashes,('Frozen input version missing',q.name,sha)
  protocol_hash_checks.append({'protocol':q.name,'sha256':sha,'stored_bytes':blob_hashes[sha]})
rows=list(csv.DictReader(Path('docs/EVIDENCE_REGISTRY.tsv').read_text().splitlines(),delimiter='\t'))
new=[r for r in rows if r['id'] in ['E-768','E-769','E-770','E-771']]
assert new==json.loads((P/'NEW_REGISTRY_ROWS.json').read_text())
assert len(rows)==771 and all(Path(r['artifact']).exists() for r in new)
frontier=Path('docs/CURRENT_FRONTIER.md').read_text()
assert frontier.count('\n## Research brief\n')==1 and '最終更新: 2026-11-22' in frontier
for r in new:assert r['id'] in frontier
for tag in ['architecture','registry','manifest','brief']:
 assert json.loads((P/f'validation-{tag}.json').read_text())['exit_code']==0
j=json.loads(Path('docs/data/daily_research/2026-11-22.json').read_text());late=[]
for seg in j['segments']:
 seconds=(datetime.fromisoformat(seg['end'])-datetime.fromisoformat(seg['start'])).total_seconds()
 if seconds>300:late.append({'start':seg['start'],'end':seg['end'],'seconds':seconds,'unit':seg.get('unit')})
if a.final:assert j['cursor'] is None and (P/'FINAL_WORK_SUMMARY.json').exists()
out={'at':datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'final_after_journal_stop':a.final,'owned_file_count':len(present)+1,
 'hashes':{s:hashlib.sha256(Path(s).read_bytes()).hexdigest() for s in present},'all_recorded_source_and_frozen_input_hashes_present':True,
 'finished_process_receipts':hash_checks,'late_checkpoint_intervals':late,'raw_archives_added':archives,
 'protocol_hash_checks':protocol_hash_checks,
 'static_checks':'architecture/registry/G1-G5/protected/G6-static/viewer/brief passed; Python AST/ownership/text/frozen input hashes checked',
 'new_Lean_adoption':False,'full_new_Lean_build':'not run; first finite candidate failed512MB; inherited helper512STOPPED not retried',
 'protected_and_previous_day_files_unchanged':True,'unowned_preserved':base['unowned_sha256'],'index_untouched':True}
(P/'OWNED_CONTENT_AUDIT.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:out[k] for k in ['at','final_after_journal_stop','owned_file_count','late_checkpoint_intervals','raw_archives_added']},ensure_ascii=False,indent=2))
