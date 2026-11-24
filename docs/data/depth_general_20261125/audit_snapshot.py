"""Owned docs/evidence snapshot only; no mathematical worker or Lean retry."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import argparse,ast,base64,csv,hashlib,json,re,subprocess

ap=argparse.ArgumentParser();ap.add_argument('--final',action='store_true');args=ap.parse_args()
P=Path(__file__).resolve().parent;root=Path.cwd();prefix=str(P.relative_to(root))+'/'
base=json.loads((P/'BASELINE.json').read_text())
run=lambda argv:subprocess.check_output(argv,text=True).strip()
assert run(['git','branch','--show-current'])=='main'
assert run(['git','rev-parse','HEAD'])==base['head']
assert not run(['git','diff','--cached','--name-only']),'Preserve preexisting index'
shared={'docs/CURRENT_FRONTIER.md','docs/EVIDENCE_REGISTRY.tsv','docs/PROOF_MAP.md','docs/RESEARCH_PORTFOLIO.md','docs/RESEARCH_GENERALIZATION_TRACKER.md'}
prior=set(base['prior_unpublished_owned_paths'])
for s in prior-shared:
    assert hashlib.sha256(Path(s).read_bytes()).hexdigest()==base['prior_unpublished_sha256'][s],('Prior-day bytes changed',s)
for s in base['unowned']:
    assert hashlib.sha256(Path(s).read_bytes()).hexdigest()==base['unowned_sha256'][s]
today=set(json.loads((P/'EXPLICIT_DOC_PATHS.json').read_text()))
changed=lambda:set(run(['git','diff','--name-only']).splitlines()+run(['git','ls-files','--others','--exclude-standard']).splitlines())
paths=changed()-set(base['unowned'])
assert all(s in prior or s in today or s.startswith(prefix)for s in paths),sorted(s for s in paths if s not in prior|today and not s.startswith(prefix))
assert not any(s.startswith('Recaman')or'protected_pins/'in s or s.endswith('PROTECTED_CLAIMS.tsv')for s in paths)
assert not any(any(t in Path(s).parts for t in ['__pycache__','.cache','.git'])or s.endswith(('.pyc','.lock','.env'))for s in paths)
for q in P.glob('*.py'):ast.parse(q.read_text(),filename=str(q))
archives=[]
for s in sorted(paths-prior):
    q=Path(s);raw=q.read_bytes();txt=raw.decode('utf-8')
    bad=txt.endswith('\n\n')or any(line.rstrip()!=line for line in txt.splitlines())
    if bad and q.suffix=='.log':
        sha=hashlib.sha256(raw).hexdigest();a=P/'raw_stdout'/f'{sha}.json';a.parent.mkdir(exist_ok=True)
        a.write_text(json.dumps({'path':s,'sha256':sha,'encoding':'base64','exact_original_bytes':base64.b64encode(raw).decode(),'reason':'Exact stdout archived BEFORE display-only whitespace normalization'},indent=2)+'\n')
        q.write_text('\n'.join(line.rstrip()for line in txt.rstrip().splitlines())+'\n');archives.append({'view':s,'archive':str(a.relative_to(root)),'original_sha256':sha})
    elif bad:raise AssertionError(('Review non-log whitespace',s))
if archives:
    old=json.loads((P/'RAW_STDOUT_ARCHIVES.json').read_text())if(P/'RAW_STDOUT_ARCHIVES.json').exists()else[]
    (P/'RAW_STDOUT_ARCHIVES.json').write_text(json.dumps(old+archives,indent=2)+'\n')
paths=changed()-set(base['unowned'])
audit_path=prefix+'OWNED_CONTENT_AUDIT.json';manifest_path=prefix+'OWNED_PATHS.json'
future=[prefix+x for x in ['FINAL_WORK_SUMMARY.json','FINAL_BRIEF.json','FINAL_BRIEF.log']]
paths.update([audit_path,manifest_path]);manifest={'paths':sorted(paths-set(future)),'explicit_anticipated_after_stop':future,'excluded_unowned':base['unowned'],'prior_unpublished_owned_count':len(prior),'scope':'Explicit prior160 owned frozen snapshot plus Nov25 docs/journal/packet and two UNEXECUTED Nov26 cards; no foreign journals/Lean/gates/protected/cache. Post-push receipt is separate explicit docs-only commit.'}
(P/'OWNED_PATHS.json').write_text(json.dumps(manifest,indent=2)+'\n')
present=sorted(s for s in paths|set(future)if Path(s).is_file()and s!=audit_path)
blobs={hashlib.sha256(Path(s).read_bytes()).hexdigest():s for s in present}
for q in (P/'raw_stdout').glob('*.json')if(P/'raw_stdout').exists()else[]:
    r=json.loads(q.read_text());raw=base64.b64decode(r['exact_original_bytes']);assert hashlib.sha256(raw).hexdigest()==r['sha256'];blobs[r['sha256']]=str(q)+' decoded'
receipt_checks=[]
for q in P.glob('*-result.json'):
    r=json.loads(q.read_text());assert 'finished_jst'in r
    for key in ['worker_source_sha256','runner_sha256']:assert r[key]in blobs,(q,key,r[key])
    receipt_checks.append(q.name)
protocol_checks=[]
def dig(value):
    if isinstance(value,dict):
        for v in value.values():yield from dig(v)
    elif isinstance(value,list):
        for v in value:yield from dig(v)
    elif isinstance(value,str)and re.fullmatch('[a-f0-9]{64}',value):yield value
for q in P.glob('*PROTOCOL.json'):
    for sha in dig(json.loads(q.read_text())):
        assert sha in blobs,('Frozen version missing',q.name,sha);protocol_checks.append({'protocol':q.name,'sha256':sha,'stored_bytes':blobs[sha]})
for q in P.glob('H*_PAPER_ADOPTION.json'):
    r=json.loads(q.read_text());np=r.get('note',r.get('paper_note'));au=r.get('audit',r.get('meaning_audit'))
    assert hashlib.sha256(Path(np).read_bytes()).hexdigest()==r['note_sha256'],q.name
    assert hashlib.sha256(Path(au).read_bytes()).hexdigest()==r['audit_sha256'],q.name
rows=list(csv.DictReader(Path('docs/EVIDENCE_REGISTRY.tsv').read_text().splitlines(),delimiter='\t'))
new=json.loads((P/'NEW_REGISTRY_ROWS.json').read_text());assert len(rows)==780 and rows[-6:]==new
assert sum(r['label']=='PROVED-LEAN'for r in rows)==477
old_registry='\n'.join(Path('docs/EVIDENCE_REGISTRY.tsv').read_text().splitlines()[:775])+'\n'
assert hashlib.sha256(old_registry.encode()).hexdigest()==base['prior_unpublished_sha256']['docs/EVIDENCE_REGISTRY.tsv'],'Historical registry rows changed'
for r in new:assert Path(r['artifact']).exists()and r['id']in Path('docs/CURRENT_FRONTIER.md').read_text()
assert Path('docs/CURRENT_FRONTIER.md').read_text().count('\n## Research brief\n')==1
for tag in ['architecture','registry','manifest','brief']:assert json.loads((P/f'validation-{tag}.json').read_text())['exit_code']==0
j=json.loads(Path('docs/data/daily_research/2026-11-25.json').read_text());late=[]
for seg in j['segments']:
    sec=(datetime.fromisoformat(seg['end'])-datetime.fromisoformat(seg['start'])).total_seconds()
    if sec>300:late.append({'start':seg['start'],'end':seg['end'],'seconds':sec,'unit':seg.get('unit')})
if args.final:
    assert j['cursor']is None and all(Path(s).exists()for s in future)
out={'at':datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'final_after_stop':args.final,'owned_file_count':len(present)+1,'prior_frozen_paths_checked':len(prior-shared),'shared_current_paths':sorted(shared),'hashes':{s:hashlib.sha256(Path(s).read_bytes()).hexdigest()for s in present},'all_receipt_source_hashes_present':True,'completed_process_receipts':sorted(receipt_checks),'protocol_hash_checks':protocol_checks,'late_checkpoint_intervals':late,'raw_archives_added':archives,'static_scope':'architecture/registry/G1-G5/protected/G6-static/viewer/brief passed; full Lean/G6 Lean half NOT run (no Lean changes)','new_Lean':False,'unowned_preserved':base['unowned_sha256'],'historical_registry_prefix_unchanged':True,'H04_initial_prelaunch_hash_exception':'explicit failure preserved, later repair hash is NOT retroactive','index_untouched':True}
(P/'OWNED_CONTENT_AUDIT.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
subprocess.run(['git','diff','--check'],check=True)
print(json.dumps({k:out[k]for k in ['at','final_after_stop','owned_file_count','prior_frozen_paths_checked','late_checkpoint_intervals','raw_archives_added']},ensure_ascii=False,indent=2))
