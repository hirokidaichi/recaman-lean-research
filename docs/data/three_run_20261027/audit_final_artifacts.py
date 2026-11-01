from pathlib import Path
import hashlib,json,csv,subprocess,datetime,re
P=Path(__file__).resolve().parent;root=P.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=json.loads((P/'START.json').read_text());cur={str(x.relative_to(root)):sha(x) for x in [root/'Recaman.lean',*sorted((root/'Recaman').glob('*.lean'))]}
old=start['lean_source_sha256'];existing_changed=[x for x,h in old.items() if cur.get(x)!=h];new=sorted(set(cur)-set(old));allowed={'Recaman.lean','Recaman/Audit.lean'}
assert set(existing_changed)<=allowed,existing_changed
assert len(new)==11,new
(P/'final-source-manifest.json').write_text(json.dumps({'revision':start['revision'],'lean_sources':cur,'existing_changed':existing_changed,'new_lean':new,'unrelated_existing_lean_preserved':True},indent=2)+'\n')
worker=[];validation=[];missing=[]
for p in sorted(P.glob('*-start.json')):
 tag=p.name[:-11];rp=P/(tag+'-result.json')
 if not rp.exists():missing.append({'tag':tag,'start':p.name,'reason':'AS preexec rejected before launch' if tag=='spectrum-seven' else 'inspect'});continue
 x=json.loads(rp.read_text())
 if 'worker_cpu_seconds' in x:worker.append(x)
 elif 'cpu_seconds' in x:validation.append(x)
math=[x for x in worker if not x['tag'].startswith('guard-')];guard=[x for x in worker if x['tag'].startswith('guard-')]
# Preserve every frozen math-worker version, including the one implementation failure.
retained={sha(x):str(x.relative_to(root)) for x in P.iterdir() if x.is_file() and x.suffix in {'.py','.txt'}}
ret=[]
for x in worker:
 h=x['worker_source_sha256'];assert h in retained,(x['tag'],h)
 ret.append({'tag':x['tag'],'sha256':h,'retained':retained[h],'exit_code':x['exit_code']})
(P/'worker-source-retention.json').write_text(json.dumps(ret,indent=2)+'\n')
out={'math_worker_cpu_seconds':sum(x['worker_cpu_seconds'] for x in math),'math_worker_controller_cpu_seconds':sum(x['controller_cpu_seconds'] for x in math),'guard_worker_cpu_seconds':sum(x['worker_cpu_seconds'] for x in guard),'guard_controller_cpu_seconds':sum(x['controller_cpu_seconds'] for x in guard),'recorded_validation_cpu_seconds':sum(x['cpu_seconds'] for x in validation),'recorded_validation_runs':len(validation),'validation_runs':[{k:x[k] for k in ['tag','exit_code','cpu_seconds','wall_seconds']} for x in validation],'math_worker_runs':[{k:x[k] for k in ['tag','exit_code','worker_cpu_seconds','controller_cpu_seconds']} for x in math],'unmeasured_preexec_child_cpu':True,'unmeasured_reason':'one Popen preexec failed while trying unsupported RLIMIT_AS; no wait4 usage was captured, never infer zero','missing_result_runs':missing,'contract':'math/guard are cooperative single-Python descendants-forbidden; validation caps are per-process, not hard cumulative tree caps; CPU separate from journal wall work','cpu_totals_complete_for_entire_session':False}
(P/'final-resource-summary.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
rows={r[0]:r for r in csv.reader((root/'docs/EVIDENCE_REGISTRY.tsv').open(),delimiter='\t') if r and r[0].startswith('E-')}
labels={f'E-{i}':rows[f'E-{i}'][1] for i in range(416,433)}
assert rows['E-416'][1]=='PROVED-LEAN' and rows['E-432'][1]=='PROVED-PAPER'
for i in [424,427]:assert rows[f'E-{i}'][1]=='COMPUTED'
assert rows['E-430'][1]=='REFUTED'
for i in list(range(416,424))+[425,426,428,429,431]:assert (root/f'docs/statement_audits/E-{i}.md').exists()
# Today's own local Markdown links, excluding inert quoted paths/remote URLs.
paths=[root/'docs/RESEARCH_HANDOFF_2026-10-27_DAILY.md',root/'docs/RESEARCH_NOTE_2026-10-27_C1_SOURCE_FAMILY.md',root/'docs/HYPOTHESIS_CARD_2026-10-28_SOURCE_FAMILY_KERNEL.md',root/'docs/CURRENT_FRONTIER.md',*sorted((root/'docs').glob('HYPOTHESIS_CARD_2026-10-27_*.md'))]
bad=[];n=0
for p in paths:
 if not p.exists():continue
 for s in re.findall(r'\]\(([^)]+)\)',p.read_text()):
  s=s.split('#')[0]
  if not s or '://' in s:continue
  q=Path(s) if s.startswith('/') else p.parent/s;n+=1
  if not q.exists():bad.append({'file':str(p.relative_to(root)),'target':s})
(P/'link-audit.json').write_text(json.dumps({'checked':n,'missing':bad},ensure_ascii=False,indent=2)+'\n');assert not bad,bad
status=subprocess.check_output(['git','status','-s'],text=True,cwd=root);(P/'final-git-status.txt').write_text(status)
latest=json.loads((P/'check-final-references-result.json').read_text());assert latest['exit_code']==0
consistency={'at':datetime.datetime.now(datetime.timezone(datetime.timedelta(hours=9))).isoformat(),'existing_lean_changed':existing_changed,'new_lean_count':len(new),'unrelated_lean_preserved':True,'evidence_labels':labels,'last_full_check':'check-final-references:427jobs/2918 declarations','link_errors':bad,'stage_commit_push':'none','journal':'still active; no final time claimed','finite_tables_not_kernel':True,'automation_prompt_readback':json.loads((P/'automation-readback.json').read_text())['prompt_exact_match']}
prior=json.loads((P/'final-consistency.json').read_text()) if (P/'final-consistency.json').exists() else {}
if prior.get('journal')=='stopped; cursor null':consistency.update({k:v for k,v in prior.items() if k in ['journal','confirmed_work_seconds','shortfall_seconds','actual_end']})
(P/'final-consistency.json').write_text(json.dumps(consistency,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in ['validation_runs','math_worker_runs']},ensure_ascii=False,indent=2));print(json.dumps(consistency,ensure_ascii=False,indent=2))
