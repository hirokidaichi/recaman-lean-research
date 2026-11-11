import json,hashlib,subprocess,importlib.util
from pathlib import Path
packet=Path(__file__).parent
spec=importlib.util.spec_from_file_location('harness','scripts/harness_gate.py');h=importlib.util.module_from_spec(spec);spec.loader.exec_module(h)
results=[json.loads(p.read_text()) for p in packet.glob('*-result.json')]
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard','Recaman'],text=True).splitlines()
mods=sorted(set([x for x in new if x.endswith('.lean')]+['Recaman/FloorSupplyPairCharge.lean']))
accepted=[]
for path in mods:
 sha=hashlib.sha256(Path(path).read_bytes()).hexdigest()
 matches=[r['tag'] for r in results if r['exit_code']==0 and r.get('source_sha256',{}).get(path)==sha and '-M512' in r['argv']]
 assert matches,(path,sha)
 accepted.append({'path':path,'sha256':sha,'successful_512MB_receipts':matches})
idx=h.theorem_index();signatures=[]
for i in range(678,701):
 rid=f'E-{i}';row=next(c for c in h.read_registry('docs/EVIDENCE_REGISTRY.tsv') if c[0]==rid)
 audit=Path(f'docs/statement_audits/{rid}.md').read_text()
 for sym in row[5].split(';'):
  sig=h.signature_text(idx[sym][1]);assert sig in audit,(rid,sym)
  signatures.append({'row':rid,'symbol':sym,'signature_verbatim':True})
assert not Path('Recaman/DepthSixSourceResidual.lean').exists()
summary={'accepted_individual_sources':accepted,'signatures':signatures,'C05_tree_sha256':next(r['source_tree_sha256'] for r in results if r['tag']=='C05'),'failed_sources':'packet only; H49R accepted but not adopted after shadowed-binder audit','human_review':'pending','C1':'unproved'}
(packet/'FINAL_CURRENT_BYTES_AND_SIGNATURES.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
for m in mods:subprocess.run(['python3','scripts/harness_gate.py','--lint-module',m],check=True)
print(json.dumps({'current_sources':len(accepted),'verbatim_signatures':len(signatures),'status':'pass'}))
