"""Read-only mathematical OUTPUT/prose/link consistency audit; never reruns a worker."""
from pathlib import Path
from datetime import datetime
from zoneinfo import ZoneInfo
import hashlib,json,re
P=Path(__file__).resolve().parent;load=lambda tag:json.loads((P/(tag+'.log')).read_text())
checks=[]
def expect(tag,key,value):
    obj=load(tag)
    for part in key.split('/'):obj=obj[part]
    assert obj==value,(tag,key,obj,value);checks.append({'tag':tag,'field':key,'value':value})
expect('generated-stock-discovery','planned_states',120);expect('generated-stock-holdout','planned_states',72)
for tag in ['generated-stock-discovery','generated-stock-holdout']:
    expect(tag,'range_complete',True);expect(tag,'counter',None)
expect('height-kernel-discovery','prefix_inequality_checks',11626)
expect('height-kernel-holdout','prefix_inequality_checks',56952)
expect('height-dual-controls','primal_basis_checks',704)
expect('height-dual-controls','perturbed_optimal_profiles_refuted',79)
assert len(load('height-dual-controls')['nongeometric_checks'])==20
expect('prefix-basis-controls','basis_walks',54);expect('prefix-basis-controls','prefix_inequality_checks',17022)
expect('staged-source-discovery','complete_words_checked',351);expect('staged-source-discovery','original_A_targets_checked',3942)
expect('staged-source-holdout','complete_words_checked',40);expect('staged-source-holdout','original_A_targets_checked',1269)
assert len(load('staged-source-holdout')['full_prehistory_controls'])==15
expect('four-filter-discovery','counts/words',63);expect('four-filter-discovery','counts/chronology_good',58);expect('four-filter-discovery','counts/chronology_bad',5)
expect('four-filter-holdout','counts/words',195);expect('four-filter-holdout','counts/chronology_good',152);expect('four-filter-holdout','counts/chronology_bad',43)
expect('predecessor-discovery','small_control_counts/words',511);expect('predecessor-discovery','small_control_counts/admissible',387)
expect('predecessor-discovery','small_control_counts/both_prepend_bad',0)
expect('stock-lookbehind-discovery','tiny_inverse_cases',576)
assert [r['n']for r in load('staged-greedy-discovery-repair1')['records']]==list(range(1,6))
assert [r['n']for r in load('staged-greedy-holdout')['records']]==[7,11,17,23]
assert [r['r']for r in load('predecessor-family-discovery')['records']]==[6,7,9,10]
assert [r['r']for r in load('predecessor-family-holdout')['records']]==[12,13,15,16]
for tag,k,ls,loss in [('stock-lookbehind-discovery',15,[0,1,3,5],824),('stock-lookbehind-holdout',35,[2,10,35],4724)]:
    rows=load(tag)['records'];assert [r['lookbehind_L']for r in rows]==ls
    assert all(r['k']==k and r['stock_loss']==loss and r['whole_original_free']==r['lookbehind_L']+3*k+1 for r in rows)
receipts=[]
for q in sorted(P.glob('*-result.json')):
    if q.name.startswith('guard-'):continue
    r=json.loads(q.read_text());log=P/(r['tag']+'.log');raw=log.read_bytes()
    if r['exit_code']==0:
        v=json.loads(raw);assert v.get('all_pass',v.get('range_complete',False))
    else:
        assert r['tag']=='staged-greedy-discovery'and b'SyntaxError'in raw and r['worker_cpu_seconds']==.046653
    receipts.append({'tag':r['tag'],'source_sha256':r['worker_source_sha256'],'output_sha256':hashlib.sha256(raw).hexdigest(),'exit_code':r['exit_code'],'CPU':r['worker_cpu_seconds']})
assert len(receipts)==20 and abs(sum(r['CPU']for r in receipts)-1.010299)<1e-8
docs=[Path(s)for s in json.loads((P/'EXPLICIT_DOC_PATHS.json').read_text())if s.endswith('.md')]
links=[]
for q in docs:
    if q.name in ['PROOF_MAP.md','RESEARCH_PORTFOLIO.md','RESEARCH_GENERALIZATION_TRACKER.md']:continue
    source=q.read_text()
    if q.name=='CURRENT_FRONTIER.md':source=source.split('## 2026-11-23:',1)[0]
    for label,target in re.findall(r'\[([^\]]+)\]\(([^)]+)\)',source):
        target=target.strip('<>').split('#',1)[0]
        if not target or re.match(r'\w+://',target):continue
        dest=Path(target)if target.startswith('/')else q.parent/target
        assert dest.exists(),('Broken local link',q,label,target)
        links.append({'from':str(q),'target':target})
out={'at':datetime.now(ZoneInfo('Asia/Tokyo')).isoformat(),'all_pass':True,'prose_metric_checks':checks,'worker_output_receipts':receipts,'local_links_checked':len(links),'links':links,
     'scope':'Output-to-prose/source/card scope audit, not a new mathematical computation or independent proof. No worker rerun. All unbounded claims remain PAPER/human review pending.',
     'nuances':['H06 discovery high-only coherent seed has9 entries and no required0; independent four-filter witness includes0 in its full interval. Neither is canonical.','H01 parameter ranges have8 nonempty generated-loss examples only; candidate remains CONJECTURED/methodSTOPPED.','H04 first failed attempt NOT prelaunch hash-frozen; corrected version is prospectively frozen, failure retained.','H07 whole0 prefix startsA and is not strictly positive; positive is the tail with complete original sources retained.']}
(P/'EVIDENCE_OUTPUT_INDEX.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'at':out['at'],'all_pass':True,'worker_outputs':len(receipts),'metric_checks':len(checks),'local_links':len(links)}))
