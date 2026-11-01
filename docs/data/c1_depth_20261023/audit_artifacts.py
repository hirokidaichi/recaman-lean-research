"""Read-only provenance/class summary, plus saved CPU accounting output."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import resource

resource.setrlimit(resource.RLIMIT_CPU,(5,7))
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
mapping={'RUNS.json':'eighth_a.cpp','INDEPENDENT_RUN.json':'independent_eighth_a.cpp',
         'SIGNATURE_RUN.json':'signature_graph.py','CERTIFICATE_RUN.json':'graph_certificate.py',
         'Q_RUN.json':'q_graph.py','Q_INDEPENDENT_RUN.json':'q_independent.py',
         'HIGHER_RUNS.json':'sixteenth_a.cpp','RELAXED_HIGHER_RUN.json':'relaxed_higher.py',
         'HIGHER_INDEPENDENT_RUN.json':'higher_independent.py','TERMINAL_SUPPORT_RUN.json':'terminal_support.py'}
checks={}
for meta,source in mapping.items():
    data=json.loads((p/meta).read_text())
    checks[source]=sha(p/source)==data['source_sha256']
for row in json.loads((p/'Q4_RUNS.json').read_text())['runs']:
    file=Path(row['argv'][1]);checks[file.name]=sha(file)==row['source_sha256']
checks['q4_root_input']=sha(p/'relaxed-higher.json')==json.loads((p/'Q4_RUNS.json').read_text())['roots_source_sha256']
checks['terminal_dependency']=sha(p/'ledger_checks.py')==json.loads((p/'TERMINAL_SUPPORT_RUN.json').read_text())['ledger_dependency_sha256']
assert all(checks.values()),checks

classes=json.loads((p/'relaxed-higher.json').read_text())['classes']
class_summary=[]
for r,ws in enumerate(classes):
    deepest=0
    for w in ws:
        f=0;low=0
        for c in w:f+=1 if c=='A' else -1;low=min(low,f)
        assert f==r-1
        deepest=max(deepest,-low)
    class_summary.append(dict(r=r,candidates=len(ws),max_A=max(w.count('A') for w in ws),
                              max_length=max(map(len,ws)),max_depth=deepest))
assert class_summary[4]['max_depth']==4

timed=['discovery','holdout','independent','signature-graph','certificate','q','q-independent',
       'higher-discovery','higher-holdout','relaxed-higher','higher-independent','q4','q4-independent','terminal-support']
times=[]
for name in timed:
    raw=(p/(name+'.time')).read_text()
    vals={k:float(v) for k,v in re.findall(r'^(real|user|sys) ([0-9.]+)$',raw,re.M)}
    assert {'real','user','sys'}<=vals.keys(),name
    times.append(dict(run=name,**vals,cpu_seconds=vals['user']+vals['sys']))
total=sum(t['cpu_seconds'] for t in times)
assert total+5+0.02*len(times)<240
report=dict(source_checks=checks,all_source_hashes_match=True,classes=class_summary,
            cpu=dict(measured_runs=times,rounded_measured_cpu_seconds=round(total,3),budget_seconds=240,
                     rounding_bound_seconds=round(0.02*len(times),3),
                     unmeasured_literal_control_cpu_cap_seconds=5,
                     compilation_and_Lean_validation='separate; early validation CPU not fully measured',
                     journal_work_seconds_are_not_cpu_seconds=True))
(p/'artifact-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'source_checks':len(checks),'all_source_hashes_match':True,'classes':class_summary,
                  'rounded_measured_cpu_seconds':round(total,3),'unmeasured_control_cap_seconds':5}))
