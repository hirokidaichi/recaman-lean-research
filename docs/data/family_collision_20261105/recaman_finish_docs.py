from pathlib import Path
import json,hashlib,tomllib,subprocess,collections,datetime
packet=Path('docs/data/family_collision_20261105')
# Current-byte evidence: exact -M512 successes, not inferred from a warm build.
receipts=[]
for p in packet.glob('*-result.json'):
 try:d=json.loads(p.read_text())
 except Exception:continue
 d['_receipt']=str(p);receipts.append(d)
files=sorted(set(subprocess.check_output(['git','ls-files','--others','--exclude-standard','Recaman'],text=True).splitlines()+subprocess.check_output(['git','diff','--name-only','--diff-filter=A','f06d97ea35ffa528a383f1edd37ecd27f2d6bf35','--','Recaman'],text=True).splitlines()))
proof=[]
for x in files:
 if not x.endswith('.lean'):continue
 sh=hashlib.sha256(Path(x).read_bytes()).hexdigest()
 hits=[d for d in receipts if d.get('exit_code')==0 and d.get('source_sha256',{}).get(x)==sh and '-M512' in d.get('argv',[])]
 proof.append({'path':x,'sha256':sh,'accepted_receipts':[d['_receipt'] for d in hits]})
(packet/'CURRENT_BYTE_ACCEPTANCE.json').write_text(json.dumps(proof,ensure_ascii=False,indent=2)+'\n')
assert all(x['accepted_receipts'] for x in proof),[x for x in proof if not x['accepted_receipts']]
# Include failed validation attempts; do not turn unmeasured CPU into zero.
cpu=collections.defaultdict(float);unknown=[];classified=[]
for d in receipts:
 argv=d.get('argv',[])
 kind='guard_validation' if ('make' in argv and 'test-tools' in argv) or any('lint_new' in a or 'harness_gate' in a or 'test_harness' in a for a in argv) else 'lean_validation'
 v=d.get('cpu_seconds')
 if isinstance(v,(float,int)):cpu[kind]+=v
 else:unknown.append(d['_receipt'])
 classified.append({'receipt':d['_receipt'],'kind':kind,'cpu_seconds':v,'exit_code':d.get('exit_code'),'argv':argv})
ledger={'mathematical_worker':'not launched; budget0','measured_cpu_seconds':dict(cpu),'unmeasured_receipts':unknown,'other_shell_git_journal_docs_cpu':'not measured; not counted as0','cap_scope':'10CPU per-process/20wall individual Lean,60CPU per-process/90wall wholecheck; NOT cumulative process-tree/OS address-space cap','entries':classified}
(packet/'CPU_LEDGER.json').write_text(json.dumps(ledger,ensure_ascii=False,indent=2)+'\n')
auto=tomllib.loads(Path('/Users/hirokidaichi/.codex/automations/recam-n-6-8/automation.toml').read_text())
a={k:auto[k] for k in ['id','kind','name','status','rrule','target_thread_id']};a['prompt_sha256']=hashlib.sha256(auto['prompt'].encode()).hexdigest();a['next_card']='H-20261106-01';a['readback_verified']=a['next_card'] in auto['prompt']
(packet/'AUTOMATION_READBACK.json').write_text(json.dumps(a,ensure_ascii=False,indent=2)+'\n')
# Explicit current references; no obsolete source is advertised as the next unknown edge.
p=Path('docs/CURRENT_FRONTIER.md');s=p.read_text();at=s.index('## 次の一問')
table='''## 当日証拠の参照

| IDs | 意味 |
|---|---|
| E-546 / E-547 / E-557 / E-563 / E-572 | 狭いmass1 fullgap。E575会計に包含、独立coverageを重複計上しない。 |
| E-558 / E-559 | 同targetのearly-family clockとv2 support。 |
| E-560 / E-561 / E-562 | low-old排除、mixed zerohead circle、actual source free-floor。 |
| E-564 / E-566 / E-567 | mass2 v4/all-old帯budget/全v zerohead fullgap。 |
| E-565 / E-569 / E-570 / E-571 / E-573 / E-574 | mixed source順序、circle、defect source union、actual mass charge。 |
| E-568 / E-575 / E-576 / E-577 / E-578 / E-579 / E-580 | 現行coverage・会計・mixed拡張・actual counterband・未Lean次unit。 |

'''
if '## 当日証拠の参照' not in s:p.write_text(s[:at]+table+s[at:])
p=Path('docs/DAILY_RESEARCH_SCHEDULE.md');s=p.read_text().replace('最終更新: 2026-11-04','最終更新: 2026-11-05',1);start=s.index('2026-11-06の現行入口') if '2026-11-06の現行入口' in s else s.index('2026-11-05の現行入口');end=s.index('以下の初回計画',start)
s=s[:start]+'''2026-11-06の現行入口は[H-20261106-01](HYPOTHESIS_CARD_2026-11-06_TOP_GAP_SAME_TARGET.md)。[11/05 DAILY](RESEARCH_HANDOFF_2026-11-05_DAILY.md)→[source collision note](RESEARCH_NOTE_2026-11-05_C1_SOURCE_COLLISION.md)→[gap13 source note](RESEARCH_NOTE_2026-11-05_TOP_GAP_SOURCE.md)→同カード。
E568 zerohead/oldtarget全massとE575 arbitrarymixed mass1はPROVED-LEAN。E579 genuine四run oldtarget counterはj13/A30/selectedwindow108へ。E580 j13のv1/A30/C2..4/T15or16/negativeheadはPAPER、actual counted-source witness/clock接着は未Lean。最初15分は同元p j13/C4 counterからold+initialS witnessとT>=15/h>=7を内部供給し、未知tuple/free結論を新Propで入力しない。進まなければC2/C3同joint25分とnegativehead/shared-prefix機構20分へ。全old履歴と他source massを保持する。
E438 AS式/E458 actual17は既存入力で再証明しない。狭いmass1枝をE575に追加の独立coverageと数えない。H12/H23及び旧r4/H06/H21等STOPは資源/tactic/split/import変更で再開せず、r3/Q/C2初日監査へ戻らない。CPU探索当初0、07:45探索stop、確定journal/main通常publication/必須日次報告を継続する。
'''+s[end:];p.write_text(s)
# Stable result detail, not just theorem/module counts.
p=Path('docs/RESEARCH_NOTE_2026-11-05_C1_SOURCE_COLLISION.md');s=p.read_text()
if 'Final meaning audit' not in s:s+='''

## Final meaning audit / 2026-11-05

E567 closes allzerohead mass2 separators by a new all-old lateband budget and source floor; E568 is typed coverage integration. E575 then exposes a simpler general mass/count conservation proof for arbitrarymixed mass1 targets at allrun counts. Earlier narrowmass1 fullgap theorems remain accepted but are subsumed; source coupling is recorded separately. E576 extends existingE438's three-run AS formula, not a new identity. ExistingE458 supply17 is reused, not rediscovered.

E579's current nonzerohead oldtarget frontier is a necessary counterband free4..13/A30/j13/C2..14/S30/B60/selectedsuffix35/selectedwindow108. The selectedwindow bound does not delete the history before it or other highmass suppliers. The j14 exclusion derives actualtotal17/head10/last7/headfree4 internally and couplesheadA14 to AS cross68; no witness/free conclusion input. E580 topj13 source/negativehead/fourtuple classification is PAPER only, with a separate complete argument in TOP_GAP_SOURCE. GeneralC1/Q/H/SL/surjectivity remain unresolved.
'''
p.write_text(s)
print(json.dumps({'current_byte_modules':len(proof),'unmatched':0,'cpu':dict(cpu),'unmeasured':unknown,'automation_verified':a['readback_verified']},ensure_ascii=False))
