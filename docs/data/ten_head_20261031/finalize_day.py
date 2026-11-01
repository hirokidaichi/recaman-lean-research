"""Read-only journal accounting and owned day documents; never starts/stops a session."""
from pathlib import Path
import argparse,collections,datetime as dt,hashlib,json,re,subprocess
p=Path(__file__).resolve().parent;root=p.parents[2]
ap=argparse.ArgumentParser();ap.add_argument('--closed',action='store_true');a=ap.parse_args()
j=json.loads((root/'docs/data/daily_research/2026-10-31.json').read_text())
if a.closed and j['cursor'] is not None:raise SystemExit('closed journal required')
phase=collections.defaultdict(float);unit=collections.defaultdict(float);allocation=collections.defaultdict(float)
explore={4,5,6,7,8,9,17,19,21}
for s in j['segments']:
 sec=(dt.datetime.fromisoformat(s['end'])-dt.datetime.fromisoformat(s['start'])).total_seconds();phase[s['phase']]+=sec;unit[s['unit']]+=sec
 if s['phase']=='research':
  m=re.search(r'H-20261031-(\d+)',s['unit']);kind='exploration' if m and int(m[1]) in explore else 'exploitation';allocation[kind]+=sec
 else:allocation[s['phase']]+=sec
confirmed=round(sum(phase[x] for x in ['setup','research','audit','handoff']),3)
first=j['events'][0]['at'];end=j['events'][-1]['at'] if not j['cursor'] else None
summary={'date':j['date'],'closed':j['cursor'] is None,'actual_start':first,'actual_end':end,'confirmed_work_seconds':confirmed,'shortfall_seconds':round(max(0,7200-confirmed),3),'excluded':{k:round(v,3) for k,v in phase.items() if k in ['waiting','blocked']},'unconfirmed_gaps':j['unconfirmed_gaps'],'open_cursor':j['cursor'],'phase_seconds':{k:round(v,3) for k,v in phase.items()},'allocation_seconds':{k:round(v,3) for k,v in allocation.items()},'unit_seconds':{k:round(v,3) for k,v in unit.items()},'planned_seconds':{'setup':600,'exploitation':3600,'exploration':1800,'audit':600,'handoff':600},'scope':'Journal confirms declared wall intervals, not pure CPU/thinking. Parent R-20261031-01 counted once. No retrospective startup credit.'}
(p/('ACCOUNTING_FINAL.json' if a.closed else 'ACCOUNTING_SNAPSHOT.json')).write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
fmt=lambda x:f'{int(x//60)}分{x%60:06.3f}秒'
block=f"実開始 {first}、実終了 {end or '未確定（継続中）'}。confirmed_work_seconds={confirmed:.3f}、確認済み{fmt(confirmed)}、120分への不足{fmt(summary['shortfall_seconds'])}。待機/blocked除外{summary['excluded']}、未確認gap{len(j['unconfirmed_gaps'])}件。open区間は含めない。\n\n"
block+='| 区分 | 予定 | 閉区間の実績 |\n|---|---:|---:|\n'+''.join(f'| {k} | {fmt(v)} | {fmt(allocation.get(k,0))} |\n' for k,v in summary['planned_seconds'].items())
block+='\n実績はjournalのphase/unitから重複なしで分類。06:37:51〜06:39:48のaudit区間にH09 draftも混じったため、その117秒はauditとして残し純粋な役割時間を遡って推定しない。監査/保存超過は研究枠から支出し08時を延長しない。setupは実読取に合わせ31秒へ短縮、初回起動遅れを補填しない。\n'
daily=root/'docs/RESEARCH_HANDOFF_2026-10-31_DAILY.md';s=daily.read_text();s=re.sub(r'<!-- ACCOUNTING_START -->.*?<!-- ACCOUNTING_END -->','<!-- ACCOUNTING_START -->\n'+block+'<!-- ACCOUNTING_END -->',s,flags=re.S)
if a.closed:s=s.replace('（最終保存中・終了実績未確定）','（確定）')
daily.write_text(s)
if a.closed:
 schedule=root/'docs/DAILY_RESEARCH_SCHEDULE.md';ss=schedule.read_text();marker='<!-- 20261031 confirmed -->';addition='\n'+marker+'\n## 2026-10-31 実績と翌日入口\n\n'+block.split('| 区分')[0]+'\n次は[H-20261101-01](HYPOTHESIS_CARD_2026-11-01_MASS_THREE_ACTUAL_CHARGE.md)。E482の完了帯を再実行せず、E483の帯外mass3 target/old4をactualfreeへ接続する。自動実行の同ID/ACTIVE/6時・6時半・7時・7時半/同chat/必須final報告をreadback済み。未来の2時間完遂は未確認。正本は[DAILY](RESEARCH_HANDOFF_2026-10-31_DAILY.md)/[journal](data/daily_research/2026-10-31.json)。\n'
 if marker not in ss:schedule.write_text(ss+addition)
base=json.loads((p/'START.json').read_text())['lean_sources'];cur={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in [root/'Recaman.lean',*sorted((root/'Recaman').glob('*.lean'))]};rs=[]
for f in p.glob('*-result.json'):
 try:r=json.loads(f.read_text())
 except Exception:continue
 r['result_file']=str(f.relative_to(root));rs.append(r)
new={x:h for x,h in cur.items() if x not in base};checks={};missing=[]
for f,h in new.items():
 matches=[r for r in rs if r.get('exit_code')==0 and '-M512' in r.get('argv',[]) and r.get('source_sha256',{}).get(f)==h]
 checks[f]={'sha256':h,'strict_512_pass':[r['result_file'] for r in matches]}
 if not matches:missing.append(f)
manifest={'at':dt.datetime.now().astimezone().isoformat(),'baseline_changed':[x for x in base if cur.get(x)!=base[x]],'new_source_count':len(new),'missing_current_byte_512_pass':missing,'adopted':checks,'all_lean_sha256':cur,'excluded_unverified':[str(x.relative_to(root)) for x in p.glob('*unverified*')]+[str(x.relative_to(root)) for x in p.glob('*unadopted*')]};(p/'SOURCE_VALIDATION_INDEX.json').write_text(json.dumps(manifest,indent=2)+'\n')
math=[r for r in rs if 'worker_cpu_seconds' in r and not r.get('tag','').startswith('guard')];guard=[r for r in rs if 'worker_cpu_seconds' in r and r.get('tag','').startswith('guard')];lean=[r for r in rs if 'cpu_seconds' in r]
cpu={'math_cpu_seconds':round(sum(r['worker_cpu_seconds'] for r in math),6),'math_budget_seconds':3,'math':[{k:r.get(k) for k in ['tag','worker_cpu_seconds','exit_code','reason','result_file']} for r in math],'guard_cpu_seconds':round(sum(r['worker_cpu_seconds'] for r in guard),6),'lean_validation_cpu_seconds_wait4':round(sum(r['cpu_seconds'] for r in lean),6),'lean_runs':len(lean),'single_worker_controller_cpu_seconds':round(sum(r.get('controller_cpu_seconds',0) for r in math+guard),6),'unmetered_cpu_scope':'Direct registry/lint/link checks, ordinary Python recording, tool/network time and model work are not included and are not assigned zero.','scope':'CPU separate from wall journal. Lean caps are per-process, not cumulative tree caps. Failed runs counted. RLIMIT_CPU granularity exceeded nominal1s slightly on SIGXCPU holdout.'};(p/'CPU_SUMMARY.json').write_text(json.dumps(cpu,indent=2)+'\n')
print(json.dumps({'closed':summary['closed'],'confirmed':confirmed,'end':end,'allocation_seconds':summary['allocation_seconds'],'missing_512':missing,'math_cpu':cpu['math_cpu_seconds'],'lean_cpu':cpu['lean_validation_cpu_seconds_wait4']},ensure_ascii=False))
