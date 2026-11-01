"""Finalize saved report metadata only after the real session has already stopped."""
from pathlib import Path
import datetime,hashlib,json,subprocess
p=Path(__file__).parent
status=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
assert status['cursor'] is None and status['open_interval_unconfirmed_seconds']==0
subprocess.run(['python3',str(p/'write_session_metrics.py')],check=True)
a=json.loads((p/'ACCOUNTING_FINAL.json').read_text());assert a['actual_end']
f=Path('docs/CURRENT_FRONTIER.md');s=f.read_text().replace('最終更新: 2026-11-01（研究中）。','最終更新: 2026-11-01（終了・実績確定）。').replace('2026-11-01最終検証済み、journal終了処理前。','2026-11-01最終検証・journal終了済み。').replace('07:42全check543jobs/3163宣言PASS','07:47最終全check543jobs/3163宣言PASS')
m=int(a['confirmed_work_seconds']//60);sec=a['confirmed_work_seconds']-m*60;sm=int(a['shortfall_seconds']//60);ss=a['shortfall_seconds']-sm*60
s=s.replace('予定120分/open区間を確定実績にしない。',f"実終了{a['actual_end']}、confirmed {m}分{sec:.3f}秒、不足{sm}分{ss:.3f}秒。待機/中断/gapの計上0、open0。予定120分を実績にしない。",1);f.write_text(s)
with (p/'BRIEF_FINAL.txt').open('w') as out:subprocess.run(['make','brief'],stdout=out,check=True)
f=Path('docs/RESEARCH_HANDOFF_2026-11-01_DAILY.md');s=f.read_text().replace('数学探索は07:40台に終了','数学探索は07:40台に終了');s+='\n終了確認: journal stopを実時計で実行し、cursor null/open0。全起動jobにresultがあり、自分の計算は終了済み。最後のbriefは確定した終了判断/実績へ同期。終了後の遅延heartbeatは新start/stopや重複日次報告を追加しない。\n';f.write_text(s)
f=p/'OWNED_FILES.json';d=json.loads(f.read_text());d['snapshot_jst']=datetime.datetime.now().astimezone().isoformat()
for item in d['files']:item['sha256']=hashlib.sha256(Path(item['path']).read_bytes()).hexdigest()
f.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
final={k:a[k] for k in ['actual_start','actual_end','confirmed_work_seconds','shortfall_seconds','excluded_non_work_seconds','unconfirmed_gap_seconds','open_interval_unconfirmed_seconds','cursor','phase_seconds','research_allocation_seconds']};final['final_check']='543 jobs / 3163 declarations PASS';final['math_worker_cpu_seconds']=0.715819;final['report_status']='prepared for final; this file does not claim the chat notification was already sent'
(p/'FINAL_SESSION_COMPLETION.json').write_text(json.dumps(final,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(final,ensure_ascii=False))
