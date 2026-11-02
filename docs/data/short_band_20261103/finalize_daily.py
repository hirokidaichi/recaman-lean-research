"""Close only this owned session at the real clock, then write final accounting."""
from pathlib import Path
from datetime import datetime
import json,subprocess,collections
packet=Path('docs/data/short_band_20261103')
result=json.loads(subprocess.check_output(['python3','scripts/research_session.py','stop','--session','f9152e9d-af2b-440c-897b-4f2da8c07e4d','--note','本日の研究・検証を終了し、自分のLean/Lake processは完了。08:00期限前の確定実績保存・最終metadata commit/push用余裕を残してjournalを閉じる。C1全体とR6候補不在は未証明。'],text=True))
assert result['cursor'] is None and result['overtime_work_seconds']==0
j=json.loads(Path('docs/data/daily_research/2026-11-03.json').read_text())
by=collections.defaultdict(float);units=collections.defaultdict(float);allocation=collections.defaultdict(float)
local={'03','06','08','11','14'}
for x in j['segments']:
 sec=(datetime.fromisoformat(x['end'])-datetime.fromisoformat(x['start'])).total_seconds()
 by[x['phase']]+=sec;units[x['unit']]+=sec
 if x['phase']=='research':
  n=x['unit'].split('H-20261103-')[-1][:2] if 'H-20261103-' in x['unit'] else '?'
  allocation['local_exploration' if n in local else 'exploitation']+=sec
actual_start=next(x['start'] for x in j['segments'] if x['phase']=='setup')
actual_end=j['events'][-1]['at']
def fs(x):return f'{int(x//60)}分{x%60:06.3f}秒'
work=result['confirmed_work_seconds'];short=result['shortfall_seconds']
account={'journal':'docs/data/daily_research/2026-11-03.json','session':'f9152e9d-af2b-440c-897b-4f2da8c07e4d','cycle':'R-20261103-01','actual_start':actual_start,'actual_end':actual_end,**result,'phase_seconds':dict(by),'research_phase_allocation_seconds':dict(allocation),'unit_seconds':dict(units),'planned_seconds':{'setup':600,'exploitation':3600,'local_exploration':1800,'audit':600,'handoff':600},'reallocation_reason':'setup compressed to actual127.023s; audit/signature/source/validation/publication costs consumed research allocation. H13 cap stop switched to independent target grammar and R5 long-first. No double counting or future credit.','measurement_scope':'confirmed wall intervals, not pure thought or CPU; post-stop publication is excluded','mathematical_worker_cpu_seconds':0}
(packet/'WORK_ACCOUNTING_FINAL.json').write_text(json.dumps(account,ensure_ascii=False,indent=2)+'\n')
p=Path('docs/RESEARCH_HANDOFF_2026-11-03_DAILY.md');s=p.read_text();a=s.index('## 実時計と確定前の保存状態');b=s.index('## 証拠・検証',a)
section=f'''## 実時計と確定実績

実開始 {actual_start}、実終了 {actual_end}（Asia/Tokyo、journal stop）。confirmed_work_seconds={work:.3f}秒＝{fs(work)}、120分に対する不足{fs(short)}。waiting64.987秒を除外、中断/gap0、overtime0、cursor閉鎖済み。開いた区間や予定を計上せず、stop後の最終publicationも実績へ戻さない。不足理由は06:00直後のsetup切替差と08:00前の確定記録/commit/push余裕、遡及補填なし。

[確定集計](data/short_band_20261103/WORK_ACCOUNTING_FINAL.json)と[journal](data/daily_research/2026-11-03.json)が正本。phase実績はsetup {fs(by['setup'])}、research {fs(by['research'])}、audit {fs(by['audit'])}、handoff {fs(by['handoff'])}。research内の活用{fs(allocation['exploitation'])}、局所探索{fs(allocation['local_exploration'])}。これはjournalに記録した作業区間で純思考/純CPU時間ではない。

旧予定setup10/活用60/局所30/別pass監査10/handoff10分に対し、setupを実127.023秒へ縮め、その余裕を含めて監査・保存へ再配分。G5逐語意味監査・source全量化・resource失敗対応とpublicationの実費を研究枠から差引き、活用/局所の予定90分を実行済みとは呼ばない。H13 cap STOP後も独立target grammarとR5 edgeへ継続。前日時間/CPU持越なし。全体無変化counter0は当日新edgeによる更新で日付resetではない。

'''
s=s[:a]+section+s[b:]
s+='''\n最終保存: journal stopの確定値を含むmetadata commitを、この研究snapshot8e3e14dの後続として通常origin/mainへpushする。最終metadata SHAとls-remote一致はこのチャットの終了報告で示す（commit自身のSHAを自身の内容へ埋め込まない）。全研究成果/停止記録は保存対象、未公開研究sourceなし。hosted Lean CIは最終readbackでdeep trace certificates build中、全成功未確認。終了後にCI成功を推定しない。\n
G5最終監査では14本の元p shift adapterの質問3を明示yes（wrapper、独立成果ではない）に修正し、具体source/core定理と区別した。逐語signature/Lean statementは不変、registry G1-G5再PASS。\n'''
p.write_text(s)
p=Path('docs/CURRENT_FRONTIER.md');s=p.read_text().replace('journalは保存作業中、確定時間は当日DAILY/journalを正本とする。',f'journal stop済み、confirmed {fs(work)}、不足{fs(short)}。確定値は当日DAILY/journalを正本とする。');p.write_text(s)
p=Path('docs/DAILY_RESEARCH_SCHEDULE.md');s=p.read_text()+f'\n2026-11-03確定: 実開始{actual_start}〜終了{actual_end}、confirmed {work:.3f}秒（{fs(work)}）、不足{fs(short)}、waiting64.987秒/gap0は除外。E535/R6未解決、H13 cap STOP、main研究snapshot8e3e14d＋後続確定metadata、hosted CIは未完了。[DAILY](RESEARCH_HANDOFF_2026-11-03_DAILY.md)を正本とし、翌日の実績へ加えない。\n';p.write_text(s)
p=packet/'PUBLICATION.json';d=json.loads(p.read_text());d['journal_closed']=True;d['confirmed_work_seconds']=work;d['shortfall_seconds']=short;d['actual_end']=actual_end;d['final_closed_journal_metadata_commit']='contains this record; final exact SHA/remote readback reported in chat and Git ancestry';d['hosted_CI_latest_snapshot']='HOSTED_CI_FINAL.json; latest explicit readback, full success unconfirmed';p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
paths=sorted(set(subprocess.check_output(['git','diff','--name-only'],text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()+['docs/data/short_band_20261103/FINAL_METADATA_PATHS.json']))
owned=set(json.loads((packet/'OWNED_PATHS.json').read_text()))
for f in paths:
 assert f in owned or f.startswith('docs/data/short_band_20261103/'),f
 assert not any(x in f for x in ['.lock','__pycache__','.pyc']),f
(packet/'FINAL_METADATA_PATHS.json').write_text(json.dumps(paths,indent=2)+'\n')
print(json.dumps({'confirmed_work_seconds':work,'shortfall_seconds':short,'actual_start':actual_start,'actual_end':actual_end,'phase_seconds':dict(by),'metadata_paths':len(paths)},ensure_ascii=False,indent=2))
