"""Close the live journal, then reflect its confirmed values. No research execution."""
from pathlib import Path
import subprocess,json,datetime,re,collections,math,hashlib
root=Path(__file__).resolve().parents[3]
packet=Path(__file__).resolve().parent
session='94063213-c369-4df2-8ce1-85cc11351419'
cmd=['python3','scripts/research_session.py','stop','--session',session,'--note','新数学07:40終了、最終Lean/registry/G5/briefと保存・次日automation readback確認、全自起動計算終了。08:00前に当日runを閉じる。']
r=subprocess.run(cmd,cwd=root,text=True,capture_output=True)
print(r.stdout);print(r.stderr)
if r.returncode:raise SystemExit(r.returncode)
status=json.loads(r.stdout)
jpath=root/'docs/data/daily_research/2026-10-30.json';j=json.loads(jpath.read_text())
assert j['cursor'] is None
cats=collections.defaultdict(float);units=collections.defaultdict(float);work=[]
for x in j['segments']:
 d=(datetime.datetime.fromisoformat(x['end'])-datetime.datetime.fromisoformat(x['start'])).total_seconds()
 units[x['unit']]+=d;c=x['phase']
 if c=='research':
  m=re.search(r'/H(\d+)',x['unit']);c='exploitation' if m and int(m[1])<=13 else 'exploration'
 cats[c]+=d
 if x['phase'] in ['setup','research','audit','handoff']:work.append(x)
confirmed=round(sum(cats[x] for x in ['setup','exploitation','exploration','audit','handoff']),3)
assert abs(confirmed-status['confirmed_work_seconds'])<.002
facts={'date':j['date'],'session':session,'actual_start':work[0]['start'],'actual_end':work[-1]['end'],'confirmed_work_seconds':confirmed,'target_seconds':7200,'shortfall_seconds':round(7200-confirmed,3),'excluded_waiting_seconds':round(cats['waiting'],3),'unconfirmed_gaps':j['unconfirmed_gaps'],'category_seconds':{k:round(v,3) for k,v in cats.items()},'unit_seconds':{k:round(v,3) for k,v in units.items()},'planned_minutes':{'setup':10,'exploitation':60,'exploration':30,'audit':10,'handoff':10},'journal':'docs/data/daily_research/2026-10-30.json','measurement':'journal-confirmed wall intervals, not pure CPU/thinking time; parent/child costs are the same time'}
(packet/'UNIT_COSTS_FINAL.json').write_text(json.dumps(facts,ensure_ascii=False,indent=2)+'\n')
(packet/'REPORT_FACTS.json').write_text(json.dumps(facts,ensure_ascii=False,indent=2)+'\n')
fmt=lambda s:f'{int(s//60)}分{s%60:06.3f}秒'
dpath=root/'docs/RESEARCH_HANDOFF_2026-10-30_DAILY.md';s=dpath.read_text();a=s.index('<!-- JOURNAL-SUMMARY-BEGIN -->');b=s.index('<!-- JOURNAL-SUMMARY-END -->')
summary=f'''<!-- JOURNAL-SUMMARY-BEGIN -->
**確定**: {facts['actual_start']}〜{facts['actual_end']}、confirmed_work_seconds **{confirmed:.3f}秒（{fmt(confirmed)}）**。120分への不足 **{facts['shortfall_seconds']:.3f}秒**。waiting **{facts['excluded_waiting_seconds']:.3f}秒**を除外、unconfirmed gapなし、cursorはstopで閉鎖。予定やopen区間の先取り計上なし。journal-confirmed区間でありpure CPU/思考時間の計測ではない。

| 区分 | 予定分 | 実績 |
|---|---:|---:|
| setup | 10 | {fmt(cats['setup'])} |
| C1活用 H01〜H13 | 60 | {fmt(cats['exploitation'])} |
| 局所探索 H14〜H24 | 30 | {fmt(cats['exploration'])} |
| 別pass監査 | 10 | {fmt(cats['audit'])} |
| handoff/記録 | 10 | {fmt(cats['handoff'])} |

監査・記録の超過を含めた実配分で、setup短縮と研究枠から差し引いた。実開始の06:00からの遅れと08:00前の終了余裕が不足に残り、遡及補填なし。親cycleとunitを加算していない。詳細は[UNIT_COSTS_FINAL](data/four_run_20261030/UNIT_COSTS_FINAL.json)。
'''
s=s[:a]+summary+s[b:];s=s.replace('## 実時計と親cycle（stop後の確定値を正本にする）','## 実時計と親cycle（stop済み確定値）');dpath.write_text(s)
card=root/'docs/HYPOTHESIS_CARD_2026-10-30_FOUR_RUN_OLD_TARGET.md';cs=card.read_text().replace('10/30 cycle終了へ保存中。','10/30 cycle終了、journal stop済み。');cs+=f"\n実績確定: {confirmed:.3f}秒、{fmt(confirmed)}、不足{facts['shortfall_seconds']:.3f}秒。waiting23.281秒除外/gapなし。各unit費用は同日DAILY/journal参照。\n";card.write_text(cs)
manifest=json.loads((packet/'SOURCE_MANIFEST_FINAL.json').read_text());assert all(hashlib.sha256((root/f).read_bytes()).hexdigest()==h for f,h in manifest['all_source_sha256'].items())
(packet/'BRIEF_FINAL.txt').write_text(subprocess.check_output(['make','brief'],cwd=root,text=True))
(packet/'GIT_STATUS_END.txt').write_text(subprocess.check_output(['git','status','--short'],cwd=root,text=True))
work_floor=int(confirmed);wm,ws=divmod(work_floor,60);short=math.ceil(facts['shortfall_seconds'])
start_text=datetime.datetime.fromisoformat(facts['actual_start']).strftime('%H:%M:%S')
end_text=datetime.datetime.fromisoformat(facts['actual_end']).strftime('%H:%M:%S')
report=f"""10/30は{start_text}〜{end_text}、**{wm}分{ws}秒**作業しました（監査・記録込み）。120分まで{short}秒不足。待機23秒は除外し、中断はありません。

固定前半 `S⁵A³S⁴A⁴SA³` に任意長のS/Aを続ける四A-run族で、元pのzero・正不足、同じold target・最終S源という条件下のfree-gapをLeanで証明しました（PROVED-LEAN）。**一般の四run・C1は未解決**です。

前半だけで賄う案などは反証して棄却。幅のp版の追加形式化は512MB上限で停止しました。次回は紙上の二場合（PROVED-PAPER・未Lean）を実履歴へ接続し、最後の未供給Aを1個／2個確保する問いから再開します。全checkはPASS、再開指示も更新済みです。

[日次記録](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/RESEARCH_HANDOFF_2026-10-30_DAILY.md) · [実績journal](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/daily_research/2026-10-30.json)
"""
(packet/'REPORT_DRAFT.md').write_text(report)
print(json.dumps({k:v for k,v in facts.items() if k not in ['unit_seconds','planned_minutes']},ensure_ascii=False,indent=2))
