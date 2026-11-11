import json,re
from pathlib import Path
from datetime import datetime
packet=Path(__file__).parent
jp=Path('docs/data/daily_research/2026-11-12.json');j=json.loads(jp.read_text())
assert j['cursor'] is None,'Do not finalize an open journal'
stop=json.loads((packet/'FINAL_SESSION_STOP.json').read_text())
work=stop['confirmed_work_seconds'];short=stop['shortfall_seconds']
phases={}
for x in j['segments']:
 phases[x['phase']]=phases.get(x['phase'],0)+(datetime.fromisoformat(x['end'])-datetime.fromisoformat(x['start'])).total_seconds()
phases={k:round(v,3) for k,v in phases.items()}
ws=[x for x in j['segments'] if x['phase'] in ['setup','research','audit','handoff']]
start=ws[0]['start'];end=ws[-1]['end']
def duration(s):
 m=int(s//60);return f'{m}分{s-m*60:06.3f}秒'
record={'date':j['date'],'actual_start_jst':start,'actual_end_jst':end,'confirmed_work_seconds':work,'shortfall_seconds':short,'excluded_waiting_seconds':phases.get('waiting',0),'unconfirmed_gap_seconds':stop['unconfirmed_gap_seconds'],'phase_seconds':phases,'publication_after_stop_excluded':True,'journal':'docs/data/daily_research/2026-11-12.json'}
(packet/'FINAL_JOURNAL_SUMMARY.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
section=f"""## 確定実績

実開始 **{start[11:26]} JST**、終了 **{end[11:26]} JST**。confirmed_work_seconds=**{work:.3f}**、**{duration(work)}**。120分に対する不足 **{duration(short)}**。waiting **{phases.get('waiting',0):.3f}秒**を除外、未確認gap **{stop['unconfirmed_gap_seconds']:.3f}秒**。journalは担当が確認した区間であり、純CPU/純思考時間ではない。stop後のcommit/push/remote照合を遡及加算しない。

元計画setup600/研究・監査6000/handoff600秒。実phase秒数は **{json.dumps(phases,ensure_ascii=False)}**。setup短縮分を研究・監査へ再配分し、監査超過は活用枠から差引いた。活用/局所のunit判断は当日カードが正本で、別の独立計時はしていない。不足は実setup開始の8.835秒遅れと、08:00以前のstop後に最終確定値の保存・hook付きcommit・通常pushを完了するための余裕を残したことによる。未確認区間や将来予定の補填はない。

[journal](data/daily_research/2026-11-12.json)、[確定phase集計](data/depth_six_20261112/FINAL_JOURNAL_SUMMARY.json)。session 0bb9180f-09a1-4aa9-a2fc-0a9a29010939。waiting開始05:59:00.555174、実setup開始06:00:08.835479。06:07のcut二像/old-head5排除で最初15分gate通過し、j6→old-j5→old-j4→local free1→時計4の順で継続。07:39:20から最終意味監査、最終handoffの切替時刻はjournal正本。

"""
p=Path('docs/RESEARCH_HANDOFF_2026-11-12_DAILY.md');s=p.read_text();s=re.sub(r'## 実績 \(確定journal stop後に置換\).*?(?=## 今日わかったこと)',section,s,flags=re.S);assert '確定journal stop後に置換' not in s;p.write_text(s)
p=Path('docs/HYPOTHESIS_CARD_2026-11-12_DEPTH_SIX_SOURCE_AREA.md');s=p.read_text().replace('final audit in progress','final audit passed C05/G08R')
s+='\n## Final confirmed journal\n\n'+json.dumps(record,ensure_ascii=False,indent=2)+'\nC05 full check1007jobs/3907axioms、現29sourceの個別M512 receiptと33署名照合を確認。E701のみPAPER。全停止/採用外を保持しjournal stop後の公開は研究実績に加算しない。\n';p.write_text(s)
print(json.dumps(record,ensure_ascii=False))
