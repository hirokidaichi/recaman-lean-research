"""Save only confirmed final journal values after an actual stop."""
from pathlib import Path
import collections
import datetime
import json
import re
import subprocess

packet=Path(__file__).parent
status=json.loads(subprocess.check_output(['python3','scripts/research_session.py','status'],text=True))
journal=json.loads(Path(status['journal']).read_text())
assert status['cursor'] is None,status['cursor']
assert status['open_interval_unconfirmed_seconds']==0
phase=collections.defaultdict(float)
local_units={3,9,10,11,12,14,16,18,26,27,28,29,30}
research=collections.defaultdict(float)
for segment in journal['segments']:
    seconds=(datetime.datetime.fromisoformat(segment['end'])-datetime.datetime.fromisoformat(segment['start'])).total_seconds()
    phase[segment['phase']]+=seconds
    if segment['phase']=='research':
        number=int(re.search(r'H-20261111-(\d+)',segment['unit']).group(1))
        research['local_exploration' if number in local_units else 'exploitation']+=seconds
start=next(event['at'] for event in journal['events'] if event['action']=='start')
stop=[event['at'] for event in journal['events'] if event['action']=='stop'][-1]
def duration(seconds):
    return f'{int(seconds//60)}分{seconds%60:06.3f}秒'
confirmed=status['confirmed_work_seconds']
text=f"""実開始 **{start}**、実終了 **{stop}**。confirmed_work_seconds={confirmed:.3f}、確認済み **{duration(confirmed)}**。120分に対する不足 **{duration(status['shortfall_seconds'])}**。待機除外 {status['excluded_non_work_seconds'].get('waiting',0):.3f}秒、blocked除外 {status['excluded_non_work_seconds'].get('blocked',0):.3f}秒、未確認gap {status['unconfirmed_gap_seconds']:.3f}秒、open 0秒、overtime {status['overtime_work_seconds']:.3f}秒。

phase実績はsetup {duration(phase['setup'])}、研究 {duration(phase['research'])}、監査 {duration(phase['audit'])}、handoff {duration(phase['handoff'])}。研究の内容別整理は活用 {duration(research['exploitation'])}、局所探索 {duration(research['local_exploration'])}。局所探索unitは3/9/10/11/12/14/16/18/26/27/28/29/30、他の研究unitを活用と分類し、全研究区間を一度ずつ数えた。

予定の活用60/局所30/監査10から、独立の高さ・面積・全高機構へ研究時間を再配分した。監査予定600秒に対し実績{phase['audit']:.3f}秒、超過{max(0,phase['audit']-600):.3f}秒は、全型52署名・30moduleの現bytes・frozen hash・停止隔離の追加照合に使い、研究へ回せる時間から差し引いた。setup短縮分は研究と必要監査へ再配分し、必要確認は実測だけで計上。開始遅れとstop後のcommit/push・remote/CI確認を足さず、終了期限を延長しない。"""
p=Path('docs/RESEARCH_HANDOFF_2026-11-11_DAILY.md')
s=p.read_text()
s=re.sub(r'<!-- JOURNAL_FINAL_BEGIN -->.*?<!-- JOURNAL_FINAL_END -->',
         '<!-- JOURNAL_FINAL_BEGIN -->\n'+text+'\n<!-- JOURNAL_FINAL_END -->',s,flags=re.S)
p.write_text(s)
p=Path('docs/HYPOTHESIS_CARD_2026-11-11_SHORT_RECORD_OVERLAP.md')
p.write_text(p.read_text()+f'\n確定journal {start}〜{stop}、confirmed_work_seconds={confirmed:.3f}、{duration(confirmed)}、不足{duration(status["shortfall_seconds"])}。待機・中断・gapは確定DAILY/journalに従う。\n')
summary={'status':status,'actual_start':start,'actual_stop':stop,'phase_seconds':dict(phase),'research_content_seconds':dict(research),'allocation_note':'Content classification by actual closed units. No unit or CPU is added twice.'}
(packet/'JOURNAL_FINAL_STATUS.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False))
