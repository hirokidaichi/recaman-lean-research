"""Prepare final text from a stopped journal; never mark delivery from a draft."""
from pathlib import Path
from datetime import datetime
import json,csv
P=Path(__file__).resolve().parent;root=P.parents[2]
s=json.loads((P/'final-time-summary.json').read_text());j=json.loads((root/'docs/data/daily_research/2026-10-27.json').read_text());assert j['cursor'] is None
r={x[0]:x for x in csv.reader((root/'docs/EVIDENCE_REGISTRY.tsv').open(),delimiter='\t') if x and x[0].startswith('E-')}
assert all(r[x][1]=='PROVED-LEAN' for x in ['E-416','E-423','E-429','E-431']) and r['E-432'][1]=='PROVED-PAPER'
def fmt(v):
 v=round(v);return f'{v//60}分{v%60:02d}秒'
a=datetime.fromisoformat(s['start']).strftime('%H:%M:%S');b=datetime.fromisoformat(s['end']).strftime('%H:%M:%S')
text=f'''10/27は **{a}〜{b} JST、確認済み{fmt(s['confirmed_work_seconds'])}** 作業しました。120分に対する不足は**{fmt(s['shortfall_seconds'])}**。開始の遅れを遡って埋めず、待機・中断・CPU時間も加算していません。終了処理が8時を4.412秒超過し、集計処理も修正しました。超過分は実績から除外しています。

**三つの加算区間に限り、反例を192符号以内の代表へ移し、供給窓の始点を第二の加算区間より前へ絞りました（PROVED-LEAN）。** 元の実free数・target供給・相対不足条件を保存する縮約です。同じ供給源の再利用にも位置とgap長の制約を証明しました。

C1に向けた反例候補の絞り込みが進みました。ただし、有限領域の反例不在、残る古い履歴などの供給源、任意の加算区間数を扱うrankとC1全体は未証明です。

r4表は新制約でも削減0件で停止。有限表のkernel検査はメモリ制限の設定が拒否され未起動でした。受理したLean成果の全体検証・公理監査は成功しています。

次回は、特定の三加算区間の族でfree数の下限を与える紙上証明（**PROVED-PAPER、未Lean・人間レビュー未**）をLeanへ移します。自動実行の引き継ぎも更新済みです。

[日次記録](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/RESEARCH_HANDOFF_2026-10-27_DAILY.md)・[実績journal](/Users/hirokidaichi/ghq/github.com/hirokidaichi/recaman-lean-research/docs/data/daily_research/2026-10-27.json)
'''
xml='<heartbeat>\n<automation_id>recam-n-6-8</automation_id>\n<decision>NOTIFY</decision>\n<message>\n'+text+'</message>\n</heartbeat>'
(P/'final-report-draft.md').write_text('<!-- Prepared from actual stopped journal; a draft does not certify chat delivery. -->\n'+text)
(P/'final-report-draft.xml').write_text(xml+'\n');print(xml)
