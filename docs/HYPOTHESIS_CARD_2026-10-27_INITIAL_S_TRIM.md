# Hypothesis card: 長い初期Sを同じhistoryで正準化する

- ID: H-20261027-07
- Status: PROVED-LEAN（E-421）
- Parent: R-20261027-01/E418/E420。Mode: 活用（有限contextの数学的供給）、最初15分gate、CPU探索0。

任意padded BlockWord全実prefix後のS^h x、全A予算ones x<=B、B>=2、h>=C=2B-1とする。
実future符号を変えず、初期SだけをC個へ短縮したg(i)=if i<C then S else f(n+h+i-C)を構成する。
全x prefixで元EndN0とgのEndN0を同値にし、future/全tailの実free countを保存、gの全positive不足を供給できるか。xのS/語長上限は置かない。
E416反例ではB20からC39。元のh>=39を排除するとは主張せず、空BlockWordとh39を持つ同値代表へ移す。

紙上chain: E418 u空で古いBlockWordを消す。余分な初期SはlocalSupply_erase_prefixで消せる（残すC>=B>=ones xだから残tail mass<=0）。S^h=S^(h-C) S^C、全prefixに同じcapを適用。gのclock shift/signとsegを明示し、元freeを同値で接着。C>=B+1からpositive_after_manyS。

反証: endpoint S、x空、h=C/B2、Sを任意長含むx、初期S中free0。基点のsilent再定義なし。無予算のE405を再開せずA予算を残す。
受入は全長同値/count保存/actual counterexample移送をLean/G5/Audit/check。新しいg関数の定義だけを成果としない。
15分で元free保存に届かなければSTOPPED、次はold開始点のA-budget依存半径へ。修理1回まで。

06:45:50全体check420jobs/2885宣言成功、G5/Audit/lint確認。数学修理0。元h>=39を排除せず、実counterexample/free/positiveを持つh39空old代表へ移す。次はH08のA-budget old半径へ。

## 当日journal確定実績
親cycle R-20261027-01: 06:01:46.075185〜08:00:04.411787、確認済み118分13.925秒、不足1分46.075秒。
このcardの明示unit実績はH-20261027-07/exploit/initial-S-canonical-history: 4分03.209秒、H-20261027-07/audit/canonical-initial-S: 4分47.796秒。
同じcycleの内訳で別cycle/CPUを追加加算しない。[当日DAILY](RESEARCH_HANDOFF_2026-10-27_DAILY.md)/[journal](data/daily_research/2026-10-27.json)に予定と実績・再配分・失敗・次判断を保存。
